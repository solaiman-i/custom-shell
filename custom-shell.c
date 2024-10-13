/*
 * cush - the customizable shell.
 *
 * Developed by Solaiman Ibrahimi & Ken Johnson
 * Fall 2024
 */

#define _GNU_SOURCE    1
#include <stdio.h>
#include <readline/readline.h>
#include <unistd.h>
#include <stdlib.h>
#include <string.h>
#include <termios.h>
#include <sys/wait.h>
#include <assert.h>
#include <spawn.h>
#include <time.h>
#include "list.h"
#include <signal.h>

/* Since the handed out code contains a number of unused functions. */
#pragma GCC diagnostic ignored "-Wunused-function"

#include "termstate_management.h"
#include "signal_support.h"
#include "shell-ast.h"
#include "utils.h"
#include <errno.h>
#include <readline/history.h>
#include <fcntl.h>

int posix_spawnattr_tcsetpgrp_np(posix_spawnattr_t *__attr, int fd);
struct termios saved_term;
static void handle_child_status(pid_t pid, int status);
void run_command(struct ast_command_line *cmdline);
void fg_builtin(struct ast_command* cmd);
void jobs_builtin(void);
void stop_builtin(struct ast_command* cmd);
void kill_builtin(struct ast_command* cmd);
void exit_builtin(void);
void bg_builtin(struct ast_command* cmd);
void cd_custom_builtin(struct ast_command* cmd);
void history_custom_builtin(void);

static void
usage(char *progname)
{
    printf("Usage: %s -h\n"
        " -h            print this help\n",
        progname);

    exit(EXIT_SUCCESS);
}

/* Build a prompt */
static char *
build_prompt(void)
{
    return strdup("cush> ");
}

enum job_status {
    FOREGROUND,     /* job is running in foreground.  Only one job can be
                       in the foreground state. */
    BACKGROUND,     /* job is running in background */
    STOPPED,        /* job is stopped via SIGSTOP */
    NEEDSTERMINAL,  /* job is stopped because it was a background job
                       and requires exclusive terminal access */
};

struct job {
    struct list_elem elem;   /* Link element for jobs list. */
    struct ast_pipeline *pipe;  /* The pipeline of commands this job represents */
    int     jid;             /* Job id. */
    enum job_status status;  /* Job status. */ 
    int  num_processes_alive;   /* The number of processes that we know to be alive */
    struct termios saved_tty_state;  /* The state of the terminal when this job was 
                                        stopped after having been in foreground */
    /* Add additional fields here if needed. */
    bool termStateIsSaved;          //boolean representing
    int pgid;                       // process group id
    pid_t *pids;                    //list of process ids for each job
};

/* Utility functions for job list management.
 * We use 2 data structures: 
 * (a) an array jid2job to quickly find a job based on its id
 * (b) a linked list to support iteration
 */
#define MAXJOBS (1<<16)
static struct list job_list; 
static struct job * jid2job[MAXJOBS];

/* Return job corresponding to jid */
static struct job * 
get_job_from_jid(int jid)
{
    if (jid > 0 && jid < MAXJOBS && jid2job[jid] != NULL)
        return jid2job[jid];

    return NULL;
}

/* Add a new job to the job list */
static struct job *
add_job(struct ast_pipeline *pipe)
{
    struct job * job = malloc(sizeof *job);
    job->pipe = pipe;
    job->num_processes_alive = 0;
    job->termStateIsSaved = false;
    list_push_back(&job_list, &job->elem);
    for (int i = 1; i < MAXJOBS; i++) {
        if (jid2job[i] == NULL) {
            jid2job[i] = job;
            job->jid = i;
            return job;
        }
    }
    fprintf(stderr, "Maximum number of jobs exceeded\n");
    abort();
    return NULL;
}

/* Delete a job.
 * This should be called only when all processes that were
 * forked for this job are known to have terminated.
 */
static void
delete_job(struct job *job)
{
    int jid = job->jid;
    assert(jid != -1);
    jid2job[jid]->jid = -1;
    jid2job[jid] = NULL;
    ast_pipeline_free(job->pipe);
    free(job->pids);
    free(job);
}

static const char *
get_status(enum job_status status)
{
    switch (status) {
    case FOREGROUND:
        return "Foreground";
    case BACKGROUND:
        return "Running";
    case STOPPED:
        return "Stopped";
    case NEEDSTERMINAL:
        return "Stopped (tty)";
    default:
        return "Unknown";
    }
}

/* Print the command line that belongs to one job. */
static void
print_cmdline(struct ast_pipeline *pipeline)
{
    struct list_elem * e = list_begin (&pipeline->commands); 
    for (; e != list_end (&pipeline->commands); e = list_next(e)) {
        struct ast_command *cmd = list_entry(e, struct ast_command, elem);
        if (e != list_begin(&pipeline->commands))
            printf("| ");
        char **p = cmd->argv;
        printf("%s", *p++);
        while (*p)
            printf(" %s", *p++);
    }
}

/* Print a job */
static void
print_job(struct job *job)
{
    printf("[%d]\t%s\t\t(", job->jid, get_status(job->status));
    print_cmdline(job->pipe);
    printf(")\n");
}

// helper method used to print the status of a background job
static void
print_bg(struct job *job)
{
    printf("[%d] %d\n", job->jid, job->pgid);
}


// SIGCHLD handler.
static void
sigchld_handler(int sig, siginfo_t *info, void *_ctxt)
{
    pid_t child;
    int status;

    assert(sig == SIGCHLD);

    while ((child = waitpid(-1, &status, WUNTRACED|WNOHANG)) > 0) {
        handle_child_status(child, status);
    }
}

static void
wait_for_job(struct job *job)
{
    assert(signal_is_blocked(SIGCHLD));

    while (job->status == FOREGROUND && job->num_processes_alive > 0) {
        int status;

        pid_t child = waitpid(-1, &status, WUNTRACED);

        // When called here, any error returned by waitpid indicates a logic
        // bug in the shell.
        // In particular, ECHILD "No child process" means that there has
        // already been a successful waitpid() call that reaped the child, so
        // there's likely a bug in handle_child_status where it failed to update
        // the "job" status and/or num_processes_alive fields in the required
        // fashion.
        // Since SIGCHLD is blocked, there cannot be races where a child's exit
        // was handled via the SIGCHLD signal handler.
        if (child != -1)
            {
                handle_child_status(child, status);
            }
        else
            utils_fatal_error("waitpid failed, see code for explanation");
    }
    termstate_give_terminal_back_to_shell();
    signal_unblock(SIGCHLD);
}



static void
handle_child_status(pid_t pid, int status)
{
    //returns error if list is empty
    if (list_empty(&job_list)) {
        fprintf(stderr, "job list is empty\n");
        return;
    }
    //finds the job
    for (struct list_elem *e = list_begin(&job_list);
       e != list_end(&job_list); e = list_next(e)) {
        struct job *job = list_entry(e, struct job, elem);
        if (!job) {
                fprintf(stderr, "this pid is not associated with a job: %d\n", pid);
                return;
        }
        //finds the process associated with the given pid
        for(int i=0; i<sizeof(job->pids); i++){    
            if (job->pids[i] == pid) {   
                // determine status 
                if (WIFEXITED(status)) { 
                    if (job->status == FOREGROUND) {
                        termstate_sample();
                        termstate_give_terminal_back_to_shell();
                    }
                    job->num_processes_alive--; 
                } 
                else if (WIFSIGNALED(status)) {
                    job->num_processes_alive--;

                    int sig = WTERMSIG(status);
                    if (sig == SIGFPE) { // sigfpe : 'floating-pt-error'
                        fprintf(stderr, "Floating point exception\n");
                    } else if (sig == SIGSEGV) { // sigsegv : 'seg-fault'
                        fprintf(stderr, "Segmentation fault\n");
                    } else if (sig == SIGABRT) { // sigabrt : 'abort proc signal'
                        fprintf(stderr, "Aborted\n");
                    } else if (sig == SIGKILL) { // sigkill : 'kill signal'
                        fprintf(stderr, "Killed\n");
                    } else if (sig == SIGTERM) { // sigterm : 'termination signal'
                        fprintf(stderr, "Terminated\n");
                    }
                }
                else if (WIFSTOPPED(status)) { // signal stopped a process
                    if (job->status == FOREGROUND) { // if process was fg -> stopped, save terminal state
                        tcgetattr(0, &job->saved_tty_state);
                        job->termStateIsSaved = true;
                    }
                    job->status = STOPPED;
                    if (WSTOPSIG(status) == SIGTSTP) {
                        print_job(job);
                    }
                    termstate_save(&saved_term);
                    termstate_give_terminal_back_to_shell();

                } 
                else if (WIFCONTINUED(status)) { // process continues
                    if (job->status == STOPPED || job->status == NEEDSTERMINAL) {
                        job->status = BACKGROUND; // continue as bg job
                    }
                }
            }
        }
    }
}

//brings a background process to the foreground
void fg_builtin(struct ast_command* cmd) {
    if (!cmd->argv[1]) {
        perror("No argument given with fg");
        return;
    }
    int jobID = atoi(cmd->argv[1]);
    struct job* thisJob = get_job_from_jid(jobID);
    if (thisJob == NULL) {
        fprintf(stderr, "fg %d failed, no such job\n", jobID);
        return;
    }
    thisJob->status = FOREGROUND;
    //uses saved state if termstateIsSaved is true
    if (thisJob->termStateIsSaved) {
        termstate_give_terminal_to(&thisJob->saved_tty_state, thisJob->pgid);
        thisJob->termStateIsSaved = false;
    }
    //else sets state to null
    else {
        termstate_give_terminal_to(NULL, thisJob->pgid);
    }
    print_job(thisJob);
    if (killpg(thisJob->pgid, SIGCONT) != 0)
    {
        utils_fatal_error("kill pgid failed %d", thisJob->pgid);
        return;
    }
    wait_for_job(thisJob);
}
//brings a foreground job to the background 
void bg_builtin(struct ast_command* cmd) {
    if (cmd->argv[1] == NULL) {
        fprintf(stderr, "bg: not enough arguments\n");
        return;
    }

    int jobID = atoi(cmd->argv[1]);
    if (get_job_from_jid(jobID) == NULL) {
        fprintf(stderr, "bg %d failed, no such job\n", jobID);
        return;
    }

    struct job* job = get_job_from_jid(jobID);
    if (job->status != STOPPED) { // already running proc
        fprintf(stderr, "this job: %d is already running\n", jobID);
        return;
    }

    job->status = BACKGROUND; // safe to set to bg now
    print_job(job);
    if (killpg(job->pgid, SIGCONT) != 0) {
        utils_fatal_error("kill pgid failed %d", job->pgid);
        return;
    }
    wait_for_job(job);
}
//prints the list of jobs
void jobs_builtin(void)
{
    for (int i = 1; i < MAXJOBS; i ++) {
        struct job *job = get_job_from_jid(i);
        if (job != NULL) {
            print_job(job);
        }
    }
}
//kills a process with the given jobID
void kill_builtin(struct ast_command* cmd) {
    if (cmd->argv[1] == NULL) {
        fprintf(stderr, "kill: not enough arguments\n");
        return;
    }
    int jobID = atoi(cmd->argv[1]);
    if (get_job_from_jid(jobID) == NULL) {
        fprintf(stderr, "attempt to kill %d failed, no such process\n", jobID);
        return;
    }
    struct job* job = get_job_from_jid(jobID);
    if (job->jid == atoi(cmd->argv[1])) {
        job->status = STOPPED;
        for (int i = 0; i < job->num_processes_alive; i++) {
            killpg(job->pgid, SIGKILL);
        }
    }
}
//stops a process with the given jobID
void stop_builtin(struct ast_command* cmd) {
    if (cmd->argv[1] == NULL) {
        fprintf(stderr, "stop: not enough arguments\n");
        return;
    }
    int jobID = atoi(cmd->argv[1]);
    if (get_job_from_jid(jobID) == NULL) {
        fprintf(stderr, "attempt to stop %d failed, no such process\n", jobID);
        return;
    }

    struct job* job = get_job_from_jid(jobID);
    if (job->jid == atoi(cmd->argv[1])) {
        job->status = STOPPED;
        for (int i = 0; i < job->num_processes_alive; i++) {
            killpg(job->pgid, SIGSTOP);
        }
    }
}
//deletes all jobs then exits
void exit_builtin(void) {
    for (int i = 1; i < MAXJOBS; i ++) {
        struct job *job = get_job_from_jid(i);
        if(job != NULL){
            delete_job(job);
        }
    }
    exit(0);
}
//cd custom built in for changing directories in the shell
void cd_custom_builtin(struct ast_command* cmd) {
    char *path_from_cmd = cmd->argv[1];

    if (path_from_cmd == NULL) {
        if (getenv("HOME") == NULL) {
            fprintf(stderr, "cd: HOME env variable not set\n");
        } else if (chdir(getenv("HOME")) != 0) {
            fprintf(stderr, "cd: Changing directory to HOME failed:\n");
        }
        return;
    }

    if (chdir(path_from_cmd) != 0) {
        if (errno == EACCES) {
            fprintf(stderr, "cd: Permission denied!\n");
            return;
        }
        else if (errno == ENOTDIR) {
            fprintf(stderr, "cd: Can't change directory to a file: %s\n", path_from_cmd);
            return;
        }
        else if (errno == ENOENT) {
            fprintf(stderr, "cd: No such file or directory: %s\n", path_from_cmd);
            return;
        }
        else {
            fprintf(stderr, "cd: Could not change directory: %s\n", strerror(errno));
            return;
        }
    }
}
//history custom built in for displaying previous shell commands
void history_custom_builtin() {
    HIST_ENTRY **cmd_history;
    cmd_history = history_list();

    if (cmd_history) {
        for (int i = 0; cmd_history[i] != NULL; i++) {
            printf("[%d]: %s\n", i+1, cmd_history[i]->line);
        }
    }
}

//helper method which handles spawning, running built in commands, and piping
void run_command(struct ast_command_line *cmdline) {
    termstate_sample();
    signal_block(SIGCHLD);
    //iterates through a command line input and splits it into pipelines
    for (struct list_elem *e = list_begin(&cmdline->pipes);
         e != list_end(&cmdline->pipes); e = list_next(e)) {
        struct ast_pipeline *pipe = list_entry(e, struct ast_pipeline, elem);
        
        //adds job to job list and creates pid list for job
        struct job *job = add_job(pipe); 
        job->pids = malloc(sizeof(pid_t) * list_size(&pipe->commands));

        if (!job->pids) {
            fprintf(stderr, "memory allocation failed for job PIDs list\n");
            return; 
        }

        int idx = 0; //keeps track of how many commands have been processed in a pipeline ex. if idx = 0 first command
        pid_t gid = 0; //group id for pgid. set to 0 for first command (which makes pgid itself)

        //setup pipes
        int pipe_fd[2];
        pipe_fd[0] = -1;
        pipe_fd[1] = -1;
        int prev_fd = -1;
        //iterate through pipelines and split into commands
        for (struct list_elem *inner_e = list_begin(&pipe->commands);
             inner_e != list_end(&pipe->commands); inner_e = list_next(inner_e)) {
            struct ast_command *cmd = list_entry(inner_e, struct ast_command, elem);

            termstate_sample();
            //check for built ins
            if (strcmp(cmd->argv[0], "jobs") == 0) {
                jobs_builtin();
                signal_unblock(SIGCHLD);
                return;
            }
            else if (strcmp(cmd->argv[0], "fg") == 0) {
                fg_builtin(cmd);
                signal_unblock(SIGCHLD);
                return;
            }
            else if(strcmp(cmd->argv[0], "bg") == 0) {
                bg_builtin(cmd);
                signal_unblock(SIGCHLD);
                return;
            }
            else if (strcmp(cmd->argv[0], "kill") == 0) {
                kill_builtin(cmd);
                signal_unblock(SIGCHLD);
                return;
            }
            else if (strcmp(cmd->argv[0], "exit") == 0) {
                exit_builtin();
                signal_unblock(SIGCHLD);
                return;
            }
            else if(strcmp(cmd->argv[0], "stop") == 0) {
                stop_builtin(cmd);
                signal_unblock(SIGCHLD);
                return;
            }
            else if(strcmp(cmd->argv[0], "cd") == 0) {
                cd_custom_builtin(cmd);
                signal_unblock(SIGCHLD);
                return;
            }
            else if (strcmp(cmd->argv[0], "history") == 0) {
                history_custom_builtin();
                signal_unblock(SIGCHLD);
                return;
            }
            else if (cmd->argv[0][0] == '!') {
                HIST_ENTRY **cmd_history;
                cmd_history = history_list();
                if (cmd->argv[0][1] == '-' && isdigit(cmd->argv[0][2])) {
                    int n = atoi(&cmd->argv[0][2]);
                    int size = -1;
                    while (cmd_history[size] != NULL) {
                        size++;
                    }
                    if (size != -1) {
                        size++;
                    }
                    else {
                        fprintf(stderr, "Improper n-value for !-n cmd\n");
                        return;
                    }
                    char *holder = strtok(cmd_history[size - n - 2]->line, " ");
                    cmd->argv = malloc(sizeof(char *) * 3);
                    cmd->argv[0] = strdup(holder);
                    holder = strtok(NULL, " ");
                    cmd->argv[1] = holder ? strdup(holder) : NULL;
                    cmd->argv[2] = NULL;
                    printf("Running command from history: %s\n", cmd_history[size - n - 2]->line);
                }
                else if (isdigit(cmd->argv[0][1])) {
                    int n = atoi(&cmd->argv[0][1]);
                    HIST_ENTRY **cmd_history;
                    cmd_history = history_list();
                    int size = -1;
                    while (cmd_history[size] != NULL) {
                        size++;
                    }
                    if (size != -1) {
                        size++;
                    }
                    else {
                        fprintf(stderr, "Improper n-value for !n cmd\n");
                        return;
                    }
                    if (n >= size || n < 1) {
                        fprintf(stderr, "Improper n-value for !n cmd\n");
                        return;
                    }
                    char *holder = strtok(cmd_history[n-1]->line, " ");
                    cmd->argv = malloc(sizeof(char *) * 3);
                    cmd->argv[0] = strdup(holder);
                    holder = strtok(NULL, " ");
                    cmd->argv[1] = holder ? strdup(holder) : NULL;
                    cmd->argv[2] = NULL;
                    printf("Running command from history: %s\n", cmd_history[n - 1]->line);
                }
                else {
                    fprintf(stderr, "Invalid event designator format, accepted use-cases: {!n, !-n}\n");
                    return;
                }
            }

            // n-1 pipes created for n cmds -> cmd1 | cmd2 | ... | n
            if (list_next(inner_e) != list_end(&pipe->commands)) {
                if (pipe2(pipe_fd, O_CLOEXEC) == -1) {
                    perror("pipe2 failed");
                    signal_unblock(SIGCHLD);
                    delete_job(job);
                    return;
                }
            }

            //setting up attributes for posix spawn
            posix_spawn_file_actions_t child_file_attr;
            posix_spawnattr_t child_spawn_attr;
            pid_t pid;
            posix_spawn_file_actions_init(&child_file_attr);
            posix_spawnattr_init(&child_spawn_attr);

            // input redirection for the first command if iored_input is true
            if (pipe->iored_input && idx == 0) {
                posix_spawn_file_actions_addopen(&child_file_attr, STDIN_FILENO, pipe->iored_input, O_RDONLY, 0666);
            }

            // output redirection for the last command
            if (pipe->iored_output && list_next(inner_e) == list_end(&pipe->commands)) {
                int flags;
                if (pipe->append_to_output) {
                    flags = O_WRONLY | O_CREAT | O_APPEND;
                }
                else {
                    flags = O_WRONLY | O_CREAT | O_TRUNC;
                }
                posix_spawn_file_actions_addopen(&child_file_attr, STDOUT_FILENO, pipe->iored_output, flags, 0666);
            }

            // pipe setup
            if (prev_fd != -1) {
                posix_spawn_file_actions_adddup2(&child_file_attr, prev_fd, STDIN_FILENO);
            }
            if (list_next(inner_e) != list_end(&pipe->commands)) {
                posix_spawn_file_actions_adddup2(&child_file_attr, pipe_fd[1], STDOUT_FILENO);
            }

            // stderr redirection setup
            if (cmd->dup_stderr_to_stdout) {
                posix_spawn_file_actions_adddup2(&child_file_attr, STDOUT_FILENO, STDERR_FILENO);
            }

            // process group setup
            if (idx == 0) {
                posix_spawnattr_setpgroup(&child_spawn_attr, 0);
                //if first command in pipeline set the pgid to be 0 (the pid of the first command)
            } 
            else {
                posix_spawnattr_setpgroup(&child_spawn_attr, gid);
                //else set the pgid to be gid (which is set to be the pid of the first command later)
            }
            int flags = POSIX_SPAWN_SETPGROUP;
            //if foreground, set the spawn to take access to the terminal
            if (!pipe->bg_job) {
                flags |= POSIX_SPAWN_TCSETPGROUP;
                posix_spawnattr_tcsetpgrp_np(&child_spawn_attr, termstate_get_tty_fd());
            }
            posix_spawnattr_setflags(&child_spawn_attr, flags);

            // spawn with the set attributes
            if (posix_spawnp(&pid, cmd->argv[0], &child_file_attr, &child_spawn_attr, cmd->argv, environ) != 0) {
                perror("posix_spawnp failed");
                signal_unblock(SIGCHLD);
                delete_job(job);
                termstate_give_terminal_back_to_shell();
                return;
            }
            // if first command in pipeline, store the pid for the next commands pgid
            if (idx == 0) {
                gid = pid;
                job->pgid = pid;
            }
            //store the pid in pids array and increment the number of processes
            job->pids[idx++] = pid;
            job->num_processes_alive++;

            // close pipe ends
            if (prev_fd!= -1) {
                close(prev_fd);
            }
            if (list_next(inner_e) != list_end(&pipe->commands)) {
                close(pipe_fd[1]);
                prev_fd = pipe_fd[0];
            } else if (prev_fd != -1) {
                close(prev_fd);
            }
        
            // designate job status and print if background
            if (pipe->bg_job) {
                job->status = BACKGROUND;
                print_bg(job);
            } else {
                job->status = FOREGROUND;
            }

        }
    signal_block(SIGCHLD);
    wait_for_job(job);
    }
    signal_unblock(SIGCHLD);
    termstate_give_terminal_back_to_shell();
}



int
main(int ac, char *av[])
{
    int opt;

    /* Process command-line arguments. See getopt(3) */
    while ((opt = getopt(ac, av, "h")) > 0) {
        switch (opt) {
        case 'h':
            usage(av[0]);
            break;
        }
    }

    using_history(); // for our history implementation *to initialize history*

    list_init(&job_list);
    signal_set_handler(SIGCHLD, sigchld_handler);
    termstate_init();

    for (;;) {
        signal_unblock(SIGCHLD);
        assert(!signal_is_blocked(SIGCHLD));
        assert(termstate_get_current_terminal_owner() == getpgrp());

        char * prompt = isatty(0) ? build_prompt() : NULL;
        char * cmdline = readline(prompt);
        free (prompt);

        if (cmdline == NULL)  /* User typed EOF */
            break;
        
        add_history(cmdline); // to add to history of cmds

        struct ast_command_line * cline = ast_parse_command_line(cmdline);
        free (cmdline);

        if (cline == NULL)                  /* Error in command line */
            continue;

        if (list_empty(&cline->pipes)) {    /* User hit enter */
            ast_command_line_free(cline);
            continue;
        }

        //ast_command_line_print(cline);      /* Output a representation of the entered command line */
        run_command(cline);
        //loop through all the jobs and see if any can be deleted/freed
        for (int i = 1; i < MAXJOBS; i ++)
                {
                    struct job *job = get_job_from_jid(i);
                    
                    if (job != NULL && job-> num_processes_alive == 0)
                    {
                        list_remove(&job->elem);
                        delete_job(job);
                    }
                }
    }
    return 0;
}
