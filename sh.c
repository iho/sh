// sh.c Synrc Bourne Shell

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <errno.h>
#include <limits.h>
#include <ctype.h>

#define SH_MAX_INPUT 1024
#define MAX_ARGS 64
#define MAX_TOKENS 256
#define MAX_VARS 128
#define MAX_FUNCS 32

typedef enum {
    TOK_WORD, TOK_ASSIGNMENT, TOK_NEWLINE, TOK_IO_NUMBER,
    TOK_AND_IF, TOK_OR_IF, TOK_DSEMI,
    TOK_DLESS, TOK_DGREAT, TOK_LESSAND, TOK_GREATAND, TOK_LESSGREAT, TOK_DLESSDASH,
    TOK_CLOBBER, TOK_LESS, TOK_GREAT,
    TOK_IF, TOK_THEN, TOK_ELSE, TOK_ELIF, TOK_FI,
    TOK_DO, TOK_DONE, TOK_CASE, TOK_ESAC, TOK_WHILE,
    TOK_UNTIL, TOK_FOR, TOK_IN,
    TOK_LBRACE, TOK_RBRACE, TOK_BANG, TOK_LPAREN, TOK_RPAREN,
    TOK_SEMI, TOK_PIPE, TOK_AMP, TOK_EOF
} TokenType;

typedef struct {
    TokenType type;
    char *value;
} Token;

typedef struct {
    char *name;
    char *body;
} Function;

struct { char *name; char *value; } vars[MAX_VARS];
Function funcs[MAX_FUNCS];
int var_count = 0;
int func_count = 0;
Token tokens[MAX_TOKENS];
int token_pos = 0;
int token_count = 0;

char *strdup_safe(const char *s) {
    if (!s) return NULL;
    char *dup = malloc(strlen(s) + 1);
    if (dup) strcpy(dup, s);
    return dup;
}

void error(const char *msg) {
    perror(msg);
    exit(EXIT_FAILURE);
}

char *expand_var(char *word) {
    if (!word || word[0] != '$') return strdup_safe(word);
    char *var_name = word + 1;
    for (int i = 0; i < var_count; i++) {
        if (strcmp(vars[i].name, var_name) == 0) return strdup_safe(vars[i].value);
    }
    return strdup_safe(getenv(var_name) ? getenv(var_name) : "");
}

void set_var(const char *name, const char *value) {
    for (int i = 0; i < var_count; i++) {
        if (strcmp(vars[i].name, name) == 0) {
            free(vars[i].value);
            vars[i].value = strdup_safe(value);
            return;
        }
    }
    if (var_count < MAX_VARS) {
        vars[var_count].name = strdup_safe(name);
        vars[var_count].value = strdup_safe(value);
        var_count++;
    }
}

void set_function(const char *name, const char *body) {
    for (int i = 0; i < func_count; i++) {
        if (strcmp(funcs[i].name, name) == 0) {
            free(funcs[i].body);
            funcs[i].body = strdup_safe(body);
            return;
        }
    }
    if (func_count < MAX_FUNCS) {
        funcs[func_count].name = strdup_safe(name);
        funcs[func_count].body = strdup_safe(body);
        func_count++;
    }
}

char *get_function(const char *name) {
    for (int i = 0; i < func_count; i++) {
        if (strcmp(funcs[i].name, name) == 0) return funcs[i].body;
    }
    return NULL;
}

void tokenize(char *input) {
    token_count = 0;
    char *p = input;
    while (*p && token_count < MAX_TOKENS - 1) {
        while (isspace(*p)) p++;
        if (!*p) break;

        Token *t = &tokens[token_count];
        if (strncmp(p, "&&", 2) == 0) { t->type = TOK_AND_IF; p += 2; }
        else if (strncmp(p, "||", 2) == 0) { t->type = TOK_OR_IF; p += 2; }
        else if (strncmp(p, ";;", 2) == 0) { t->type = TOK_DSEMI; p += 2; }
        else if (strncmp(p, "<<-", 3) == 0) { t->type = TOK_DLESSDASH; p += 3; }
        else if (strncmp(p, "<<", 2) == 0) { t->type = TOK_DLESS; p += 2; }
        else if (strncmp(p, ">>", 2) == 0) { t->type = TOK_DGREAT; p += 2; }
        else if (strncmp(p, "<&", 2) == 0) { t->type = TOK_LESSAND; p += 2; }
        else if (strncmp(p, ">&", 2) == 0) { t->type = TOK_GREATAND; p += 2; }
        else if (strncmp(p, "<>", 2) == 0) { t->type = TOK_LESSGREAT; p += 2; }
        else if (strncmp(p, ">|", 2) == 0) { t->type = TOK_CLOBBER; p += 2; }
        else if (strncmp(p, "if", 2) == 0 && !isalnum(p[2])) { t->type = TOK_IF; p += 2; }
        else if (strncmp(p, "then", 4) == 0 && !isalnum(p[4])) { t->type = TOK_THEN; p += 4; }
        else if (strncmp(p, "else", 4) == 0 && !isalnum(p[4])) { t->type = TOK_ELSE; p += 4; }
        else if (strncmp(p, "elif", 4) == 0 && !isalnum(p[4])) { t->type = TOK_ELIF; p += 4; }
        else if (strncmp(p, "fi", 2) == 0 && !isalnum(p[2])) { t->type = TOK_FI; p += 2; }
        else if (strncmp(p, "do", 2) == 0 && !isalnum(p[2])) { t->type = TOK_DO; p += 2; }
        else if (strncmp(p, "done", 4) == 0 && !isalnum(p[4])) { t->type = TOK_DONE; p += 4; }
        else if (strncmp(p, "case", 4) == 0 && !isalnum(p[4])) { t->type = TOK_CASE; p += 4; }
        else if (strncmp(p, "esac", 4) == 0 && !isalnum(p[4])) { t->type = TOK_ESAC; p += 4; }
        else if (strncmp(p, "while", 5) == 0 && !isalnum(p[5])) { t->type = TOK_WHILE; p += 5; }
        else if (strncmp(p, "until", 5) == 0 && !isalnum(p[5])) { t->type = TOK_UNTIL; p += 5; }
        else if (strncmp(p, "for", 3) == 0 && !isalnum(p[3])) { t->type = TOK_FOR; p += 3; }
        else if (strncmp(p, "in", 2) == 0 && !isalnum(p[2])) { t->type = TOK_IN; p += 2; }
        else if (*p == '{') { t->type = TOK_LBRACE; p++; }
        else if (*p == '}') { t->type = TOK_RBRACE; p++; }
        else if (*p == '!') { t->type = TOK_BANG; p++; }
        else if (*p == '(') { t->type = TOK_LPAREN; p++; }
        else if (*p == ')') { t->type = TOK_RPAREN; p++; }
        else if (*p == '<') { t->type = TOK_LESS; p++; }
        else if (*p == '>') { t->type = TOK_GREAT; p++; }
        else if (*p == ';') { t->type = TOK_SEMI; p++; }
        else if (*p == '|') { t->type = TOK_PIPE; p++; }
        else if (*p == '&') { t->type = TOK_AMP; p++; }
        else if (*p == '\n') { t->type = TOK_NEWLINE; p++; }
        else {
            char *start = p;
            if (isdigit(*p)) {
                while (isdigit(*p)) p++;
                if (*p == '<' || *p == '>') {
                    t->type = TOK_IO_NUMBER;
                    t->value = strndup(start, p - start);
                    token_count++;
                    continue;
                }
                p = start;
            }
            while (*p && !isspace(*p) && *p != ';' && *p != '|' && *p != '&' && *p != '<' && *p != '>' && *p != '(' && *p != ')' && *p != '{' && *p != '}') p++;
            t->value = strndup(start, p - start);
            t->type = (strchr(t->value, '=') && t->value[0] != '=') ? TOK_ASSIGNMENT : TOK_WORD;
        }
        token_count++;
    }
    tokens[token_count].type = TOK_EOF;
}

Token *next_token() {
    return &tokens[token_pos++];
}

void expect(TokenType type) {
    Token *t = next_token();
    if (t->type != type) {
        fprintf(stderr, "Syntax error: expected %d, got %d\n", type, t->type);
        exit(1);
    }
}

int apply_redirect(int io_number, TokenType op, char *filename) {
    int fd, target;
    switch (op) {
        case TOK_LESS:
            fd = open(filename, O_RDONLY);
            target = io_number >= 0 ? io_number : 0;
            break;
        case TOK_GREAT:
            fd = open(filename, O_WRONLY | O_CREAT | O_TRUNC, 0644);
            target = io_number >= 0 ? io_number : 1;
            break;
        case TOK_DGREAT:
            fd = open(filename, O_WRONLY | O_CREAT | O_APPEND, 0644);
            target = io_number >= 0 ? io_number : 1;
            break;
        case TOK_CLOBBER:
            fd = open(filename, O_WRONLY | O_CREAT | O_TRUNC, 0644);
            target = io_number >= 0 ? io_number : 1;
            break;
        default:
            return -1;
    }
    if (fd < 0) error("open");
    dup2(fd, target);
    close(fd);
    return 0;
}

int execute_simple_command(char **args, int *redirects) {
    if (!args[0]) return 0;

    char *func = get_function(args[0]);
    if (func) {
        tokenize(func);
        token_pos = 0;
        int result = parse_program();
        return result;
    }

    pid_t pid = fork();
    if (pid == 0) {
        for (int i = 0; redirects[i] != -1; i += 3) {
            apply_redirect(redirects[i], redirects[i + 1], args[redirects[i + 2]]);
        }
        execvp(args[0], args);
        error("execvp");
    } else if (pid > 0) {
        int status;
        waitpid(pid, &status, 0);
        return WEXITSTATUS(status);
    } else {
        error("fork");
    }
    return 1;
}

int parse_io_redirect(int *redirects, int *redir_count) {
    Token *t = next_token();
    int io_number = -1;
    if (t->type == TOK_IO_NUMBER) {
        io_number = atoi(t->value);
        t = next_token();
    }
    if (t->type == TOK_LESS || t->type == TOK_GREAT || t->type == TOK_DGREAT || t->type == TOK_CLOBBER) {
        Token *file = next_token();
        if (file->type != TOK_WORD) {
            fprintf(stderr, "Syntax error: expected filename\n");
            exit(1);
        }
        redirects[*redir_count] = io_number;
        redirects[*redir_count + 1] = t->type;
        redirects[*redir_count + 2] = *redir_count / 3; // Index into args for filename
        *redir_count += 3;
        return 1;
    }
    token_pos--;
    return 0;
}

int parse_simple_command() {
    char *args[MAX_ARGS] = {0};
    int argc = 0;
    int redirects[3 * MAX_ARGS] = {-1};
    int redir_count = 0;

    Token *t;
    while ((t = next_token())->type != TOK_EOF && t->type != TOK_SEMI && t->type != TOK_NEWLINE && t->type != TOK_PIPE) {
        if (t->type == TOK_WORD) {
            args[argc++] = expand_var(t->value);
        } else if (t->type == TOK_ASSIGNMENT) {
            char *eq = strchr(t->value, '=');
            *eq = 0;
            set_var(t->value, eq + 1);
        } else if (t->type == TOK_IO_NUMBER || t->type == TOK_LESS || t->type == TOK_GREAT || t->type == TOK_DGREAT || t->type == TOK_CLOBBER) {
            token_pos--;
            parse_io_redirect(redirects, &redir_count);
            args[argc++] = expand_var(next_token()->value); // Filename
        } else {
            token_pos--;
            break;
        }
    }
    args[argc] = NULL;
    redirects[redir_count] = -1;
    int result = execute_simple_command(args, redirects);
    for (int i = 0; i < argc; i++) free(args[i]);
    return result;
}

int parse_pipeline() {
    int pipefd[2];
    pid_t pid;
    int status = 0;
    int in_fd = 0;

    while (1) {
        Token *t = next_token();
        if (t->type == TOK_BANG) {
            status = !parse_pipeline();
            break;
        }
        token_pos--;

        if (pipe(pipefd) < 0) error("pipe");
        pid = fork();
        if (pid == 0) {
            if (in_fd != 0) {
                dup2(in_fd, 0);
                close(in_fd);
            }
            if ((t = next_token())->type == TOK_PIPE) {
                close(pipefd[0]);
                dup2(pipefd[1], 1);
                close(pipefd[1]);
            } else {
                token_pos--;
            }
            exit(parse_simple_command());
        } else if (pid > 0) {
            close(pipefd[1]);
            if (in_fd != 0) close(in_fd);
            in_fd = pipefd[0];
            t = next_token();
            if (t->type != TOK_PIPE) {
                token_pos--;
                waitpid(pid, &status, 0);
                break;
            }
        } else {
            error("fork");
        }
    }
    return WEXITSTATUS(status);
}

int parse_and_or() {
    int result = parse_pipeline();
    Token *t;
    while ((t = next_token())->type == TOK_AND_IF || t->type == TOK_OR_IF) {
        if (t->type == TOK_AND_IF) {
            if (result == 0) result = parse_pipeline();
        } else {
            if (result != 0) result = parse_pipeline();
        }
    }
    token_pos--;
    return result;
}

int parse_compound_list() {
    int result = 0;
    Token *t;
    while ((t = next_token())->type != TOK_EOF && t->type != TOK_DONE && t->type != TOK_FI && t->type != TOK_ESAC) {
        token_pos--;
        result = parse_and_or();
        t = next_token();
        if (t->type == TOK_SEMI || t->type == TOK_NEWLINE) continue;
        token_pos--;
    }
    token_pos--;
    return result;
}

int parse_if_clause() {
    expect(TOK_IF);
    int cond = parse_compound_list();
    expect(TOK_THEN);
    int result = 0;
    if (cond == 0) result = parse_compound_list();
    Token *t = next_token();
    if (t->type == TOK_ELSE) {
        if (cond != 0) result = parse_compound_list();
    } else if (t->type == TOK_ELIF) {
        token_pos--;
        if (cond != 0) result = parse_if_clause();
    } else {
        token_pos--;
    }
    expect(TOK_FI);
    return result;
}

int parse_while_clause() {
    expect(TOK_WHILE);
    int cond = parse_compound_list();
    expect(TOK_DO);
    int result = 0;
    while (cond == 0) {
        result = parse_compound_list();
        cond = parse_compound_list();
    }
    expect(TOK_DONE);
    return result;
}

int parse_for_clause() {
    expect(TOK_FOR);
    Token *var = next_token();
    if (var->type != TOK_WORD) {
        fprintf(stderr, "Syntax error: for expects variable\n");
        exit(1);
    }
    Token *t = next_token();
    char *words[MAX_ARGS] = {0};
    int word_count = 0;
    if (t->type == TOK_IN) {
        while ((t = next_token())->type == TOK_WORD && word_count < MAX_ARGS - 1) {
            words[word_count++] = expand_var(t->value);
        }
        token_pos--;
    } else {
        token_pos--;
    }
    expect(TOK_DO);
    int result = 0;
    for (int i = 0; i < word_count; i++) {
        set_var(var->value, words[i]);
        result = parse_compound_list();
    }
    expect(TOK_DONE);
    return result;
}

int parse_function_definition() {
    Token *name = next_token();
    if (name->type != TOK_WORD) {
        fprintf(stderr, "Syntax error: function expects name\n");
        exit(1);
    }
    expect(TOK_LPAREN);
    expect(TOK_RPAREN);
    char body[SH_MAX_INPUT] = {0};
    int len = 0;
    Token *t;
    while ((t = next_token())->type != TOK_RBRACE && t->type != TOK_EOF) {
        if (t->type == TOK_WORD) {
            len += snprintf(body + len, SH_MAX_INPUT - len, "%s ", t->value);
        } else if (t->type == TOK_SEMI) {
            len += snprintf(body + len, SH_MAX_INPUT - len, "; ");
        }
    }
    set_function(name->value, body);
    return 0;
}

int parse_program() {
    int result = 0;
    Token *t;
    while ((t = next_token())->type != TOK_EOF) {
        token_pos--;
        result = parse_and_or();
        t = next_token();
        if (t->type == TOK_SEMI || t->type == TOK_NEWLINE || t->type == TOK_AMP) continue;
        token_pos--;
    }
    return result;
}

int main() {
    char input[SH_MAX_INPUT];
    while (1) {
        printf("$ ");
        if (!fgets(input, sizeof(input), stdin)) break;
        input[strcspn(input, "\n")] = 0;
        if (strlen(input) == 0) continue;
        tokenize(input);
        token_pos = 0;
        parse_program();
    }
    return 0;
}

