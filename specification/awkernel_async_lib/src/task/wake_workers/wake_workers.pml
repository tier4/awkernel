#define TASK_NUM 4
#define WORKERS 2

proctype run_main(int tid) {
    skip;
}

proctype primary_main() {
    skip;
}

proctype spawn_tasks() {
    skip;
}

init {
    int i;

    run primary_main();

    for (i: 0 .. WORKERS - 1) {
        run run_main(i);
    }

    run spawn_tasks();

    skip;
}