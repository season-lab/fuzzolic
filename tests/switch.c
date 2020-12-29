int switchf(int v) {
    int res = -1;
    switch (v) {
        case 0:
            res = 1111;
            break;
        case 1:
            res = 2111;
            break;
        case 2:
            res = 3333;
            break;
        case 3:
            res = 4444;
            break;
        case 4:
            res = 5555;
            break;
        case 5:
            res = 6666;
            break;
        case 6:
            res = 7777;
            break;
        default:
            res = 0;
    }
    if (res == 5555)
        res = 1;
    else
        res = 0;

    return res;
}