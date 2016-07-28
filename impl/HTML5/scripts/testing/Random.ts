export function rand(): number
{
    return Math.floor(Math.random() * 9007199254740991); // Number.MAX_SAFE_INTEGER;
}