export const snake_case = (str = '') => {
    const strArr = str.split(' ');
    const snakeArr = strArr.reduce((acc:string[], val:string) => {
       return acc.concat(val.toLowerCase());
    }, []);
    return snakeArr.join('_');
};
