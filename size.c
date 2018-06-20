#include <stdio.h>
#define MI(t,n,i) I(sizeof(t),n,i)
#define P(v) if(v!=NULL){printf(#v);printf(":%s\n",v);}
typedef char* string;
string i8 = NULL, n8 = NULL, i16 = NULL, n16 = NULL, i32 = NULL, n32 = NULL, i64 = NULL, n64 = NULL;
void I(unsigned char l,string n,string i) {
	switch(l){
		case 1:i8=i;n8=n;break;
		case 2:i16=i;n16=n;break;
		case 4:i32=i;n32=n;break;
		case 8:i64=i;n64=n;break;
	}
}
int main(){
	MI(int,"unsigned int","signed int");
	MI(short,"unsigned short","signed short");
	MI(char,"unsigned char","signed char");
	MI(long,"unsigned long","signed long");
	MI(long long,"unsigned long long","signed long long");
	P(i8);P(n8);P(i16);P(n16);P(i32);P(n32);P(i64);P(n64);
	return 0;
}
