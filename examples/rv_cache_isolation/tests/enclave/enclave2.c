#define DB_SIZE 32

typedef struct {
  char password;
  int secret_key;
} DbData;

// DbData db[DB_SIZE];
// TODO: What's the right way to do this?
extern void persistent_base2(void);
DbData * db = (DbData *) &persistent_base2;


// NOTE: We overwrite passwords here and can leak information through this
int add_password(unsigned int id, char value, int secret) {
  if (id < DB_SIZE) {
    db[id] = (DbData){.password = value,
                      .secret_key = secret };
    return 0;
  } else {
    return 1;
  }
}

char lookup(unsigned int id, int secret) {
  if (id < DB_SIZE && (db[id].secret_key == secret) ) {
    return db[id].password;
  } else {
    return 0;
  }
}
