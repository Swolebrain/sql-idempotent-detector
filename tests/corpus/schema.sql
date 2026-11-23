-- Schema used by the corpus in tests/corpus/*.toml.
CREATE TABLE users (
  id         int8 PRIMARY KEY,
  status     text NOT NULL,
  logins     int4 NOT NULL DEFAULT 0,
  score      int4,
  a          int4,
  b          int4,
  small      int2,
  flag       boolean,
  email      text,
  updated_at timestamptz,
  token      uuid,
  price      numeric(10,2)
);

CREATE TABLE audited (id int8 PRIMARY KEY, n int4);
CREATE TRIGGER audit BEFORE UPDATE ON audited FOR EACH ROW EXECUTE FUNCTION audit_fn();

CREATE TABLE checked (id int8 PRIMARY KEY, n int4 CHECK (n >= 0));

CREATE TABLE parent (id int8 PRIMARY KEY, name text);
CREATE TABLE child (id int8 PRIMARY KEY, parent_id int8 REFERENCES parent(id) ON DELETE CASCADE, v int4);

CREATE VIEW active_users AS SELECT * FROM users WHERE status = 'active';

CREATE TABLE secured (id int8 PRIMARY KEY, n int4);
ALTER TABLE secured ENABLE ROW LEVEL SECURITY;
