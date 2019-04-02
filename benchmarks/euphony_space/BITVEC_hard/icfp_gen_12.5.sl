(set-logic BV)
(synth-fun f ((x (_ BitVec 64))) (_ BitVec 64)
  ((Start (_ BitVec 64)) (StartBool Bool))
  ((Start (_ BitVec 64)
            (
              (bvnot Start)
              (bvxor Start Start)
              (bvand Start Start)
              (bvor Start Start)
              (bvneg Start)
              (bvadd Start Start)
              (bvmul Start Start)
              (bvudiv Start Start)
              (bvurem Start Start)
              (bvlshr Start Start)
              (bvashr Start Start)
              (bvshl Start Start)
              (bvsdiv Start Start)
              (bvsrem Start Start)
              (bvsub Start Start)
              x
              #x0000000000000000
              #x0000000000000001
              #x0000000000000002
              #x0000000000000003
              #x0000000000000004
              #x0000000000000005
              #x0000000000000006
              #x0000000000000007
              #x0000000000000008
              #x0000000000000009
              #x0000000000000009
              #x0000000000000009
              #x000000000000000A
              #x000000000000000B
              #x000000000000000C
              #x000000000000000D
              #x000000000000000E
              #x000000000000000F
              #x0000000000000010
              #x0000000000000011
              #x0000000000000012
              #x0000000000000013
              #x0000000000000014
              #x0000000000000015
              #x0000000000000016
              #x0000000000000017
              #x0000000000000018
              #x0000000000000019
              #x000000000000001A
              #x000000000000001B
              #x000000000000001C
              #x000000000000001D
              #x000000000000001E
              #x000000000000001F
              (ite StartBool Start Start)
            ))
  (StartBool Bool
            (
              (= Start Start)
              (not StartBool)
              (and StartBool StartBool)
              (or StartBool StartBool)
              (xor StartBool StartBool)
            ))
            ))
(constraint (= (f #x6A417BFA141EFFFF) #x6A417BFA141EFFFF))
(constraint (= (f #x9A19AA3639A1731C) #x9A19AA3639A1731D))
(constraint (= (f #xBB8F8177049D16BE) #xBB8F8177049D16BF))
(constraint (= (f #x34FB0E1CA10DD336) #x34FB0E1CA10DD337))
(constraint (= (f #x619D7D423C8D6401) #x619D7D423C8D6401))
(constraint (= (f #x7170BD10C7C4C2C4) #x7170BD10C7C4C2C5))
(constraint (= (f #x0C8D7659D8A6B63B) #x0C8D7659D8A6B63D))
(constraint (= (f #xA9084D35EA38F366) #xA9084D35EA38F367))
(constraint (= (f #xA2CD1BC056C66869) #xA2CD1BC056C6686B))
(constraint (= (f #x5BCA9932A21AB05D) #x5BCA9932A21AB05F))
(constraint (= (f #x00000000000FD846) #x00000000000FD846))
(constraint (= (f #x00000000000F5C06) #x00000000000F5C06))
(constraint (= (f #x00000000000EFFFF) #x00000000000EFFFF))
(constraint (= (f #x80000000000D0618) #x80000000000D0618))
(constraint (= (f #x00000000000D5F6B) #x00000000000D5F6B))
(constraint (= (f #x000000000000FFFF) #x0000000000010001))
(constraint (= (f #x800000000000FFFF) #x8000000000010001))
(constraint (= (f #x0000000000000002) #x0000000000000005))
(constraint (= (f #x8000000000000002) #x0000000000000005))
(constraint (= (f #x80000000000E5E1E) #x80000000000E5E1F))
(constraint (= (f #x800000000008970D) #x800000000008970F))
(constraint (= (f #x80000000000C27A0) #x80000000000C27A1))
(constraint (= (f #x80000000000C8238) #x80000000000C8239))
(constraint (= (f #x80000000000EC2B0) #x80000000000EC2B1))
(constraint (= (f #x800000000000F425) #x800000000000F427))
(constraint (= (f #x800000000000DAE1) #x800000000000DAE3))
(constraint (= (f #x800000000000A62F) #x800000000000A631))
(constraint (= (f #x000000000000CA62) #x000000000000CA63))
(constraint (= (f #x000000000000CB3A) #x000000000000CB3B))
(check-synth)
