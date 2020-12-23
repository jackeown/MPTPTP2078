%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : tmap_1__t8_tmap_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:21 EDT 2019

% Result     : Theorem 7.57s
% Output     : CNFRefutation 7.57s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 402 expanded)
%              Number of clauses        :   38 ( 126 expanded)
%              Number of leaves         :    6 ( 103 expanded)
%              Depth                    :   12
%              Number of atoms          :  441 (5251 expanded)
%              Number of equality atoms :   59 ( 379 expanded)
%              Maximal formula depth    :   28 (   9 average)
%              Maximal clause size      :   55 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d1_tmap_1,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ~ v1_xboole_0(X2)
         => ! [X3] :
              ( ( ~ v1_xboole_0(X3)
                & m1_subset_1(X3,k1_zfmisc_1(X1)) )
             => ! [X4] :
                  ( ( ~ v1_xboole_0(X4)
                    & m1_subset_1(X4,k1_zfmisc_1(X1)) )
                 => ! [X5] :
                      ( ( v1_funct_1(X5)
                        & v1_funct_2(X5,X3,X2)
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) )
                     => ! [X6] :
                          ( ( v1_funct_1(X6)
                            & v1_funct_2(X6,X4,X2)
                            & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) )
                         => ( k2_partfun1(X3,X2,X5,k9_subset_1(X1,X3,X4)) = k2_partfun1(X4,X2,X6,k9_subset_1(X1,X3,X4))
                           => ! [X7] :
                                ( ( v1_funct_1(X7)
                                  & v1_funct_2(X7,k4_subset_1(X1,X3,X4),X2)
                                  & m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,X3,X4),X2))) )
                               => ( X7 = k1_tmap_1(X1,X2,X3,X4,X5,X6)
                                <=> ( k2_partfun1(k4_subset_1(X1,X3,X4),X2,X7,X3) = X5
                                    & k2_partfun1(k4_subset_1(X1,X3,X4),X2,X7,X4) = X6 ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t8_tmap_1.p',d1_tmap_1)).

fof(commutativity_k4_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => k4_subset_1(X1,X2,X3) = k4_subset_1(X1,X3,X2) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t8_tmap_1.p',commutativity_k4_subset_1)).

fof(dt_k1_tmap_1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X2)
        & ~ v1_xboole_0(X3)
        & m1_subset_1(X3,k1_zfmisc_1(X1))
        & ~ v1_xboole_0(X4)
        & m1_subset_1(X4,k1_zfmisc_1(X1))
        & v1_funct_1(X5)
        & v1_funct_2(X5,X3,X2)
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
        & v1_funct_1(X6)
        & v1_funct_2(X6,X4,X2)
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) )
     => ( v1_funct_1(k1_tmap_1(X1,X2,X3,X4,X5,X6))
        & v1_funct_2(k1_tmap_1(X1,X2,X3,X4,X5,X6),k4_subset_1(X1,X3,X4),X2)
        & m1_subset_1(k1_tmap_1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,X3,X4),X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t8_tmap_1.p',dt_k1_tmap_1)).

fof(t8_tmap_1,conjecture,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ~ v1_xboole_0(X2)
         => ! [X3] :
              ( ( ~ v1_xboole_0(X3)
                & m1_subset_1(X3,k1_zfmisc_1(X1)) )
             => ! [X4] :
                  ( ( ~ v1_xboole_0(X4)
                    & m1_subset_1(X4,k1_zfmisc_1(X1)) )
                 => ! [X5] :
                      ( ( v1_funct_1(X5)
                        & v1_funct_2(X5,X3,X2)
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) )
                     => ! [X6] :
                          ( ( v1_funct_1(X6)
                            & v1_funct_2(X6,X4,X2)
                            & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) )
                         => ( k2_partfun1(X3,X2,X5,k9_subset_1(X1,X3,X4)) = k2_partfun1(X4,X2,X6,k9_subset_1(X1,X3,X4))
                           => r1_funct_2(k4_subset_1(X1,X3,X4),X2,k4_subset_1(X1,X4,X3),X2,k1_tmap_1(X1,X2,X3,X4,X5,X6),k1_tmap_1(X1,X2,X4,X3,X6,X5)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t8_tmap_1.p',t8_tmap_1)).

fof(commutativity_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k9_subset_1(X1,X3,X2) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t8_tmap_1.p',commutativity_k9_subset_1)).

fof(redefinition_r1_funct_2,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( ~ v1_xboole_0(X2)
        & ~ v1_xboole_0(X4)
        & v1_funct_1(X5)
        & v1_funct_2(X5,X1,X2)
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X6)
        & v1_funct_2(X6,X3,X4)
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
     => ( r1_funct_2(X1,X2,X3,X4,X5,X6)
      <=> X5 = X6 ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t8_tmap_1.p',redefinition_r1_funct_2)).

fof(c_0_6,plain,(
    ! [X26,X27,X28,X29,X30,X31,X32] :
      ( ( k2_partfun1(k4_subset_1(X26,X28,X29),X27,X32,X28) = X30
        | X32 != k1_tmap_1(X26,X27,X28,X29,X30,X31)
        | ~ v1_funct_1(X32)
        | ~ v1_funct_2(X32,k4_subset_1(X26,X28,X29),X27)
        | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X26,X28,X29),X27)))
        | k2_partfun1(X28,X27,X30,k9_subset_1(X26,X28,X29)) != k2_partfun1(X29,X27,X31,k9_subset_1(X26,X28,X29))
        | ~ v1_funct_1(X31)
        | ~ v1_funct_2(X31,X29,X27)
        | ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X27)))
        | ~ v1_funct_1(X30)
        | ~ v1_funct_2(X30,X28,X27)
        | ~ m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X27)))
        | v1_xboole_0(X29)
        | ~ m1_subset_1(X29,k1_zfmisc_1(X26))
        | v1_xboole_0(X28)
        | ~ m1_subset_1(X28,k1_zfmisc_1(X26))
        | v1_xboole_0(X27)
        | v1_xboole_0(X26) )
      & ( k2_partfun1(k4_subset_1(X26,X28,X29),X27,X32,X29) = X31
        | X32 != k1_tmap_1(X26,X27,X28,X29,X30,X31)
        | ~ v1_funct_1(X32)
        | ~ v1_funct_2(X32,k4_subset_1(X26,X28,X29),X27)
        | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X26,X28,X29),X27)))
        | k2_partfun1(X28,X27,X30,k9_subset_1(X26,X28,X29)) != k2_partfun1(X29,X27,X31,k9_subset_1(X26,X28,X29))
        | ~ v1_funct_1(X31)
        | ~ v1_funct_2(X31,X29,X27)
        | ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X27)))
        | ~ v1_funct_1(X30)
        | ~ v1_funct_2(X30,X28,X27)
        | ~ m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X27)))
        | v1_xboole_0(X29)
        | ~ m1_subset_1(X29,k1_zfmisc_1(X26))
        | v1_xboole_0(X28)
        | ~ m1_subset_1(X28,k1_zfmisc_1(X26))
        | v1_xboole_0(X27)
        | v1_xboole_0(X26) )
      & ( k2_partfun1(k4_subset_1(X26,X28,X29),X27,X32,X28) != X30
        | k2_partfun1(k4_subset_1(X26,X28,X29),X27,X32,X29) != X31
        | X32 = k1_tmap_1(X26,X27,X28,X29,X30,X31)
        | ~ v1_funct_1(X32)
        | ~ v1_funct_2(X32,k4_subset_1(X26,X28,X29),X27)
        | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X26,X28,X29),X27)))
        | k2_partfun1(X28,X27,X30,k9_subset_1(X26,X28,X29)) != k2_partfun1(X29,X27,X31,k9_subset_1(X26,X28,X29))
        | ~ v1_funct_1(X31)
        | ~ v1_funct_2(X31,X29,X27)
        | ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X27)))
        | ~ v1_funct_1(X30)
        | ~ v1_funct_2(X30,X28,X27)
        | ~ m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X27)))
        | v1_xboole_0(X29)
        | ~ m1_subset_1(X29,k1_zfmisc_1(X26))
        | v1_xboole_0(X28)
        | ~ m1_subset_1(X28,k1_zfmisc_1(X26))
        | v1_xboole_0(X27)
        | v1_xboole_0(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_tmap_1])])])])])).

fof(c_0_7,plain,(
    ! [X20,X21,X22] :
      ( ~ m1_subset_1(X21,k1_zfmisc_1(X20))
      | ~ m1_subset_1(X22,k1_zfmisc_1(X20))
      | k4_subset_1(X20,X21,X22) = k4_subset_1(X20,X22,X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[commutativity_k4_subset_1])])).

fof(c_0_8,plain,(
    ! [X33,X34,X35,X36,X37,X38] :
      ( ( v1_funct_1(k1_tmap_1(X33,X34,X35,X36,X37,X38))
        | v1_xboole_0(X33)
        | v1_xboole_0(X34)
        | v1_xboole_0(X35)
        | ~ m1_subset_1(X35,k1_zfmisc_1(X33))
        | v1_xboole_0(X36)
        | ~ m1_subset_1(X36,k1_zfmisc_1(X33))
        | ~ v1_funct_1(X37)
        | ~ v1_funct_2(X37,X35,X34)
        | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X34)))
        | ~ v1_funct_1(X38)
        | ~ v1_funct_2(X38,X36,X34)
        | ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X34))) )
      & ( v1_funct_2(k1_tmap_1(X33,X34,X35,X36,X37,X38),k4_subset_1(X33,X35,X36),X34)
        | v1_xboole_0(X33)
        | v1_xboole_0(X34)
        | v1_xboole_0(X35)
        | ~ m1_subset_1(X35,k1_zfmisc_1(X33))
        | v1_xboole_0(X36)
        | ~ m1_subset_1(X36,k1_zfmisc_1(X33))
        | ~ v1_funct_1(X37)
        | ~ v1_funct_2(X37,X35,X34)
        | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X34)))
        | ~ v1_funct_1(X38)
        | ~ v1_funct_2(X38,X36,X34)
        | ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X34))) )
      & ( m1_subset_1(k1_tmap_1(X33,X34,X35,X36,X37,X38),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X33,X35,X36),X34)))
        | v1_xboole_0(X33)
        | v1_xboole_0(X34)
        | v1_xboole_0(X35)
        | ~ m1_subset_1(X35,k1_zfmisc_1(X33))
        | v1_xboole_0(X36)
        | ~ m1_subset_1(X36,k1_zfmisc_1(X33))
        | ~ v1_funct_1(X37)
        | ~ v1_funct_2(X37,X35,X34)
        | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X34)))
        | ~ v1_funct_1(X38)
        | ~ v1_funct_2(X38,X36,X34)
        | ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X34))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tmap_1])])])])).

cnf(c_0_9,plain,
    ( X5 = k1_tmap_1(X1,X4,X2,X3,X6,X7)
    | v1_xboole_0(X3)
    | v1_xboole_0(X2)
    | v1_xboole_0(X4)
    | v1_xboole_0(X1)
    | k2_partfun1(k4_subset_1(X1,X2,X3),X4,X5,X2) != X6
    | k2_partfun1(k4_subset_1(X1,X2,X3),X4,X5,X3) != X7
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,k4_subset_1(X1,X2,X3),X4)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,X2,X3),X4)))
    | k2_partfun1(X2,X4,X6,k9_subset_1(X1,X2,X3)) != k2_partfun1(X3,X4,X7,k9_subset_1(X1,X2,X3))
    | ~ v1_funct_1(X7)
    | ~ v1_funct_2(X7,X3,X4)
    | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ v1_funct_1(X6)
    | ~ v1_funct_2(X6,X2,X4)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( k4_subset_1(X2,X1,X3) = k4_subset_1(X2,X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,plain,
    ( k2_partfun1(k4_subset_1(X1,X2,X3),X4,X5,X2) = X6
    | v1_xboole_0(X3)
    | v1_xboole_0(X2)
    | v1_xboole_0(X4)
    | v1_xboole_0(X1)
    | X5 != k1_tmap_1(X1,X4,X2,X3,X6,X7)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,k4_subset_1(X1,X2,X3),X4)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,X2,X3),X4)))
    | k2_partfun1(X2,X4,X6,k9_subset_1(X1,X2,X3)) != k2_partfun1(X3,X4,X7,k9_subset_1(X1,X2,X3))
    | ~ v1_funct_1(X7)
    | ~ v1_funct_2(X7,X3,X4)
    | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ v1_funct_1(X6)
    | ~ v1_funct_2(X6,X2,X4)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_12,plain,
    ( m1_subset_1(k1_tmap_1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,X3,X4),X2)))
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | v1_xboole_0(X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X1))
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,X3,X2)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ v1_funct_1(X6)
    | ~ v1_funct_2(X6,X4,X2)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( v1_funct_1(k1_tmap_1(X1,X2,X3,X4,X5,X6))
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | v1_xboole_0(X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X1))
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,X3,X2)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ v1_funct_1(X6)
    | ~ v1_funct_2(X6,X4,X2)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,plain,
    ( v1_funct_2(k1_tmap_1(X1,X2,X3,X4,X5,X6),k4_subset_1(X1,X3,X4),X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | v1_xboole_0(X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X1))
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,X3,X2)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ v1_funct_1(X6)
    | ~ v1_funct_2(X6,X4,X2)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,plain,
    ( X1 = k1_tmap_1(X2,X3,X4,X5,X6,X7)
    | v1_xboole_0(X3)
    | v1_xboole_0(X5)
    | v1_xboole_0(X4)
    | v1_xboole_0(X2)
    | k2_partfun1(X4,X3,X6,k9_subset_1(X2,X4,X5)) != k2_partfun1(X5,X3,X7,k9_subset_1(X2,X4,X5))
    | k2_partfun1(k4_subset_1(X2,X5,X4),X3,X1,X5) != X7
    | k2_partfun1(k4_subset_1(X2,X5,X4),X3,X1,X4) != X6
    | ~ v1_funct_2(X1,k4_subset_1(X2,X5,X4),X3)
    | ~ v1_funct_2(X7,X5,X3)
    | ~ v1_funct_2(X6,X4,X3)
    | ~ v1_funct_1(X7)
    | ~ v1_funct_1(X6)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X2,X5,X4),X3)))
    | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X5,X3)))
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X3)))
    | ~ m1_subset_1(X5,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_16,plain,
    ( k2_partfun1(k4_subset_1(X1,X2,X3),X4,k1_tmap_1(X1,X4,X2,X3,X5,X6),X2) = X5
    | v1_xboole_0(X4)
    | v1_xboole_0(X3)
    | v1_xboole_0(X2)
    | v1_xboole_0(X1)
    | k2_partfun1(X2,X4,X5,k9_subset_1(X1,X2,X3)) != k2_partfun1(X3,X4,X6,k9_subset_1(X1,X2,X3))
    | ~ v1_funct_2(X6,X3,X4)
    | ~ v1_funct_2(X5,X2,X4)
    | ~ v1_funct_1(X6)
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_11]),c_0_12]),c_0_13]),c_0_14])).

cnf(c_0_17,plain,
    ( k2_partfun1(k4_subset_1(X1,X2,X3),X4,X5,X3) = X6
    | v1_xboole_0(X3)
    | v1_xboole_0(X2)
    | v1_xboole_0(X4)
    | v1_xboole_0(X1)
    | X5 != k1_tmap_1(X1,X4,X2,X3,X7,X6)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,k4_subset_1(X1,X2,X3),X4)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,X2,X3),X4)))
    | k2_partfun1(X2,X4,X7,k9_subset_1(X1,X2,X3)) != k2_partfun1(X3,X4,X6,k9_subset_1(X1,X2,X3))
    | ~ v1_funct_1(X6)
    | ~ v1_funct_2(X6,X3,X4)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ v1_funct_1(X7)
    | ~ v1_funct_2(X7,X2,X4)
    | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_18,negated_conjecture,(
    ~ ! [X1] :
        ( ~ v1_xboole_0(X1)
       => ! [X2] :
            ( ~ v1_xboole_0(X2)
           => ! [X3] :
                ( ( ~ v1_xboole_0(X3)
                  & m1_subset_1(X3,k1_zfmisc_1(X1)) )
               => ! [X4] :
                    ( ( ~ v1_xboole_0(X4)
                      & m1_subset_1(X4,k1_zfmisc_1(X1)) )
                   => ! [X5] :
                        ( ( v1_funct_1(X5)
                          & v1_funct_2(X5,X3,X2)
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) )
                       => ! [X6] :
                            ( ( v1_funct_1(X6)
                              & v1_funct_2(X6,X4,X2)
                              & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) )
                           => ( k2_partfun1(X3,X2,X5,k9_subset_1(X1,X3,X4)) = k2_partfun1(X4,X2,X6,k9_subset_1(X1,X3,X4))
                             => r1_funct_2(k4_subset_1(X1,X3,X4),X2,k4_subset_1(X1,X4,X3),X2,k1_tmap_1(X1,X2,X3,X4,X5,X6),k1_tmap_1(X1,X2,X4,X3,X6,X5)) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t8_tmap_1])).

cnf(c_0_19,plain,
    ( k1_tmap_1(X1,X2,X3,X4,X5,X6) = k1_tmap_1(X1,X2,X4,X3,X7,X5)
    | v1_xboole_0(X1)
    | v1_xboole_0(X4)
    | v1_xboole_0(X3)
    | v1_xboole_0(X2)
    | k2_partfun1(X4,X2,X7,k9_subset_1(X1,X4,X3)) != k2_partfun1(X3,X2,X5,k9_subset_1(X1,X4,X3))
    | k2_partfun1(X3,X2,X5,k9_subset_1(X1,X3,X4)) != k2_partfun1(X4,X2,X6,k9_subset_1(X1,X3,X4))
    | k2_partfun1(k4_subset_1(X1,X3,X4),X2,k1_tmap_1(X1,X2,X3,X4,X5,X6),X4) != X7
    | ~ v1_funct_2(X5,X3,X2)
    | ~ v1_funct_2(X7,X4,X2)
    | ~ v1_funct_2(X6,X4,X2)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_1(X7)
    | ~ v1_funct_1(X6)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X1)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16])]),c_0_12]),c_0_13]),c_0_14])).

cnf(c_0_20,plain,
    ( k2_partfun1(k4_subset_1(X1,X2,X3),X4,k1_tmap_1(X1,X4,X2,X3,X5,X6),X3) = X6
    | v1_xboole_0(X4)
    | v1_xboole_0(X3)
    | v1_xboole_0(X2)
    | v1_xboole_0(X1)
    | k2_partfun1(X2,X4,X5,k9_subset_1(X1,X2,X3)) != k2_partfun1(X3,X4,X6,k9_subset_1(X1,X2,X3))
    | ~ v1_funct_2(X5,X2,X4)
    | ~ v1_funct_2(X6,X3,X4)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_1(X6)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_17]),c_0_12]),c_0_13]),c_0_14])).

fof(c_0_21,negated_conjecture,
    ( ~ v1_xboole_0(esk1_0)
    & ~ v1_xboole_0(esk2_0)
    & ~ v1_xboole_0(esk3_0)
    & m1_subset_1(esk3_0,k1_zfmisc_1(esk1_0))
    & ~ v1_xboole_0(esk4_0)
    & m1_subset_1(esk4_0,k1_zfmisc_1(esk1_0))
    & v1_funct_1(esk5_0)
    & v1_funct_2(esk5_0,esk3_0,esk2_0)
    & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0)))
    & v1_funct_1(esk6_0)
    & v1_funct_2(esk6_0,esk4_0,esk2_0)
    & m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk2_0)))
    & k2_partfun1(esk3_0,esk2_0,esk5_0,k9_subset_1(esk1_0,esk3_0,esk4_0)) = k2_partfun1(esk4_0,esk2_0,esk6_0,k9_subset_1(esk1_0,esk3_0,esk4_0))
    & ~ r1_funct_2(k4_subset_1(esk1_0,esk3_0,esk4_0),esk2_0,k4_subset_1(esk1_0,esk4_0,esk3_0),esk2_0,k1_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k1_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk6_0,esk5_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_18])])])])).

cnf(c_0_22,plain,
    ( k1_tmap_1(X1,X2,X3,X4,X5,X6) = k1_tmap_1(X1,X2,X4,X3,X6,X5)
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | v1_xboole_0(X4)
    | v1_xboole_0(X1)
    | k2_partfun1(X4,X2,X6,k9_subset_1(X1,X4,X3)) != k2_partfun1(X3,X2,X5,k9_subset_1(X1,X4,X3))
    | k2_partfun1(X3,X2,X5,k9_subset_1(X1,X3,X4)) != k2_partfun1(X4,X2,X6,k9_subset_1(X1,X3,X4))
    | ~ v1_funct_2(X5,X3,X2)
    | ~ v1_funct_2(X6,X4,X2)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_1(X6)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X1)) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20])])).

cnf(c_0_23,negated_conjecture,
    ( k2_partfun1(esk3_0,esk2_0,esk5_0,k9_subset_1(esk1_0,esk3_0,esk4_0)) = k2_partfun1(esk4_0,esk2_0,esk6_0,k9_subset_1(esk1_0,esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_24,negated_conjecture,
    ( v1_funct_2(esk6_0,esk4_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_25,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_30,negated_conjecture,
    ( ~ v1_xboole_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_31,negated_conjecture,
    ( ~ v1_xboole_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_32,negated_conjecture,
    ( ~ v1_xboole_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_33,plain,(
    ! [X23,X24,X25] :
      ( ~ m1_subset_1(X25,k1_zfmisc_1(X23))
      | k9_subset_1(X23,X24,X25) = k9_subset_1(X23,X25,X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[commutativity_k9_subset_1])])).

cnf(c_0_34,negated_conjecture,
    ( k1_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk6_0,X1) = k1_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,X1,esk6_0)
    | k2_partfun1(esk3_0,esk2_0,X1,k9_subset_1(esk1_0,esk3_0,esk4_0)) != k2_partfun1(esk3_0,esk2_0,esk5_0,k9_subset_1(esk1_0,esk3_0,esk4_0))
    | k2_partfun1(esk4_0,esk2_0,esk6_0,k9_subset_1(esk1_0,esk4_0,esk3_0)) != k2_partfun1(esk3_0,esk2_0,X1,k9_subset_1(esk1_0,esk4_0,esk3_0))
    | ~ v1_funct_2(X1,esk3_0,esk2_0)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24]),c_0_25]),c_0_26]),c_0_27]),c_0_28])]),c_0_29]),c_0_30]),c_0_31]),c_0_32])).

cnf(c_0_35,plain,
    ( k9_subset_1(X2,X3,X1) = k9_subset_1(X2,X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_36,negated_conjecture,
    ( ~ r1_funct_2(k4_subset_1(esk1_0,esk3_0,esk4_0),esk2_0,k4_subset_1(esk1_0,esk4_0,esk3_0),esk2_0,k1_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k1_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk6_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_37,negated_conjecture,
    ( k1_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk6_0,X1) = k1_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,X1,esk6_0)
    | k2_partfun1(esk3_0,esk2_0,X1,k9_subset_1(esk1_0,esk3_0,esk4_0)) != k2_partfun1(esk3_0,esk2_0,esk5_0,k9_subset_1(esk1_0,esk3_0,esk4_0))
    | ~ v1_funct_2(X1,esk3_0,esk2_0)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_23]),c_0_27])])).

cnf(c_0_38,negated_conjecture,
    ( v1_funct_2(esk5_0,esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_39,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_40,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_41,plain,(
    ! [X71,X72,X73,X74,X75,X76] :
      ( ( ~ r1_funct_2(X71,X72,X73,X74,X75,X76)
        | X75 = X76
        | v1_xboole_0(X72)
        | v1_xboole_0(X74)
        | ~ v1_funct_1(X75)
        | ~ v1_funct_2(X75,X71,X72)
        | ~ m1_subset_1(X75,k1_zfmisc_1(k2_zfmisc_1(X71,X72)))
        | ~ v1_funct_1(X76)
        | ~ v1_funct_2(X76,X73,X74)
        | ~ m1_subset_1(X76,k1_zfmisc_1(k2_zfmisc_1(X73,X74))) )
      & ( X75 != X76
        | r1_funct_2(X71,X72,X73,X74,X75,X76)
        | v1_xboole_0(X72)
        | v1_xboole_0(X74)
        | ~ v1_funct_1(X75)
        | ~ v1_funct_2(X75,X71,X72)
        | ~ m1_subset_1(X75,k1_zfmisc_1(k2_zfmisc_1(X71,X72)))
        | ~ v1_funct_1(X76)
        | ~ v1_funct_2(X76,X73,X74)
        | ~ m1_subset_1(X76,k1_zfmisc_1(k2_zfmisc_1(X73,X74))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r1_funct_2])])])])).

cnf(c_0_42,negated_conjecture,
    ( ~ r1_funct_2(k4_subset_1(esk1_0,esk3_0,esk4_0),esk2_0,k4_subset_1(esk1_0,esk3_0,esk4_0),esk2_0,k1_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k1_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk6_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_10]),c_0_27]),c_0_28])])).

cnf(c_0_43,negated_conjecture,
    ( k1_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk6_0,esk5_0) = k1_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_37]),c_0_38]),c_0_39]),c_0_40])])).

cnf(c_0_44,plain,
    ( r1_funct_2(X3,X4,X5,X6,X1,X2)
    | v1_xboole_0(X4)
    | v1_xboole_0(X6)
    | X1 != X2
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X3,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X5,X6)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_45,negated_conjecture,
    ( ~ r1_funct_2(k4_subset_1(esk1_0,esk3_0,esk4_0),esk2_0,k4_subset_1(esk1_0,esk3_0,esk4_0),esk2_0,k1_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k1_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)) ),
    inference(rw,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_46,plain,
    ( r1_funct_2(X1,X2,X3,X4,X5,X5)
    | v1_xboole_0(X4)
    | v1_xboole_0(X2)
    | ~ v1_funct_2(X5,X3,X4)
    | ~ v1_funct_2(X5,X1,X2)
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(er,[status(thm)],[c_0_44])).

cnf(c_0_47,negated_conjecture,
    ( v1_funct_1(k1_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_43]),c_0_38]),c_0_24]),c_0_39]),c_0_25]),c_0_40]),c_0_26]),c_0_28]),c_0_27])]),c_0_32]),c_0_29]),c_0_30]),c_0_31])).

cnf(c_0_48,negated_conjecture,
    ( ~ v1_funct_2(k1_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k4_subset_1(esk1_0,esk3_0,esk4_0),esk2_0)
    | ~ m1_subset_1(k1_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(esk1_0,esk3_0,esk4_0),esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_29]),c_0_47])])).

cnf(c_0_49,negated_conjecture,
    ( ~ v1_funct_2(k1_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k4_subset_1(esk1_0,esk3_0,esk4_0),esk2_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_12]),c_0_24]),c_0_38]),c_0_25]),c_0_39]),c_0_26]),c_0_40]),c_0_27]),c_0_28])]),c_0_32]),c_0_29]),c_0_31]),c_0_30])).

cnf(c_0_50,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_14]),c_0_24]),c_0_38]),c_0_25]),c_0_39]),c_0_26]),c_0_40]),c_0_27]),c_0_28])]),c_0_32]),c_0_29]),c_0_31]),c_0_30]),
    [proof]).
%------------------------------------------------------------------------------
