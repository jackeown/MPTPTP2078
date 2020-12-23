%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:07:06 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 251 expanded)
%              Number of clauses        :   51 (  88 expanded)
%              Number of leaves         :    5 (  65 expanded)
%              Depth                    :   13
%              Number of atoms          :  453 (3139 expanded)
%              Number of equality atoms :   87 ( 574 expanded)
%              Maximal formula depth    :   21 (   7 average)
%              Maximal clause size      :   70 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t132_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ( ( X2 = k1_xboole_0
            & X1 != k1_xboole_0 )
          | v1_partfun1(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_funct_2)).

fof(t148_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ~ ( ( X2 = k1_xboole_0
           => X1 = k1_xboole_0 )
          & ! [X4] :
              ( ( v1_funct_1(X4)
                & v1_funct_2(X4,X1,X2)
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
             => ~ r1_partfun1(X3,X4) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_funct_2)).

fof(t154_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X4] :
          ( ( v1_funct_1(X4)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
         => ~ ( ( X2 = k1_xboole_0
               => X1 = k1_xboole_0 )
              & r1_partfun1(X3,X4)
              & ! [X5] :
                  ( ( v1_funct_1(X5)
                    & v1_funct_2(X5,X1,X2)
                    & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
                 => ~ ( r1_partfun1(X3,X5)
                      & r1_partfun1(X4,X5) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_funct_2)).

fof(t148_partfun1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X4] :
          ( ( v1_funct_1(X4)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
         => ( ( v1_partfun1(X3,X1)
              & v1_partfun1(X4,X1)
              & r1_partfun1(X3,X4) )
           => X3 = X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_partfun1)).

fof(t162_partfun1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X4] :
          ( ( v1_funct_1(X4)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
         => ~ ( ( X2 = k1_xboole_0
               => X1 = k1_xboole_0 )
              & r1_partfun1(X3,X4)
              & ! [X5] :
                  ( ( v1_funct_1(X5)
                    & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
                 => ~ ( v1_partfun1(X5,X1)
                      & r1_partfun1(X3,X5)
                      & r1_partfun1(X4,X5) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_partfun1)).

fof(c_0_5,plain,(
    ! [X6,X7,X8] :
      ( ( X7 = k1_xboole_0
        | v1_partfun1(X8,X6)
        | ~ v1_funct_1(X8)
        | ~ v1_funct_2(X8,X6,X7)
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
        | ~ v1_funct_1(X8)
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) )
      & ( X6 != k1_xboole_0
        | v1_partfun1(X8,X6)
        | ~ v1_funct_1(X8)
        | ~ v1_funct_2(X8,X6,X7)
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
        | ~ v1_funct_1(X8)
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t132_funct_2])])])).

cnf(c_0_6,plain,
    ( X1 = k1_xboole_0
    | v1_partfun1(X2,X3)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X3,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_7,plain,(
    ! [X9,X10,X11] :
      ( ( v1_funct_1(esk1_3(X9,X10,X11))
        | X10 = k1_xboole_0
        | ~ v1_funct_1(X11)
        | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X9,X10))) )
      & ( v1_funct_2(esk1_3(X9,X10,X11),X9,X10)
        | X10 = k1_xboole_0
        | ~ v1_funct_1(X11)
        | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X9,X10))) )
      & ( m1_subset_1(esk1_3(X9,X10,X11),k1_zfmisc_1(k2_zfmisc_1(X9,X10)))
        | X10 = k1_xboole_0
        | ~ v1_funct_1(X11)
        | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X9,X10))) )
      & ( r1_partfun1(X11,esk1_3(X9,X10,X11))
        | X10 = k1_xboole_0
        | ~ v1_funct_1(X11)
        | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X9,X10))) )
      & ( v1_funct_1(esk1_3(X9,X10,X11))
        | X9 != k1_xboole_0
        | ~ v1_funct_1(X11)
        | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X9,X10))) )
      & ( v1_funct_2(esk1_3(X9,X10,X11),X9,X10)
        | X9 != k1_xboole_0
        | ~ v1_funct_1(X11)
        | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X9,X10))) )
      & ( m1_subset_1(esk1_3(X9,X10,X11),k1_zfmisc_1(k2_zfmisc_1(X9,X10)))
        | X9 != k1_xboole_0
        | ~ v1_funct_1(X11)
        | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X9,X10))) )
      & ( r1_partfun1(X11,esk1_3(X9,X10,X11))
        | X9 != k1_xboole_0
        | ~ v1_funct_1(X11)
        | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X9,X10))) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t148_funct_2])])])])])).

cnf(c_0_8,plain,
    ( v1_partfun1(X2,X1)
    | X1 != k1_xboole_0
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X1,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_funct_1(X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ! [X4] :
            ( ( v1_funct_1(X4)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
           => ~ ( ( X2 = k1_xboole_0
                 => X1 = k1_xboole_0 )
                & r1_partfun1(X3,X4)
                & ! [X5] :
                    ( ( v1_funct_1(X5)
                      & v1_funct_2(X5,X1,X2)
                      & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
                   => ~ ( r1_partfun1(X3,X5)
                        & r1_partfun1(X4,X5) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t154_funct_2])).

fof(c_0_10,plain,(
    ! [X13,X14,X15,X16] :
      ( ~ v1_funct_1(X15)
      | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14)))
      | ~ v1_funct_1(X16)
      | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X13,X14)))
      | ~ v1_partfun1(X15,X13)
      | ~ v1_partfun1(X16,X13)
      | ~ r1_partfun1(X15,X16)
      | X15 = X16 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_partfun1])])])).

cnf(c_0_11,plain,
    ( X1 = k1_xboole_0
    | v1_partfun1(X2,X3)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X3,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(cn,[status(thm)],[c_0_6])).

cnf(c_0_12,plain,
    ( v1_funct_2(esk1_3(X1,X2,X3),X1,X2)
    | X2 = k1_xboole_0
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,plain,
    ( v1_funct_1(esk1_3(X1,X2,X3))
    | X2 = k1_xboole_0
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_14,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X2 = k1_xboole_0
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_15,plain,
    ( v1_partfun1(X2,X1)
    | X1 != k1_xboole_0
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X1,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ),
    inference(cn,[status(thm)],[c_0_8])).

cnf(c_0_16,plain,
    ( v1_funct_2(esk1_3(X1,X2,X3),X1,X2)
    | X1 != k1_xboole_0
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_17,plain,
    ( v1_funct_1(esk1_3(X1,X2,X3))
    | X1 != k1_xboole_0
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_18,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X1 != k1_xboole_0
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_19,negated_conjecture,(
    ! [X26] :
      ( v1_funct_1(esk5_0)
      & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0)))
      & v1_funct_1(esk6_0)
      & m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0)))
      & ( esk4_0 != k1_xboole_0
        | esk3_0 = k1_xboole_0 )
      & r1_partfun1(esk5_0,esk6_0)
      & ( ~ v1_funct_1(X26)
        | ~ v1_funct_2(X26,esk3_0,esk4_0)
        | ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0)))
        | ~ r1_partfun1(esk5_0,X26)
        | ~ r1_partfun1(esk6_0,X26) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])])).

cnf(c_0_20,plain,
    ( X1 = X4
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_partfun1(X1,X2)
    | ~ v1_partfun1(X4,X2)
    | ~ r1_partfun1(X1,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_21,plain,
    ( X1 = k1_xboole_0
    | v1_partfun1(esk1_3(X2,X1,X3),X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X3) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_12]),c_0_13]),c_0_14])).

cnf(c_0_22,plain,
    ( v1_partfun1(esk1_3(X1,X2,X3),X1)
    | X1 != k1_xboole_0
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17]),c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,esk3_0,esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0)))
    | ~ r1_partfun1(esk5_0,X1)
    | ~ r1_partfun1(esk6_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,plain,
    ( X1 = esk1_3(X2,X3,X4)
    | X3 = k1_xboole_0
    | ~ r1_partfun1(X1,esk1_3(X2,X3,X4))
    | ~ v1_partfun1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X4) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_14]),c_0_13]),c_0_21])).

cnf(c_0_25,plain,
    ( r1_partfun1(X1,esk1_3(X2,X3,X1))
    | X3 = k1_xboole_0
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_26,plain,
    ( X1 = esk1_3(X2,X3,X4)
    | X2 != k1_xboole_0
    | ~ r1_partfun1(X1,esk1_3(X2,X3,X4))
    | ~ v1_partfun1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X4) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_18]),c_0_17]),c_0_22])).

cnf(c_0_27,plain,
    ( r1_partfun1(X1,esk1_3(X2,X3,X1))
    | X2 != k1_xboole_0
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_28,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | ~ r1_partfun1(esk5_0,esk1_3(esk3_0,esk4_0,X1))
    | ~ r1_partfun1(esk6_0,esk1_3(esk3_0,esk4_0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0)))
    | ~ v1_funct_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_12]),c_0_13]),c_0_14])).

cnf(c_0_29,plain,
    ( esk1_3(X1,X2,X3) = X3
    | X2 = k1_xboole_0
    | ~ v1_partfun1(X3,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

fof(c_0_30,plain,(
    ! [X17,X18,X19,X20] :
      ( ( v1_funct_1(esk2_4(X17,X18,X19,X20))
        | X18 = k1_xboole_0
        | ~ r1_partfun1(X19,X20)
        | ~ v1_funct_1(X20)
        | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X17,X18)))
        | ~ v1_funct_1(X19)
        | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18))) )
      & ( m1_subset_1(esk2_4(X17,X18,X19,X20),k1_zfmisc_1(k2_zfmisc_1(X17,X18)))
        | X18 = k1_xboole_0
        | ~ r1_partfun1(X19,X20)
        | ~ v1_funct_1(X20)
        | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X17,X18)))
        | ~ v1_funct_1(X19)
        | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18))) )
      & ( v1_partfun1(esk2_4(X17,X18,X19,X20),X17)
        | X18 = k1_xboole_0
        | ~ r1_partfun1(X19,X20)
        | ~ v1_funct_1(X20)
        | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X17,X18)))
        | ~ v1_funct_1(X19)
        | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18))) )
      & ( r1_partfun1(X19,esk2_4(X17,X18,X19,X20))
        | X18 = k1_xboole_0
        | ~ r1_partfun1(X19,X20)
        | ~ v1_funct_1(X20)
        | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X17,X18)))
        | ~ v1_funct_1(X19)
        | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18))) )
      & ( r1_partfun1(X20,esk2_4(X17,X18,X19,X20))
        | X18 = k1_xboole_0
        | ~ r1_partfun1(X19,X20)
        | ~ v1_funct_1(X20)
        | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X17,X18)))
        | ~ v1_funct_1(X19)
        | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18))) )
      & ( v1_funct_1(esk2_4(X17,X18,X19,X20))
        | X17 != k1_xboole_0
        | ~ r1_partfun1(X19,X20)
        | ~ v1_funct_1(X20)
        | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X17,X18)))
        | ~ v1_funct_1(X19)
        | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18))) )
      & ( m1_subset_1(esk2_4(X17,X18,X19,X20),k1_zfmisc_1(k2_zfmisc_1(X17,X18)))
        | X17 != k1_xboole_0
        | ~ r1_partfun1(X19,X20)
        | ~ v1_funct_1(X20)
        | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X17,X18)))
        | ~ v1_funct_1(X19)
        | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18))) )
      & ( v1_partfun1(esk2_4(X17,X18,X19,X20),X17)
        | X17 != k1_xboole_0
        | ~ r1_partfun1(X19,X20)
        | ~ v1_funct_1(X20)
        | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X17,X18)))
        | ~ v1_funct_1(X19)
        | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18))) )
      & ( r1_partfun1(X19,esk2_4(X17,X18,X19,X20))
        | X17 != k1_xboole_0
        | ~ r1_partfun1(X19,X20)
        | ~ v1_funct_1(X20)
        | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X17,X18)))
        | ~ v1_funct_1(X19)
        | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18))) )
      & ( r1_partfun1(X20,esk2_4(X17,X18,X19,X20))
        | X17 != k1_xboole_0
        | ~ r1_partfun1(X19,X20)
        | ~ v1_funct_1(X20)
        | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X17,X18)))
        | ~ v1_funct_1(X19)
        | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t162_partfun1])])])])])).

cnf(c_0_31,negated_conjecture,
    ( esk3_0 != k1_xboole_0
    | ~ r1_partfun1(esk5_0,esk1_3(esk3_0,esk4_0,X1))
    | ~ r1_partfun1(esk6_0,esk1_3(esk3_0,esk4_0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0)))
    | ~ v1_funct_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_16]),c_0_17]),c_0_18])).

cnf(c_0_32,plain,
    ( esk1_3(X1,X2,X3) = X3
    | X1 != k1_xboole_0
    | ~ v1_partfun1(X3,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_33,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | ~ r1_partfun1(esk5_0,X1)
    | ~ r1_partfun1(esk6_0,X1)
    | ~ v1_partfun1(X1,esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0)))
    | ~ v1_funct_1(X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_34,plain,
    ( r1_partfun1(X1,esk2_4(X2,X3,X1,X4))
    | X3 = k1_xboole_0
    | ~ r1_partfun1(X1,X4)
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_35,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_36,negated_conjecture,
    ( esk3_0 != k1_xboole_0
    | ~ r1_partfun1(esk5_0,X1)
    | ~ r1_partfun1(esk6_0,X1)
    | ~ v1_partfun1(X1,esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0)))
    | ~ v1_funct_1(X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_37,plain,
    ( r1_partfun1(X1,esk2_4(X2,X3,X1,X4))
    | X2 != k1_xboole_0
    | ~ r1_partfun1(X1,X4)
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_38,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | X1 = k1_xboole_0
    | ~ r1_partfun1(esk6_0,esk2_4(X2,X1,esk5_0,X3))
    | ~ r1_partfun1(esk5_0,X3)
    | ~ v1_partfun1(esk2_4(X2,X1,esk5_0,X3),esk3_0)
    | ~ m1_subset_1(esk2_4(X2,X1,esk5_0,X3),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0)))
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(esk2_4(X2,X1,esk5_0,X3))
    | ~ v1_funct_1(X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35])])).

cnf(c_0_39,plain,
    ( v1_partfun1(esk2_4(X1,X2,X3,X4),X1)
    | X2 = k1_xboole_0
    | ~ r1_partfun1(X3,X4)
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_40,negated_conjecture,
    ( esk3_0 != k1_xboole_0
    | X1 != k1_xboole_0
    | ~ r1_partfun1(esk6_0,esk2_4(X1,X2,esk5_0,X3))
    | ~ r1_partfun1(esk5_0,X3)
    | ~ v1_partfun1(esk2_4(X1,X2,esk5_0,X3),esk3_0)
    | ~ m1_subset_1(esk2_4(X1,X2,esk5_0,X3),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0)))
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(esk2_4(X1,X2,esk5_0,X3))
    | ~ v1_funct_1(X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_35])])).

cnf(c_0_41,plain,
    ( v1_partfun1(esk2_4(X1,X2,X3,X4),X1)
    | X1 != k1_xboole_0
    | ~ r1_partfun1(X3,X4)
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_42,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | X1 = k1_xboole_0
    | ~ r1_partfun1(esk6_0,esk2_4(esk3_0,X1,esk5_0,X2))
    | ~ r1_partfun1(esk5_0,X2)
    | ~ m1_subset_1(esk2_4(esk3_0,X1,esk5_0,X2),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0)))
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(esk3_0,X1)))
    | ~ v1_funct_1(esk2_4(esk3_0,X1,esk5_0,X2))
    | ~ v1_funct_1(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_35])])).

cnf(c_0_43,plain,
    ( r1_partfun1(X1,esk2_4(X2,X3,X4,X1))
    | X3 = k1_xboole_0
    | ~ r1_partfun1(X4,X1)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_44,negated_conjecture,
    ( r1_partfun1(esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_45,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_46,negated_conjecture,
    ( esk3_0 != k1_xboole_0
    | ~ r1_partfun1(esk6_0,esk2_4(esk3_0,X1,esk5_0,X2))
    | ~ r1_partfun1(esk5_0,X2)
    | ~ m1_subset_1(esk2_4(esk3_0,X1,esk5_0,X2),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0)))
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(esk3_0,X1)))
    | ~ v1_funct_1(esk2_4(esk3_0,X1,esk5_0,X2))
    | ~ v1_funct_1(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_35])])).

cnf(c_0_47,plain,
    ( r1_partfun1(X1,esk2_4(X2,X3,X4,X1))
    | X2 != k1_xboole_0
    | ~ r1_partfun1(X4,X1)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_48,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | X1 = k1_xboole_0
    | ~ m1_subset_1(esk2_4(esk3_0,X1,esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0)))
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,X1)))
    | ~ m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,X1)))
    | ~ v1_funct_1(esk2_4(esk3_0,X1,esk5_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_44]),c_0_45]),c_0_35])])).

cnf(c_0_49,plain,
    ( m1_subset_1(esk2_4(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X2 = k1_xboole_0
    | ~ r1_partfun1(X3,X4)
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_50,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_51,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_52,negated_conjecture,
    ( esk3_0 != k1_xboole_0
    | ~ m1_subset_1(esk2_4(esk3_0,X1,esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0)))
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,X1)))
    | ~ m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,X1)))
    | ~ v1_funct_1(esk2_4(esk3_0,X1,esk5_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_44]),c_0_45]),c_0_35])])).

cnf(c_0_53,plain,
    ( m1_subset_1(esk2_4(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X1 != k1_xboole_0
    | ~ r1_partfun1(X3,X4)
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_54,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | ~ v1_funct_1(esk2_4(esk3_0,esk4_0,esk5_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_50]),c_0_51]),c_0_44]),c_0_45]),c_0_35])])).

cnf(c_0_55,plain,
    ( v1_funct_1(esk2_4(X1,X2,X3,X4))
    | X2 = k1_xboole_0
    | ~ r1_partfun1(X3,X4)
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_56,negated_conjecture,
    ( esk3_0 != k1_xboole_0
    | ~ v1_funct_1(esk2_4(esk3_0,esk4_0,esk5_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_50]),c_0_51]),c_0_44]),c_0_45]),c_0_35])])).

cnf(c_0_57,plain,
    ( v1_funct_1(esk2_4(X1,X2,X3,X4))
    | X1 != k1_xboole_0
    | ~ r1_partfun1(X3,X4)
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_58,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | esk4_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_59,negated_conjecture,
    ( esk4_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_44]),c_0_51]),c_0_50]),c_0_45]),c_0_35])])).

cnf(c_0_60,negated_conjecture,
    ( esk3_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_44]),c_0_51]),c_0_50]),c_0_45]),c_0_35])])).

cnf(c_0_61,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_58,c_0_59])]),c_0_60]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:08:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic G_E___207_B07_F1_AE_CS_SP_PI_PS_S0Y
% 0.13/0.38  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.019 s
% 0.13/0.38  # Presaturation interreduction done
% 0.13/0.38  
% 0.13/0.38  # Proof found!
% 0.13/0.38  # SZS status Theorem
% 0.13/0.38  # SZS output start CNFRefutation
% 0.13/0.38  fof(t132_funct_2, axiom, ![X1, X2, X3]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((X2=k1_xboole_0&X1!=k1_xboole_0)|v1_partfun1(X3,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t132_funct_2)).
% 0.13/0.38  fof(t148_funct_2, axiom, ![X1, X2, X3]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>~(((X2=k1_xboole_0=>X1=k1_xboole_0)&![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>~(r1_partfun1(X3,X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_funct_2)).
% 0.13/0.38  fof(t154_funct_2, conjecture, ![X1, X2, X3]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:((v1_funct_1(X4)&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>~((((X2=k1_xboole_0=>X1=k1_xboole_0)&r1_partfun1(X3,X4))&![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,X1,X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>~((r1_partfun1(X3,X5)&r1_partfun1(X4,X5)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t154_funct_2)).
% 0.13/0.38  fof(t148_partfun1, axiom, ![X1, X2, X3]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:((v1_funct_1(X4)&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(((v1_partfun1(X3,X1)&v1_partfun1(X4,X1))&r1_partfun1(X3,X4))=>X3=X4))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_partfun1)).
% 0.13/0.38  fof(t162_partfun1, axiom, ![X1, X2, X3]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:((v1_funct_1(X4)&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>~((((X2=k1_xboole_0=>X1=k1_xboole_0)&r1_partfun1(X3,X4))&![X5]:((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>~(((v1_partfun1(X5,X1)&r1_partfun1(X3,X5))&r1_partfun1(X4,X5)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t162_partfun1)).
% 0.13/0.38  fof(c_0_5, plain, ![X6, X7, X8]:((X7=k1_xboole_0|v1_partfun1(X8,X6)|(~v1_funct_1(X8)|~v1_funct_2(X8,X6,X7)|~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X7))))|(~v1_funct_1(X8)|~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))))&(X6!=k1_xboole_0|v1_partfun1(X8,X6)|(~v1_funct_1(X8)|~v1_funct_2(X8,X6,X7)|~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X7))))|(~v1_funct_1(X8)|~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t132_funct_2])])])).
% 0.13/0.38  cnf(c_0_6, plain, (X1=k1_xboole_0|v1_partfun1(X2,X3)|~v1_funct_1(X2)|~v1_funct_2(X2,X3,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.38  fof(c_0_7, plain, ![X9, X10, X11]:(((((v1_funct_1(esk1_3(X9,X10,X11))|X10=k1_xboole_0|(~v1_funct_1(X11)|~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))))&(v1_funct_2(esk1_3(X9,X10,X11),X9,X10)|X10=k1_xboole_0|(~v1_funct_1(X11)|~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X9,X10))))))&(m1_subset_1(esk1_3(X9,X10,X11),k1_zfmisc_1(k2_zfmisc_1(X9,X10)))|X10=k1_xboole_0|(~v1_funct_1(X11)|~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X9,X10))))))&(r1_partfun1(X11,esk1_3(X9,X10,X11))|X10=k1_xboole_0|(~v1_funct_1(X11)|~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X9,X10))))))&((((v1_funct_1(esk1_3(X9,X10,X11))|X9!=k1_xboole_0|(~v1_funct_1(X11)|~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))))&(v1_funct_2(esk1_3(X9,X10,X11),X9,X10)|X9!=k1_xboole_0|(~v1_funct_1(X11)|~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X9,X10))))))&(m1_subset_1(esk1_3(X9,X10,X11),k1_zfmisc_1(k2_zfmisc_1(X9,X10)))|X9!=k1_xboole_0|(~v1_funct_1(X11)|~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X9,X10))))))&(r1_partfun1(X11,esk1_3(X9,X10,X11))|X9!=k1_xboole_0|(~v1_funct_1(X11)|~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X9,X10))))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t148_funct_2])])])])])).
% 0.13/0.38  cnf(c_0_8, plain, (v1_partfun1(X2,X1)|X1!=k1_xboole_0|~v1_funct_1(X2)|~v1_funct_2(X2,X1,X3)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.38  fof(c_0_9, negated_conjecture, ~(![X1, X2, X3]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:((v1_funct_1(X4)&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>~((((X2=k1_xboole_0=>X1=k1_xboole_0)&r1_partfun1(X3,X4))&![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,X1,X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>~((r1_partfun1(X3,X5)&r1_partfun1(X4,X5))))))))), inference(assume_negation,[status(cth)],[t154_funct_2])).
% 0.13/0.38  fof(c_0_10, plain, ![X13, X14, X15, X16]:(~v1_funct_1(X15)|~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14)))|(~v1_funct_1(X16)|~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X13,X14)))|(~v1_partfun1(X15,X13)|~v1_partfun1(X16,X13)|~r1_partfun1(X15,X16)|X15=X16))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_partfun1])])])).
% 0.13/0.38  cnf(c_0_11, plain, (X1=k1_xboole_0|v1_partfun1(X2,X3)|~v1_funct_1(X2)|~v1_funct_2(X2,X3,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))), inference(cn,[status(thm)],[c_0_6])).
% 0.13/0.38  cnf(c_0_12, plain, (v1_funct_2(esk1_3(X1,X2,X3),X1,X2)|X2=k1_xboole_0|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.38  cnf(c_0_13, plain, (v1_funct_1(esk1_3(X1,X2,X3))|X2=k1_xboole_0|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.38  cnf(c_0_14, plain, (m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|X2=k1_xboole_0|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.38  cnf(c_0_15, plain, (v1_partfun1(X2,X1)|X1!=k1_xboole_0|~v1_funct_1(X2)|~v1_funct_2(X2,X1,X3)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))), inference(cn,[status(thm)],[c_0_8])).
% 0.13/0.38  cnf(c_0_16, plain, (v1_funct_2(esk1_3(X1,X2,X3),X1,X2)|X1!=k1_xboole_0|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.38  cnf(c_0_17, plain, (v1_funct_1(esk1_3(X1,X2,X3))|X1!=k1_xboole_0|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.38  cnf(c_0_18, plain, (m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|X1!=k1_xboole_0|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.38  fof(c_0_19, negated_conjecture, ![X26]:((v1_funct_1(esk5_0)&m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0))))&((v1_funct_1(esk6_0)&m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0))))&(((esk4_0!=k1_xboole_0|esk3_0=k1_xboole_0)&r1_partfun1(esk5_0,esk6_0))&(~v1_funct_1(X26)|~v1_funct_2(X26,esk3_0,esk4_0)|~m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0)))|(~r1_partfun1(esk5_0,X26)|~r1_partfun1(esk6_0,X26)))))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])])).
% 0.13/0.38  cnf(c_0_20, plain, (X1=X4|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_partfun1(X1,X2)|~v1_partfun1(X4,X2)|~r1_partfun1(X1,X4)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.38  cnf(c_0_21, plain, (X1=k1_xboole_0|v1_partfun1(esk1_3(X2,X1,X3),X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))|~v1_funct_1(X3)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_12]), c_0_13]), c_0_14])).
% 0.13/0.38  cnf(c_0_22, plain, (v1_partfun1(esk1_3(X1,X2,X3),X1)|X1!=k1_xboole_0|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X3)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_17]), c_0_18])).
% 0.13/0.38  cnf(c_0_23, negated_conjecture, (~v1_funct_1(X1)|~v1_funct_2(X1,esk3_0,esk4_0)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0)))|~r1_partfun1(esk5_0,X1)|~r1_partfun1(esk6_0,X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.38  cnf(c_0_24, plain, (X1=esk1_3(X2,X3,X4)|X3=k1_xboole_0|~r1_partfun1(X1,esk1_3(X2,X3,X4))|~v1_partfun1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_funct_1(X1)|~v1_funct_1(X4)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_14]), c_0_13]), c_0_21])).
% 0.13/0.38  cnf(c_0_25, plain, (r1_partfun1(X1,esk1_3(X2,X3,X1))|X3=k1_xboole_0|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.38  cnf(c_0_26, plain, (X1=esk1_3(X2,X3,X4)|X2!=k1_xboole_0|~r1_partfun1(X1,esk1_3(X2,X3,X4))|~v1_partfun1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_funct_1(X1)|~v1_funct_1(X4)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_18]), c_0_17]), c_0_22])).
% 0.13/0.38  cnf(c_0_27, plain, (r1_partfun1(X1,esk1_3(X2,X3,X1))|X2!=k1_xboole_0|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.38  cnf(c_0_28, negated_conjecture, (esk4_0=k1_xboole_0|~r1_partfun1(esk5_0,esk1_3(esk3_0,esk4_0,X1))|~r1_partfun1(esk6_0,esk1_3(esk3_0,esk4_0,X1))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0)))|~v1_funct_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_12]), c_0_13]), c_0_14])).
% 0.13/0.38  cnf(c_0_29, plain, (esk1_3(X1,X2,X3)=X3|X2=k1_xboole_0|~v1_partfun1(X3,X1)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X3)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.13/0.38  fof(c_0_30, plain, ![X17, X18, X19, X20]:((((v1_funct_1(esk2_4(X17,X18,X19,X20))|(X18=k1_xboole_0|~r1_partfun1(X19,X20))|(~v1_funct_1(X20)|~m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X17,X18))))|(~v1_funct_1(X19)|~m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18)))))&(m1_subset_1(esk2_4(X17,X18,X19,X20),k1_zfmisc_1(k2_zfmisc_1(X17,X18)))|(X18=k1_xboole_0|~r1_partfun1(X19,X20))|(~v1_funct_1(X20)|~m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X17,X18))))|(~v1_funct_1(X19)|~m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18))))))&(((v1_partfun1(esk2_4(X17,X18,X19,X20),X17)|(X18=k1_xboole_0|~r1_partfun1(X19,X20))|(~v1_funct_1(X20)|~m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X17,X18))))|(~v1_funct_1(X19)|~m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18)))))&(r1_partfun1(X19,esk2_4(X17,X18,X19,X20))|(X18=k1_xboole_0|~r1_partfun1(X19,X20))|(~v1_funct_1(X20)|~m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X17,X18))))|(~v1_funct_1(X19)|~m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18))))))&(r1_partfun1(X20,esk2_4(X17,X18,X19,X20))|(X18=k1_xboole_0|~r1_partfun1(X19,X20))|(~v1_funct_1(X20)|~m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X17,X18))))|(~v1_funct_1(X19)|~m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18)))))))&(((v1_funct_1(esk2_4(X17,X18,X19,X20))|(X17!=k1_xboole_0|~r1_partfun1(X19,X20))|(~v1_funct_1(X20)|~m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X17,X18))))|(~v1_funct_1(X19)|~m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18)))))&(m1_subset_1(esk2_4(X17,X18,X19,X20),k1_zfmisc_1(k2_zfmisc_1(X17,X18)))|(X17!=k1_xboole_0|~r1_partfun1(X19,X20))|(~v1_funct_1(X20)|~m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X17,X18))))|(~v1_funct_1(X19)|~m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18))))))&(((v1_partfun1(esk2_4(X17,X18,X19,X20),X17)|(X17!=k1_xboole_0|~r1_partfun1(X19,X20))|(~v1_funct_1(X20)|~m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X17,X18))))|(~v1_funct_1(X19)|~m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18)))))&(r1_partfun1(X19,esk2_4(X17,X18,X19,X20))|(X17!=k1_xboole_0|~r1_partfun1(X19,X20))|(~v1_funct_1(X20)|~m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X17,X18))))|(~v1_funct_1(X19)|~m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18))))))&(r1_partfun1(X20,esk2_4(X17,X18,X19,X20))|(X17!=k1_xboole_0|~r1_partfun1(X19,X20))|(~v1_funct_1(X20)|~m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X17,X18))))|(~v1_funct_1(X19)|~m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18)))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t162_partfun1])])])])])).
% 0.13/0.38  cnf(c_0_31, negated_conjecture, (esk3_0!=k1_xboole_0|~r1_partfun1(esk5_0,esk1_3(esk3_0,esk4_0,X1))|~r1_partfun1(esk6_0,esk1_3(esk3_0,esk4_0,X1))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0)))|~v1_funct_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_16]), c_0_17]), c_0_18])).
% 0.13/0.38  cnf(c_0_32, plain, (esk1_3(X1,X2,X3)=X3|X1!=k1_xboole_0|~v1_partfun1(X3,X1)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X3)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.13/0.38  cnf(c_0_33, negated_conjecture, (esk4_0=k1_xboole_0|~r1_partfun1(esk5_0,X1)|~r1_partfun1(esk6_0,X1)|~v1_partfun1(X1,esk3_0)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0)))|~v1_funct_1(X1)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.13/0.38  cnf(c_0_34, plain, (r1_partfun1(X1,esk2_4(X2,X3,X1,X4))|X3=k1_xboole_0|~r1_partfun1(X1,X4)|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.13/0.38  cnf(c_0_35, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.38  cnf(c_0_36, negated_conjecture, (esk3_0!=k1_xboole_0|~r1_partfun1(esk5_0,X1)|~r1_partfun1(esk6_0,X1)|~v1_partfun1(X1,esk3_0)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0)))|~v1_funct_1(X1)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.13/0.38  cnf(c_0_37, plain, (r1_partfun1(X1,esk2_4(X2,X3,X1,X4))|X2!=k1_xboole_0|~r1_partfun1(X1,X4)|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.13/0.38  cnf(c_0_38, negated_conjecture, (esk4_0=k1_xboole_0|X1=k1_xboole_0|~r1_partfun1(esk6_0,esk2_4(X2,X1,esk5_0,X3))|~r1_partfun1(esk5_0,X3)|~v1_partfun1(esk2_4(X2,X1,esk5_0,X3),esk3_0)|~m1_subset_1(esk2_4(X2,X1,esk5_0,X3),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0)))|~m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))|~v1_funct_1(esk2_4(X2,X1,esk5_0,X3))|~v1_funct_1(X3)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35])])).
% 0.13/0.38  cnf(c_0_39, plain, (v1_partfun1(esk2_4(X1,X2,X3,X4),X1)|X2=k1_xboole_0|~r1_partfun1(X3,X4)|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.13/0.38  cnf(c_0_40, negated_conjecture, (esk3_0!=k1_xboole_0|X1!=k1_xboole_0|~r1_partfun1(esk6_0,esk2_4(X1,X2,esk5_0,X3))|~r1_partfun1(esk5_0,X3)|~v1_partfun1(esk2_4(X1,X2,esk5_0,X3),esk3_0)|~m1_subset_1(esk2_4(X1,X2,esk5_0,X3),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0)))|~m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(esk2_4(X1,X2,esk5_0,X3))|~v1_funct_1(X3)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_35])])).
% 0.13/0.38  cnf(c_0_41, plain, (v1_partfun1(esk2_4(X1,X2,X3,X4),X1)|X1!=k1_xboole_0|~r1_partfun1(X3,X4)|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.13/0.38  cnf(c_0_42, negated_conjecture, (esk4_0=k1_xboole_0|X1=k1_xboole_0|~r1_partfun1(esk6_0,esk2_4(esk3_0,X1,esk5_0,X2))|~r1_partfun1(esk5_0,X2)|~m1_subset_1(esk2_4(esk3_0,X1,esk5_0,X2),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0)))|~m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,X1)))|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(esk3_0,X1)))|~v1_funct_1(esk2_4(esk3_0,X1,esk5_0,X2))|~v1_funct_1(X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_35])])).
% 0.13/0.38  cnf(c_0_43, plain, (r1_partfun1(X1,esk2_4(X2,X3,X4,X1))|X3=k1_xboole_0|~r1_partfun1(X4,X1)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.13/0.38  cnf(c_0_44, negated_conjecture, (r1_partfun1(esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.38  cnf(c_0_45, negated_conjecture, (v1_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.38  cnf(c_0_46, negated_conjecture, (esk3_0!=k1_xboole_0|~r1_partfun1(esk6_0,esk2_4(esk3_0,X1,esk5_0,X2))|~r1_partfun1(esk5_0,X2)|~m1_subset_1(esk2_4(esk3_0,X1,esk5_0,X2),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0)))|~m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,X1)))|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(esk3_0,X1)))|~v1_funct_1(esk2_4(esk3_0,X1,esk5_0,X2))|~v1_funct_1(X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_35])])).
% 0.13/0.38  cnf(c_0_47, plain, (r1_partfun1(X1,esk2_4(X2,X3,X4,X1))|X2!=k1_xboole_0|~r1_partfun1(X4,X1)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.13/0.38  cnf(c_0_48, negated_conjecture, (esk4_0=k1_xboole_0|X1=k1_xboole_0|~m1_subset_1(esk2_4(esk3_0,X1,esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0)))|~m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,X1)))|~m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,X1)))|~v1_funct_1(esk2_4(esk3_0,X1,esk5_0,esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_44]), c_0_45]), c_0_35])])).
% 0.13/0.38  cnf(c_0_49, plain, (m1_subset_1(esk2_4(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|X2=k1_xboole_0|~r1_partfun1(X3,X4)|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.13/0.38  cnf(c_0_50, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.38  cnf(c_0_51, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.38  cnf(c_0_52, negated_conjecture, (esk3_0!=k1_xboole_0|~m1_subset_1(esk2_4(esk3_0,X1,esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0)))|~m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,X1)))|~m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,X1)))|~v1_funct_1(esk2_4(esk3_0,X1,esk5_0,esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_44]), c_0_45]), c_0_35])])).
% 0.13/0.38  cnf(c_0_53, plain, (m1_subset_1(esk2_4(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|X1!=k1_xboole_0|~r1_partfun1(X3,X4)|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.13/0.38  cnf(c_0_54, negated_conjecture, (esk4_0=k1_xboole_0|~v1_funct_1(esk2_4(esk3_0,esk4_0,esk5_0,esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_50]), c_0_51]), c_0_44]), c_0_45]), c_0_35])])).
% 0.13/0.38  cnf(c_0_55, plain, (v1_funct_1(esk2_4(X1,X2,X3,X4))|X2=k1_xboole_0|~r1_partfun1(X3,X4)|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.13/0.38  cnf(c_0_56, negated_conjecture, (esk3_0!=k1_xboole_0|~v1_funct_1(esk2_4(esk3_0,esk4_0,esk5_0,esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_50]), c_0_51]), c_0_44]), c_0_45]), c_0_35])])).
% 0.13/0.38  cnf(c_0_57, plain, (v1_funct_1(esk2_4(X1,X2,X3,X4))|X1!=k1_xboole_0|~r1_partfun1(X3,X4)|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.13/0.38  cnf(c_0_58, negated_conjecture, (esk3_0=k1_xboole_0|esk4_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.38  cnf(c_0_59, negated_conjecture, (esk4_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_44]), c_0_51]), c_0_50]), c_0_45]), c_0_35])])).
% 0.13/0.38  cnf(c_0_60, negated_conjecture, (esk3_0!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_44]), c_0_51]), c_0_50]), c_0_45]), c_0_35])])).
% 0.13/0.38  cnf(c_0_61, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_58, c_0_59])]), c_0_60]), ['proof']).
% 0.13/0.38  # SZS output end CNFRefutation
% 0.13/0.38  # Proof object total steps             : 62
% 0.13/0.38  # Proof object clause steps            : 51
% 0.13/0.38  # Proof object formula steps           : 11
% 0.13/0.38  # Proof object conjectures             : 25
% 0.13/0.38  # Proof object clause conjectures      : 22
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 28
% 0.13/0.38  # Proof object initial formulas used   : 5
% 0.13/0.38  # Proof object generating inferences   : 20
% 0.13/0.38  # Proof object simplifying inferences  : 57
% 0.13/0.38  # Training examples: 0 positive, 0 negative
% 0.13/0.38  # Parsed axioms                        : 5
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 28
% 0.13/0.38  # Removed in clause preprocessing      : 0
% 0.13/0.38  # Initial clauses in saturation        : 28
% 0.13/0.38  # Processed clauses                    : 306
% 0.13/0.38  # ...of these trivial                  : 0
% 0.13/0.38  # ...subsumed                          : 157
% 0.13/0.38  # ...remaining for further processing  : 149
% 0.13/0.38  # Other redundant clauses eliminated   : 0
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 21
% 0.13/0.38  # Backward-rewritten                   : 40
% 0.13/0.38  # Generated clauses                    : 367
% 0.13/0.38  # ...of the previous two non-trivial   : 339
% 0.13/0.38  # Contextual simplify-reflections      : 28
% 0.13/0.38  # Paramodulations                      : 367
% 0.13/0.38  # Factorizations                       : 0
% 0.13/0.38  # Equation resolutions                 : 0
% 0.13/0.38  # Propositional unsat checks           : 0
% 0.13/0.38  #    Propositional check models        : 0
% 0.13/0.38  #    Propositional check unsatisfiable : 0
% 0.13/0.38  #    Propositional clauses             : 0
% 0.13/0.38  #    Propositional clauses after purity: 0
% 0.13/0.38  #    Propositional unsat core size     : 0
% 0.13/0.38  #    Propositional preprocessing time  : 0.000
% 0.13/0.38  #    Propositional encoding time       : 0.000
% 0.13/0.38  #    Propositional solver time         : 0.000
% 0.13/0.38  #    Success case prop preproc time    : 0.000
% 0.13/0.38  #    Success case prop encoding time   : 0.000
% 0.13/0.38  #    Success case prop solver time     : 0.000
% 0.13/0.38  # Current number of processed clauses  : 60
% 0.13/0.38  #    Positive orientable unit clauses  : 4
% 0.13/0.38  #    Positive unorientable unit clauses: 0
% 0.13/0.38  #    Negative unit clauses             : 1
% 0.13/0.38  #    Non-unit-clauses                  : 55
% 0.13/0.38  # Current number of unprocessed clauses: 56
% 0.13/0.38  # ...number of literals in the above   : 485
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 89
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 3547
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 293
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 144
% 0.13/0.38  # Unit Clause-clause subsumption calls : 54
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 1
% 0.13/0.38  # BW rewrite match successes           : 1
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 17402
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.036 s
% 0.13/0.38  # System time              : 0.005 s
% 0.13/0.38  # Total time               : 0.041 s
% 0.13/0.38  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
