%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:07:12 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  104 (18521 expanded)
%              Number of clauses        :   85 (7429 expanded)
%              Number of leaves         :    9 (4807 expanded)
%              Depth                    :   18
%              Number of atoms          :  418 (76772 expanded)
%              Number of equality atoms :   97 (22407 expanded)
%              Maximal formula depth    :   26 (   4 average)
%              Maximal clause size      :   68 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t164_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))) )
     => ! [X4] :
          ( ( v1_funct_1(X4)
            & v1_funct_2(X4,X1,k1_tarski(X2))
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))) )
         => k5_partfun1(X1,k1_tarski(X2),X3) = k1_tarski(X4) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t164_funct_2)).

fof(t143_partfun1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))) )
     => ! [X4] :
          ( ( v1_funct_1(X4)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))) )
         => r1_partfun1(X3,X4) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_partfun1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(d7_partfun1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X4] :
          ( X4 = k5_partfun1(X1,X2,X3)
        <=> ! [X5] :
              ( r2_hidden(X5,X4)
            <=> ? [X6] :
                  ( v1_funct_1(X6)
                  & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                  & X6 = X5
                  & v1_partfun1(X6,X1)
                  & r1_partfun1(X3,X6) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_partfun1)).

fof(t155_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X4] :
          ( ( v1_funct_1(X4)
            & v1_funct_2(X4,X1,X2)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
         => ( r1_partfun1(X3,X4)
           => ( ( X2 = k1_xboole_0
                & X1 != k1_xboole_0 )
              | r2_hidden(X4,k5_partfun1(X1,X2,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t155_funct_2)).

fof(t174_partfun1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( v1_partfun1(X3,X1)
      <=> k5_partfun1(X1,X2,X3) = k1_tarski(X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_partfun1)).

fof(t130_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X1 != k1_xboole_0
     => ( k2_zfmisc_1(k1_tarski(X2),X1) != k1_xboole_0
        & k2_zfmisc_1(X1,k1_tarski(X2)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t130_zfmisc_1)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_funct_1(X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))) )
       => ! [X4] :
            ( ( v1_funct_1(X4)
              & v1_funct_2(X4,X1,k1_tarski(X2))
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))) )
           => k5_partfun1(X1,k1_tarski(X2),X3) = k1_tarski(X4) ) ) ),
    inference(assume_negation,[status(cth)],[t164_funct_2])).

fof(c_0_10,plain,(
    ! [X26,X27,X28,X29] :
      ( ~ v1_funct_1(X28)
      | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,k1_tarski(X27))))
      | ~ v1_funct_1(X29)
      | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X26,k1_tarski(X27))))
      | r1_partfun1(X28,X29) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_partfun1])])])).

fof(c_0_11,plain,(
    ! [X7] : k2_tarski(X7,X7) = k1_tarski(X7) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_12,plain,(
    ! [X8,X9] : k1_enumset1(X8,X8,X9) = k2_tarski(X8,X9) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_13,negated_conjecture,
    ( v1_funct_1(esk6_0)
    & m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,k1_tarski(esk5_0))))
    & v1_funct_1(esk7_0)
    & v1_funct_2(esk7_0,esk4_0,k1_tarski(esk5_0))
    & m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,k1_tarski(esk5_0))))
    & k5_partfun1(esk4_0,k1_tarski(esk5_0),esk6_0) != k1_tarski(esk7_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).

fof(c_0_14,plain,(
    ! [X14,X15,X16,X17,X18,X20,X21,X22,X24] :
      ( ( v1_funct_1(esk1_5(X14,X15,X16,X17,X18))
        | ~ r2_hidden(X18,X17)
        | X17 != k5_partfun1(X14,X15,X16)
        | ~ v1_funct_1(X16)
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X15))) )
      & ( m1_subset_1(esk1_5(X14,X15,X16,X17,X18),k1_zfmisc_1(k2_zfmisc_1(X14,X15)))
        | ~ r2_hidden(X18,X17)
        | X17 != k5_partfun1(X14,X15,X16)
        | ~ v1_funct_1(X16)
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X15))) )
      & ( esk1_5(X14,X15,X16,X17,X18) = X18
        | ~ r2_hidden(X18,X17)
        | X17 != k5_partfun1(X14,X15,X16)
        | ~ v1_funct_1(X16)
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X15))) )
      & ( v1_partfun1(esk1_5(X14,X15,X16,X17,X18),X14)
        | ~ r2_hidden(X18,X17)
        | X17 != k5_partfun1(X14,X15,X16)
        | ~ v1_funct_1(X16)
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X15))) )
      & ( r1_partfun1(X16,esk1_5(X14,X15,X16,X17,X18))
        | ~ r2_hidden(X18,X17)
        | X17 != k5_partfun1(X14,X15,X16)
        | ~ v1_funct_1(X16)
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X15))) )
      & ( ~ v1_funct_1(X21)
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X14,X15)))
        | X21 != X20
        | ~ v1_partfun1(X21,X14)
        | ~ r1_partfun1(X16,X21)
        | r2_hidden(X20,X17)
        | X17 != k5_partfun1(X14,X15,X16)
        | ~ v1_funct_1(X16)
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X15))) )
      & ( ~ r2_hidden(esk2_4(X14,X15,X16,X22),X22)
        | ~ v1_funct_1(X24)
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X14,X15)))
        | X24 != esk2_4(X14,X15,X16,X22)
        | ~ v1_partfun1(X24,X14)
        | ~ r1_partfun1(X16,X24)
        | X22 = k5_partfun1(X14,X15,X16)
        | ~ v1_funct_1(X16)
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X15))) )
      & ( v1_funct_1(esk3_4(X14,X15,X16,X22))
        | r2_hidden(esk2_4(X14,X15,X16,X22),X22)
        | X22 = k5_partfun1(X14,X15,X16)
        | ~ v1_funct_1(X16)
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X15))) )
      & ( m1_subset_1(esk3_4(X14,X15,X16,X22),k1_zfmisc_1(k2_zfmisc_1(X14,X15)))
        | r2_hidden(esk2_4(X14,X15,X16,X22),X22)
        | X22 = k5_partfun1(X14,X15,X16)
        | ~ v1_funct_1(X16)
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X15))) )
      & ( esk3_4(X14,X15,X16,X22) = esk2_4(X14,X15,X16,X22)
        | r2_hidden(esk2_4(X14,X15,X16,X22),X22)
        | X22 = k5_partfun1(X14,X15,X16)
        | ~ v1_funct_1(X16)
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X15))) )
      & ( v1_partfun1(esk3_4(X14,X15,X16,X22),X14)
        | r2_hidden(esk2_4(X14,X15,X16,X22),X22)
        | X22 = k5_partfun1(X14,X15,X16)
        | ~ v1_funct_1(X16)
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X15))) )
      & ( r1_partfun1(X16,esk3_4(X14,X15,X16,X22))
        | r2_hidden(esk2_4(X14,X15,X16,X22),X22)
        | X22 = k5_partfun1(X14,X15,X16)
        | ~ v1_funct_1(X16)
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X15))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_partfun1])])])])])])).

cnf(c_0_15,plain,
    ( r1_partfun1(X1,X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,k1_tarski(X3))))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,k1_tarski(X3)))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,k1_tarski(esk5_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( v1_partfun1(esk1_5(X1,X2,X3,X4,X5),X1)
    | ~ r2_hidden(X5,X4)
    | X4 != k5_partfun1(X1,X2,X3)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( esk1_5(X1,X2,X3,X4,X5) = X5
    | ~ r2_hidden(X5,X4)
    | X4 != k5_partfun1(X1,X2,X3)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_21,plain,(
    ! [X30,X31,X32,X33] :
      ( ( X31 = k1_xboole_0
        | r2_hidden(X33,k5_partfun1(X30,X31,X32))
        | ~ r1_partfun1(X32,X33)
        | ~ v1_funct_1(X33)
        | ~ v1_funct_2(X33,X30,X31)
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))
        | ~ v1_funct_1(X32)
        | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31))) )
      & ( X30 != k1_xboole_0
        | r2_hidden(X33,k5_partfun1(X30,X31,X32))
        | ~ r1_partfun1(X32,X33)
        | ~ v1_funct_1(X33)
        | ~ v1_funct_2(X33,X30,X31)
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))
        | ~ v1_funct_1(X32)
        | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t155_funct_2])])])])).

cnf(c_0_22,plain,
    ( r1_partfun1(X1,X4)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,k1_enumset1(X3,X3,X3))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,k1_enumset1(X3,X3,X3)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_15,c_0_16]),c_0_16]),c_0_17]),c_0_17])).

cnf(c_0_23,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,k1_enumset1(esk5_0,esk5_0,esk5_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18,c_0_16]),c_0_17])).

cnf(c_0_24,negated_conjecture,
    ( v1_funct_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_25,plain,(
    ! [X34,X35,X36] :
      ( ( ~ v1_partfun1(X36,X34)
        | k5_partfun1(X34,X35,X36) = k1_tarski(X36)
        | ~ v1_funct_1(X36)
        | ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35))) )
      & ( k5_partfun1(X34,X35,X36) != k1_tarski(X36)
        | v1_partfun1(X36,X34)
        | ~ v1_funct_1(X36)
        | ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t174_partfun1])])])).

cnf(c_0_26,plain,
    ( v1_partfun1(esk1_5(X1,X2,X3,k5_partfun1(X1,X2,X3),X4),X1)
    | ~ r2_hidden(X4,k5_partfun1(X1,X2,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3) ),
    inference(er,[status(thm)],[c_0_19])).

cnf(c_0_27,plain,
    ( esk1_5(X1,X2,X3,k5_partfun1(X1,X2,X3),X4) = X4
    | ~ r2_hidden(X4,k5_partfun1(X1,X2,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3) ),
    inference(er,[status(thm)],[c_0_20])).

cnf(c_0_28,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(X2,k5_partfun1(X3,X1,X4))
    | ~ r1_partfun1(X4,X2)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X3,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,negated_conjecture,
    ( v1_funct_2(esk7_0,esk4_0,k1_tarski(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_30,negated_conjecture,
    ( r1_partfun1(X1,esk7_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk4_0,k1_enumset1(esk5_0,esk5_0,esk5_0))))
    | ~ v1_funct_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24])])).

cnf(c_0_31,plain,
    ( k5_partfun1(X2,X3,X1) = k1_tarski(X1)
    | ~ v1_partfun1(X1,X2)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_32,plain,(
    ! [X12,X13] :
      ( ( k2_zfmisc_1(k1_tarski(X13),X12) != k1_xboole_0
        | X12 = k1_xboole_0 )
      & ( k2_zfmisc_1(X12,k1_tarski(X13)) != k1_xboole_0
        | X12 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t130_zfmisc_1])])])).

cnf(c_0_33,plain,
    ( v1_partfun1(X1,X2)
    | ~ r2_hidden(X1,k5_partfun1(X2,X3,X4))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X4) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_34,negated_conjecture,
    ( k1_enumset1(esk5_0,esk5_0,esk5_0) = k1_xboole_0
    | r2_hidden(X1,k5_partfun1(esk4_0,k1_enumset1(esk5_0,esk5_0,esk5_0),esk7_0))
    | ~ v1_funct_2(X1,esk4_0,k1_enumset1(esk5_0,esk5_0,esk5_0))
    | ~ r1_partfun1(esk7_0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk4_0,k1_enumset1(esk5_0,esk5_0,esk5_0))))
    | ~ v1_funct_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_23]),c_0_24])])).

cnf(c_0_35,negated_conjecture,
    ( v1_funct_2(esk7_0,esk4_0,k1_enumset1(esk5_0,esk5_0,esk5_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_16]),c_0_17])).

cnf(c_0_36,negated_conjecture,
    ( r1_partfun1(esk7_0,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_23]),c_0_24])])).

fof(c_0_37,plain,(
    ! [X10,X11] :
      ( ( k2_zfmisc_1(X10,X11) != k1_xboole_0
        | X10 = k1_xboole_0
        | X11 = k1_xboole_0 )
      & ( X10 != k1_xboole_0
        | k2_zfmisc_1(X10,X11) = k1_xboole_0 )
      & ( X11 != k1_xboole_0
        | k2_zfmisc_1(X10,X11) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_38,plain,
    ( m1_subset_1(esk1_5(X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X5,X4)
    | X4 != k5_partfun1(X1,X2,X3)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_39,plain,
    ( v1_funct_1(esk1_5(X1,X2,X3,X4,X5))
    | ~ r2_hidden(X5,X4)
    | X4 != k5_partfun1(X1,X2,X3)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_40,plain,
    ( k5_partfun1(X2,X3,X1) = k1_enumset1(X1,X1,X1)
    | ~ v1_funct_1(X1)
    | ~ v1_partfun1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_16]),c_0_17])).

cnf(c_0_41,plain,
    ( X1 = k1_xboole_0
    | k2_zfmisc_1(X1,k1_tarski(X2)) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_42,negated_conjecture,
    ( v1_partfun1(X1,esk4_0)
    | ~ r2_hidden(X1,k5_partfun1(esk4_0,k1_enumset1(esk5_0,esk5_0,esk5_0),esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_23]),c_0_24])])).

cnf(c_0_43,negated_conjecture,
    ( k1_enumset1(esk5_0,esk5_0,esk5_0) = k1_xboole_0
    | r2_hidden(esk7_0,k5_partfun1(esk4_0,k1_enumset1(esk5_0,esk5_0,esk5_0),esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_23]),c_0_35]),c_0_36]),c_0_24])])).

cnf(c_0_44,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_45,plain,
    ( m1_subset_1(esk1_5(X1,X2,X3,k5_partfun1(X1,X2,X3),X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X4,k5_partfun1(X1,X2,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3) ),
    inference(er,[status(thm)],[c_0_38])).

cnf(c_0_46,plain,
    ( v1_funct_1(esk1_5(X1,X2,X3,k5_partfun1(X1,X2,X3),X4))
    | ~ r2_hidden(X4,k5_partfun1(X1,X2,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3) ),
    inference(er,[status(thm)],[c_0_39])).

cnf(c_0_47,negated_conjecture,
    ( k5_partfun1(esk4_0,k1_enumset1(esk5_0,esk5_0,esk5_0),esk7_0) = k1_enumset1(esk7_0,esk7_0,esk7_0)
    | ~ v1_partfun1(esk7_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_23]),c_0_24])])).

cnf(c_0_48,negated_conjecture,
    ( k5_partfun1(esk4_0,k1_tarski(esk5_0),esk6_0) != k1_tarski(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_49,plain,
    ( X1 = k1_xboole_0
    | k2_zfmisc_1(X1,k1_enumset1(X2,X2,X2)) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_16]),c_0_17])).

cnf(c_0_50,negated_conjecture,
    ( k1_enumset1(esk5_0,esk5_0,esk5_0) = k1_xboole_0
    | v1_partfun1(esk7_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_51,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_44])).

cnf(c_0_52,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r2_hidden(X1,k5_partfun1(X2,X3,X4))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X4) ),
    inference(spm,[status(thm)],[c_0_45,c_0_27])).

cnf(c_0_53,negated_conjecture,
    ( v1_funct_1(esk1_5(esk4_0,k1_enumset1(esk5_0,esk5_0,esk5_0),esk7_0,k1_enumset1(esk7_0,esk7_0,esk7_0),X1))
    | ~ v1_partfun1(esk7_0,esk4_0)
    | ~ r2_hidden(X1,k1_enumset1(esk7_0,esk7_0,esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_23]),c_0_24])])).

cnf(c_0_54,negated_conjecture,
    ( esk1_5(esk4_0,k1_enumset1(esk5_0,esk5_0,esk5_0),esk7_0,k1_enumset1(esk7_0,esk7_0,esk7_0),X1) = X1
    | ~ v1_partfun1(esk7_0,esk4_0)
    | ~ r2_hidden(X1,k1_enumset1(esk7_0,esk7_0,esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_47]),c_0_23]),c_0_24])])).

cnf(c_0_55,negated_conjecture,
    ( k5_partfun1(esk4_0,k1_enumset1(esk5_0,esk5_0,esk5_0),esk6_0) != k1_enumset1(esk7_0,esk7_0,esk7_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_16]),c_0_16]),c_0_17]),c_0_17])).

cnf(c_0_56,negated_conjecture,
    ( X1 = k1_xboole_0
    | v1_partfun1(esk7_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_51])])).

cnf(c_0_57,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk4_0,k1_enumset1(esk5_0,esk5_0,esk5_0))))
    | ~ v1_partfun1(esk7_0,esk4_0)
    | ~ r2_hidden(X1,k1_enumset1(esk7_0,esk7_0,esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_47]),c_0_23]),c_0_24])])).

cnf(c_0_58,negated_conjecture,
    ( v1_funct_1(X1)
    | ~ v1_partfun1(esk7_0,esk4_0)
    | ~ r2_hidden(X1,k1_enumset1(esk7_0,esk7_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_59,plain,
    ( X4 = k5_partfun1(X1,X2,X3)
    | ~ r2_hidden(esk2_4(X1,X2,X3,X4),X4)
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X5 != esk2_4(X1,X2,X3,X4)
    | ~ v1_partfun1(X5,X1)
    | ~ r1_partfun1(X3,X5)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_60,negated_conjecture,
    ( v1_partfun1(esk7_0,esk4_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_56])).

cnf(c_0_61,negated_conjecture,
    ( v1_partfun1(X1,esk4_0)
    | ~ v1_partfun1(esk7_0,esk4_0)
    | ~ r2_hidden(X1,k1_enumset1(esk7_0,esk7_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_47])).

cnf(c_0_62,negated_conjecture,
    ( r1_partfun1(X1,X2)
    | ~ v1_partfun1(esk7_0,esk4_0)
    | ~ r2_hidden(X2,k1_enumset1(esk7_0,esk7_0,esk7_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk4_0,k1_enumset1(esk5_0,esk5_0,esk5_0))))
    | ~ v1_funct_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_57]),c_0_58])).

cnf(c_0_63,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,k1_tarski(esk5_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_64,plain,
    ( X1 = k5_partfun1(X2,X3,X4)
    | ~ r1_partfun1(X4,esk2_4(X2,X3,X4,X1))
    | ~ v1_partfun1(esk2_4(X2,X3,X4,X1),X2)
    | ~ r2_hidden(esk2_4(X2,X3,X4,X1),X1)
    | ~ m1_subset_1(esk2_4(X2,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(esk2_4(X2,X3,X4,X1))
    | ~ v1_funct_1(X4) ),
    inference(er,[status(thm)],[c_0_59])).

cnf(c_0_65,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk4_0,k1_enumset1(esk5_0,esk5_0,esk5_0))))
    | ~ r2_hidden(X1,k1_enumset1(esk7_0,esk7_0,esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_57,c_0_60])])).

cnf(c_0_66,negated_conjecture,
    ( v1_funct_1(X1)
    | ~ r2_hidden(X1,k1_enumset1(esk7_0,esk7_0,esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_58,c_0_60])])).

cnf(c_0_67,negated_conjecture,
    ( v1_partfun1(X1,esk4_0)
    | ~ r2_hidden(X1,k1_enumset1(esk7_0,esk7_0,esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_60])])).

cnf(c_0_68,negated_conjecture,
    ( r1_partfun1(X1,X2)
    | ~ r2_hidden(X2,k1_enumset1(esk7_0,esk7_0,esk7_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk4_0,k1_enumset1(esk5_0,esk5_0,esk5_0))))
    | ~ v1_funct_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_62,c_0_60])])).

cnf(c_0_69,plain,
    ( esk3_4(X1,X2,X3,X4) = esk2_4(X1,X2,X3,X4)
    | r2_hidden(esk2_4(X1,X2,X3,X4),X4)
    | X4 = k5_partfun1(X1,X2,X3)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_70,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,k1_enumset1(esk5_0,esk5_0,esk5_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_63,c_0_16]),c_0_17])).

cnf(c_0_71,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_72,plain,
    ( r1_partfun1(X1,esk3_4(X2,X3,X1,X4))
    | r2_hidden(esk2_4(X2,X3,X1,X4),X4)
    | X4 = k5_partfun1(X2,X3,X1)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_73,plain,
    ( v1_partfun1(esk3_4(X1,X2,X3,X4),X1)
    | r2_hidden(esk2_4(X1,X2,X3,X4),X4)
    | X4 = k5_partfun1(X1,X2,X3)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_74,plain,
    ( v1_funct_1(esk3_4(X1,X2,X3,X4))
    | r2_hidden(esk2_4(X1,X2,X3,X4),X4)
    | X4 = k5_partfun1(X1,X2,X3)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_75,negated_conjecture,
    ( X1 = k5_partfun1(esk4_0,k1_enumset1(esk5_0,esk5_0,esk5_0),X2)
    | ~ r2_hidden(esk2_4(esk4_0,k1_enumset1(esk5_0,esk5_0,esk5_0),X2,X1),k1_enumset1(esk7_0,esk7_0,esk7_0))
    | ~ r2_hidden(esk2_4(esk4_0,k1_enumset1(esk5_0,esk5_0,esk5_0),X2,X1),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(esk4_0,k1_enumset1(esk5_0,esk5_0,esk5_0))))
    | ~ v1_funct_1(X2) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_66]),c_0_67]),c_0_68])).

cnf(c_0_76,negated_conjecture,
    ( esk3_4(esk4_0,k1_enumset1(esk5_0,esk5_0,esk5_0),esk6_0,X1) = esk2_4(esk4_0,k1_enumset1(esk5_0,esk5_0,esk5_0),esk6_0,X1)
    | X1 = k5_partfun1(esk4_0,k1_enumset1(esk5_0,esk5_0,esk5_0),esk6_0)
    | r2_hidden(esk2_4(esk4_0,k1_enumset1(esk5_0,esk5_0,esk5_0),esk6_0,X1),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_71])])).

cnf(c_0_77,negated_conjecture,
    ( X1 = k5_partfun1(esk4_0,k1_enumset1(esk5_0,esk5_0,esk5_0),esk6_0)
    | r1_partfun1(esk6_0,esk3_4(esk4_0,k1_enumset1(esk5_0,esk5_0,esk5_0),esk6_0,X1))
    | r2_hidden(esk2_4(esk4_0,k1_enumset1(esk5_0,esk5_0,esk5_0),esk6_0,X1),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_70]),c_0_71])])).

cnf(c_0_78,negated_conjecture,
    ( X1 = k5_partfun1(esk4_0,k1_enumset1(esk5_0,esk5_0,esk5_0),esk6_0)
    | v1_partfun1(esk3_4(esk4_0,k1_enumset1(esk5_0,esk5_0,esk5_0),esk6_0,X1),esk4_0)
    | r2_hidden(esk2_4(esk4_0,k1_enumset1(esk5_0,esk5_0,esk5_0),esk6_0,X1),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_70]),c_0_71])])).

cnf(c_0_79,negated_conjecture,
    ( X1 = k5_partfun1(esk4_0,k1_enumset1(esk5_0,esk5_0,esk5_0),esk6_0)
    | r2_hidden(esk2_4(esk4_0,k1_enumset1(esk5_0,esk5_0,esk5_0),esk6_0,X1),X1)
    | v1_funct_1(esk3_4(esk4_0,k1_enumset1(esk5_0,esk5_0,esk5_0),esk6_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_70]),c_0_71])])).

cnf(c_0_80,plain,
    ( r2_hidden(X4,X6)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | X1 != X4
    | ~ v1_partfun1(X1,X2)
    | ~ r1_partfun1(X5,X1)
    | X6 != k5_partfun1(X2,X3,X5)
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_81,plain,
    ( m1_subset_1(esk3_4(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r2_hidden(esk2_4(X1,X2,X3,X4),X4)
    | X4 = k5_partfun1(X1,X2,X3)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_82,negated_conjecture,
    ( esk3_4(esk4_0,k1_enumset1(esk5_0,esk5_0,esk5_0),esk6_0,k1_enumset1(esk7_0,esk7_0,esk7_0)) = esk2_4(esk4_0,k1_enumset1(esk5_0,esk5_0,esk5_0),esk6_0,k1_enumset1(esk7_0,esk7_0,esk7_0))
    | ~ r2_hidden(esk2_4(esk4_0,k1_enumset1(esk5_0,esk5_0,esk5_0),esk6_0,k1_enumset1(esk7_0,esk7_0,esk7_0)),k1_enumset1(esk7_0,esk7_0,esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_70]),c_0_71])]),c_0_55])).

cnf(c_0_83,negated_conjecture,
    ( r1_partfun1(esk6_0,esk3_4(esk4_0,k1_enumset1(esk5_0,esk5_0,esk5_0),esk6_0,k1_enumset1(esk7_0,esk7_0,esk7_0)))
    | ~ r2_hidden(esk2_4(esk4_0,k1_enumset1(esk5_0,esk5_0,esk5_0),esk6_0,k1_enumset1(esk7_0,esk7_0,esk7_0)),k1_enumset1(esk7_0,esk7_0,esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_77]),c_0_70]),c_0_71])]),c_0_55])).

cnf(c_0_84,negated_conjecture,
    ( v1_partfun1(esk3_4(esk4_0,k1_enumset1(esk5_0,esk5_0,esk5_0),esk6_0,k1_enumset1(esk7_0,esk7_0,esk7_0)),esk4_0)
    | ~ r2_hidden(esk2_4(esk4_0,k1_enumset1(esk5_0,esk5_0,esk5_0),esk6_0,k1_enumset1(esk7_0,esk7_0,esk7_0)),k1_enumset1(esk7_0,esk7_0,esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_78]),c_0_70]),c_0_71])]),c_0_55])).

cnf(c_0_85,negated_conjecture,
    ( v1_funct_1(esk3_4(esk4_0,k1_enumset1(esk5_0,esk5_0,esk5_0),esk6_0,k1_enumset1(esk7_0,esk7_0,esk7_0)))
    | v1_funct_1(esk2_4(esk4_0,k1_enumset1(esk5_0,esk5_0,esk5_0),esk6_0,k1_enumset1(esk7_0,esk7_0,esk7_0)))
    | ~ v1_partfun1(esk7_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_79]),c_0_55])).

cnf(c_0_86,plain,
    ( r2_hidden(X1,k5_partfun1(X2,X3,X4))
    | ~ r1_partfun1(X4,X1)
    | ~ v1_partfun1(X1,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X1) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_80])])).

cnf(c_0_87,negated_conjecture,
    ( X1 = k5_partfun1(esk4_0,k1_enumset1(esk5_0,esk5_0,esk5_0),esk6_0)
    | r2_hidden(esk2_4(esk4_0,k1_enumset1(esk5_0,esk5_0,esk5_0),esk6_0,X1),X1)
    | m1_subset_1(esk3_4(esk4_0,k1_enumset1(esk5_0,esk5_0,esk5_0),esk6_0,X1),k1_zfmisc_1(k2_zfmisc_1(esk4_0,k1_enumset1(esk5_0,esk5_0,esk5_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_70]),c_0_71])])).

cnf(c_0_88,negated_conjecture,
    ( esk3_4(esk4_0,k1_enumset1(esk5_0,esk5_0,esk5_0),esk6_0,k1_enumset1(esk7_0,esk7_0,esk7_0)) = esk2_4(esk4_0,k1_enumset1(esk5_0,esk5_0,esk5_0),esk6_0,k1_enumset1(esk7_0,esk7_0,esk7_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_76]),c_0_55])).

cnf(c_0_89,negated_conjecture,
    ( r1_partfun1(esk6_0,esk3_4(esk4_0,k1_enumset1(esk5_0,esk5_0,esk5_0),esk6_0,k1_enumset1(esk7_0,esk7_0,esk7_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_77]),c_0_55])).

cnf(c_0_90,negated_conjecture,
    ( v1_partfun1(esk3_4(esk4_0,k1_enumset1(esk5_0,esk5_0,esk5_0),esk6_0,k1_enumset1(esk7_0,esk7_0,esk7_0)),esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_78]),c_0_55])).

cnf(c_0_91,negated_conjecture,
    ( v1_funct_1(esk2_4(esk4_0,k1_enumset1(esk5_0,esk5_0,esk5_0),esk6_0,k1_enumset1(esk7_0,esk7_0,esk7_0)))
    | v1_funct_1(esk3_4(esk4_0,k1_enumset1(esk5_0,esk5_0,esk5_0),esk6_0,k1_enumset1(esk7_0,esk7_0,esk7_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_85,c_0_60])])).

cnf(c_0_92,negated_conjecture,
    ( esk3_4(esk4_0,k1_enumset1(esk5_0,esk5_0,esk5_0),esk6_0,k1_enumset1(esk7_0,esk7_0,esk7_0)) = esk2_4(esk4_0,k1_enumset1(esk5_0,esk5_0,esk5_0),esk6_0,k1_enumset1(esk7_0,esk7_0,esk7_0))
    | v1_funct_1(esk2_4(esk4_0,k1_enumset1(esk5_0,esk5_0,esk5_0),esk6_0,k1_enumset1(esk7_0,esk7_0,esk7_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_76]),c_0_55])).

cnf(c_0_93,negated_conjecture,
    ( r2_hidden(X1,k5_partfun1(esk4_0,k1_enumset1(esk5_0,esk5_0,esk5_0),esk7_0))
    | ~ r1_partfun1(esk7_0,X1)
    | ~ v1_partfun1(X1,esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk4_0,k1_enumset1(esk5_0,esk5_0,esk5_0))))
    | ~ v1_funct_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_23]),c_0_24])])).

cnf(c_0_94,negated_conjecture,
    ( k5_partfun1(esk4_0,k1_enumset1(esk5_0,esk5_0,esk5_0),esk7_0) = k1_enumset1(esk7_0,esk7_0,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_60])])).

cnf(c_0_95,negated_conjecture,
    ( m1_subset_1(esk2_4(esk4_0,k1_enumset1(esk5_0,esk5_0,esk5_0),esk6_0,k1_enumset1(esk7_0,esk7_0,esk7_0)),k1_zfmisc_1(k2_zfmisc_1(esk4_0,k1_enumset1(esk5_0,esk5_0,esk5_0)))) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_88]),c_0_55]),c_0_65])).

cnf(c_0_96,negated_conjecture,
    ( r1_partfun1(esk6_0,esk2_4(esk4_0,k1_enumset1(esk5_0,esk5_0,esk5_0),esk6_0,k1_enumset1(esk7_0,esk7_0,esk7_0))) ),
    inference(rw,[status(thm)],[c_0_89,c_0_88])).

cnf(c_0_97,negated_conjecture,
    ( v1_partfun1(esk2_4(esk4_0,k1_enumset1(esk5_0,esk5_0,esk5_0),esk6_0,k1_enumset1(esk7_0,esk7_0,esk7_0)),esk4_0) ),
    inference(rw,[status(thm)],[c_0_90,c_0_88])).

cnf(c_0_98,negated_conjecture,
    ( v1_funct_1(esk2_4(esk4_0,k1_enumset1(esk5_0,esk5_0,esk5_0),esk6_0,k1_enumset1(esk7_0,esk7_0,esk7_0))) ),
    inference(spm,[status(thm)],[c_0_91,c_0_92])).

cnf(c_0_99,negated_conjecture,
    ( r2_hidden(X1,k1_enumset1(esk7_0,esk7_0,esk7_0))
    | ~ r1_partfun1(esk7_0,X1)
    | ~ v1_partfun1(X1,esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk4_0,k1_enumset1(esk5_0,esk5_0,esk5_0))))
    | ~ v1_funct_1(X1) ),
    inference(rw,[status(thm)],[c_0_93,c_0_94])).

cnf(c_0_100,negated_conjecture,
    ( ~ r2_hidden(esk2_4(esk4_0,k1_enumset1(esk5_0,esk5_0,esk5_0),esk6_0,k1_enumset1(esk7_0,esk7_0,esk7_0)),k1_enumset1(esk7_0,esk7_0,esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_95]),c_0_96]),c_0_97]),c_0_70]),c_0_98]),c_0_71])]),c_0_55])).

cnf(c_0_101,negated_conjecture,
    ( ~ r1_partfun1(esk7_0,esk2_4(esk4_0,k1_enumset1(esk5_0,esk5_0,esk5_0),esk6_0,k1_enumset1(esk7_0,esk7_0,esk7_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_95]),c_0_97]),c_0_98])]),c_0_100])).

cnf(c_0_102,negated_conjecture,
    ( r1_partfun1(X1,esk2_4(esk4_0,k1_enumset1(esk5_0,esk5_0,esk5_0),esk6_0,k1_enumset1(esk7_0,esk7_0,esk7_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk4_0,k1_enumset1(esk5_0,esk5_0,esk5_0))))
    | ~ v1_funct_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_95]),c_0_98])])).

cnf(c_0_103,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_102]),c_0_23]),c_0_24])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:04:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.57  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.19/0.57  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.57  #
% 0.19/0.57  # Preprocessing time       : 0.024 s
% 0.19/0.57  # Presaturation interreduction done
% 0.19/0.57  
% 0.19/0.57  # Proof found!
% 0.19/0.57  # SZS status Theorem
% 0.19/0.57  # SZS output start CNFRefutation
% 0.19/0.57  fof(t164_funct_2, conjecture, ![X1, X2, X3]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,k1_tarski(X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))))=>k5_partfun1(X1,k1_tarski(X2),X3)=k1_tarski(X4))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t164_funct_2)).
% 0.19/0.57  fof(t143_partfun1, axiom, ![X1, X2, X3]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))))=>![X4]:((v1_funct_1(X4)&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))))=>r1_partfun1(X3,X4))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_partfun1)).
% 0.19/0.57  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.19/0.57  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.19/0.57  fof(d7_partfun1, axiom, ![X1, X2, X3]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(X4=k5_partfun1(X1,X2,X3)<=>![X5]:(r2_hidden(X5,X4)<=>?[X6]:((((v1_funct_1(X6)&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&X6=X5)&v1_partfun1(X6,X1))&r1_partfun1(X3,X6))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_partfun1)).
% 0.19/0.57  fof(t155_funct_2, axiom, ![X1, X2, X3]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r1_partfun1(X3,X4)=>((X2=k1_xboole_0&X1!=k1_xboole_0)|r2_hidden(X4,k5_partfun1(X1,X2,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t155_funct_2)).
% 0.19/0.57  fof(t174_partfun1, axiom, ![X1, X2, X3]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(v1_partfun1(X3,X1)<=>k5_partfun1(X1,X2,X3)=k1_tarski(X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t174_partfun1)).
% 0.19/0.57  fof(t130_zfmisc_1, axiom, ![X1, X2]:(X1!=k1_xboole_0=>(k2_zfmisc_1(k1_tarski(X2),X1)!=k1_xboole_0&k2_zfmisc_1(X1,k1_tarski(X2))!=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t130_zfmisc_1)).
% 0.19/0.57  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.19/0.57  fof(c_0_9, negated_conjecture, ~(![X1, X2, X3]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,k1_tarski(X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))))=>k5_partfun1(X1,k1_tarski(X2),X3)=k1_tarski(X4)))), inference(assume_negation,[status(cth)],[t164_funct_2])).
% 0.19/0.57  fof(c_0_10, plain, ![X26, X27, X28, X29]:(~v1_funct_1(X28)|~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,k1_tarski(X27))))|(~v1_funct_1(X29)|~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X26,k1_tarski(X27))))|r1_partfun1(X28,X29))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_partfun1])])])).
% 0.19/0.57  fof(c_0_11, plain, ![X7]:k2_tarski(X7,X7)=k1_tarski(X7), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.19/0.57  fof(c_0_12, plain, ![X8, X9]:k1_enumset1(X8,X8,X9)=k2_tarski(X8,X9), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.19/0.57  fof(c_0_13, negated_conjecture, ((v1_funct_1(esk6_0)&m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,k1_tarski(esk5_0)))))&(((v1_funct_1(esk7_0)&v1_funct_2(esk7_0,esk4_0,k1_tarski(esk5_0)))&m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,k1_tarski(esk5_0)))))&k5_partfun1(esk4_0,k1_tarski(esk5_0),esk6_0)!=k1_tarski(esk7_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).
% 0.19/0.57  fof(c_0_14, plain, ![X14, X15, X16, X17, X18, X20, X21, X22, X24]:(((((((v1_funct_1(esk1_5(X14,X15,X16,X17,X18))|~r2_hidden(X18,X17)|X17!=k5_partfun1(X14,X15,X16)|(~v1_funct_1(X16)|~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X15)))))&(m1_subset_1(esk1_5(X14,X15,X16,X17,X18),k1_zfmisc_1(k2_zfmisc_1(X14,X15)))|~r2_hidden(X18,X17)|X17!=k5_partfun1(X14,X15,X16)|(~v1_funct_1(X16)|~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X15))))))&(esk1_5(X14,X15,X16,X17,X18)=X18|~r2_hidden(X18,X17)|X17!=k5_partfun1(X14,X15,X16)|(~v1_funct_1(X16)|~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X15))))))&(v1_partfun1(esk1_5(X14,X15,X16,X17,X18),X14)|~r2_hidden(X18,X17)|X17!=k5_partfun1(X14,X15,X16)|(~v1_funct_1(X16)|~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X15))))))&(r1_partfun1(X16,esk1_5(X14,X15,X16,X17,X18))|~r2_hidden(X18,X17)|X17!=k5_partfun1(X14,X15,X16)|(~v1_funct_1(X16)|~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X15))))))&(~v1_funct_1(X21)|~m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X14,X15)))|X21!=X20|~v1_partfun1(X21,X14)|~r1_partfun1(X16,X21)|r2_hidden(X20,X17)|X17!=k5_partfun1(X14,X15,X16)|(~v1_funct_1(X16)|~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X15))))))&((~r2_hidden(esk2_4(X14,X15,X16,X22),X22)|(~v1_funct_1(X24)|~m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X14,X15)))|X24!=esk2_4(X14,X15,X16,X22)|~v1_partfun1(X24,X14)|~r1_partfun1(X16,X24))|X22=k5_partfun1(X14,X15,X16)|(~v1_funct_1(X16)|~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X15)))))&(((((v1_funct_1(esk3_4(X14,X15,X16,X22))|r2_hidden(esk2_4(X14,X15,X16,X22),X22)|X22=k5_partfun1(X14,X15,X16)|(~v1_funct_1(X16)|~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X15)))))&(m1_subset_1(esk3_4(X14,X15,X16,X22),k1_zfmisc_1(k2_zfmisc_1(X14,X15)))|r2_hidden(esk2_4(X14,X15,X16,X22),X22)|X22=k5_partfun1(X14,X15,X16)|(~v1_funct_1(X16)|~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X15))))))&(esk3_4(X14,X15,X16,X22)=esk2_4(X14,X15,X16,X22)|r2_hidden(esk2_4(X14,X15,X16,X22),X22)|X22=k5_partfun1(X14,X15,X16)|(~v1_funct_1(X16)|~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X15))))))&(v1_partfun1(esk3_4(X14,X15,X16,X22),X14)|r2_hidden(esk2_4(X14,X15,X16,X22),X22)|X22=k5_partfun1(X14,X15,X16)|(~v1_funct_1(X16)|~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X15))))))&(r1_partfun1(X16,esk3_4(X14,X15,X16,X22))|r2_hidden(esk2_4(X14,X15,X16,X22),X22)|X22=k5_partfun1(X14,X15,X16)|(~v1_funct_1(X16)|~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X15)))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_partfun1])])])])])])).
% 0.19/0.57  cnf(c_0_15, plain, (r1_partfun1(X1,X4)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,k1_tarski(X3))))|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,k1_tarski(X3))))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.57  cnf(c_0_16, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.57  cnf(c_0_17, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.57  cnf(c_0_18, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,k1_tarski(esk5_0))))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.57  cnf(c_0_19, plain, (v1_partfun1(esk1_5(X1,X2,X3,X4,X5),X1)|~r2_hidden(X5,X4)|X4!=k5_partfun1(X1,X2,X3)|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.57  cnf(c_0_20, plain, (esk1_5(X1,X2,X3,X4,X5)=X5|~r2_hidden(X5,X4)|X4!=k5_partfun1(X1,X2,X3)|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.57  fof(c_0_21, plain, ![X30, X31, X32, X33]:((X31=k1_xboole_0|r2_hidden(X33,k5_partfun1(X30,X31,X32))|~r1_partfun1(X32,X33)|(~v1_funct_1(X33)|~v1_funct_2(X33,X30,X31)|~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X30,X31))))|(~v1_funct_1(X32)|~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))))&(X30!=k1_xboole_0|r2_hidden(X33,k5_partfun1(X30,X31,X32))|~r1_partfun1(X32,X33)|(~v1_funct_1(X33)|~v1_funct_2(X33,X30,X31)|~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X30,X31))))|(~v1_funct_1(X32)|~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t155_funct_2])])])])).
% 0.19/0.57  cnf(c_0_22, plain, (r1_partfun1(X1,X4)|~v1_funct_1(X4)|~v1_funct_1(X1)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,k1_enumset1(X3,X3,X3))))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,k1_enumset1(X3,X3,X3))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_15, c_0_16]), c_0_16]), c_0_17]), c_0_17])).
% 0.19/0.57  cnf(c_0_23, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,k1_enumset1(esk5_0,esk5_0,esk5_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18, c_0_16]), c_0_17])).
% 0.19/0.57  cnf(c_0_24, negated_conjecture, (v1_funct_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.57  fof(c_0_25, plain, ![X34, X35, X36]:((~v1_partfun1(X36,X34)|k5_partfun1(X34,X35,X36)=k1_tarski(X36)|(~v1_funct_1(X36)|~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))))&(k5_partfun1(X34,X35,X36)!=k1_tarski(X36)|v1_partfun1(X36,X34)|(~v1_funct_1(X36)|~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t174_partfun1])])])).
% 0.19/0.57  cnf(c_0_26, plain, (v1_partfun1(esk1_5(X1,X2,X3,k5_partfun1(X1,X2,X3),X4),X1)|~r2_hidden(X4,k5_partfun1(X1,X2,X3))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X3)), inference(er,[status(thm)],[c_0_19])).
% 0.19/0.57  cnf(c_0_27, plain, (esk1_5(X1,X2,X3,k5_partfun1(X1,X2,X3),X4)=X4|~r2_hidden(X4,k5_partfun1(X1,X2,X3))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X3)), inference(er,[status(thm)],[c_0_20])).
% 0.19/0.57  cnf(c_0_28, plain, (X1=k1_xboole_0|r2_hidden(X2,k5_partfun1(X3,X1,X4))|~r1_partfun1(X4,X2)|~v1_funct_1(X2)|~v1_funct_2(X2,X3,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.57  cnf(c_0_29, negated_conjecture, (v1_funct_2(esk7_0,esk4_0,k1_tarski(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.57  cnf(c_0_30, negated_conjecture, (r1_partfun1(X1,esk7_0)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk4_0,k1_enumset1(esk5_0,esk5_0,esk5_0))))|~v1_funct_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24])])).
% 0.19/0.57  cnf(c_0_31, plain, (k5_partfun1(X2,X3,X1)=k1_tarski(X1)|~v1_partfun1(X1,X2)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.57  fof(c_0_32, plain, ![X12, X13]:((k2_zfmisc_1(k1_tarski(X13),X12)!=k1_xboole_0|X12=k1_xboole_0)&(k2_zfmisc_1(X12,k1_tarski(X13))!=k1_xboole_0|X12=k1_xboole_0)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t130_zfmisc_1])])])).
% 0.19/0.57  cnf(c_0_33, plain, (v1_partfun1(X1,X2)|~r2_hidden(X1,k5_partfun1(X2,X3,X4))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_funct_1(X4)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.19/0.57  cnf(c_0_34, negated_conjecture, (k1_enumset1(esk5_0,esk5_0,esk5_0)=k1_xboole_0|r2_hidden(X1,k5_partfun1(esk4_0,k1_enumset1(esk5_0,esk5_0,esk5_0),esk7_0))|~v1_funct_2(X1,esk4_0,k1_enumset1(esk5_0,esk5_0,esk5_0))|~r1_partfun1(esk7_0,X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk4_0,k1_enumset1(esk5_0,esk5_0,esk5_0))))|~v1_funct_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_23]), c_0_24])])).
% 0.19/0.57  cnf(c_0_35, negated_conjecture, (v1_funct_2(esk7_0,esk4_0,k1_enumset1(esk5_0,esk5_0,esk5_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29, c_0_16]), c_0_17])).
% 0.19/0.57  cnf(c_0_36, negated_conjecture, (r1_partfun1(esk7_0,esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_23]), c_0_24])])).
% 0.19/0.57  fof(c_0_37, plain, ![X10, X11]:((k2_zfmisc_1(X10,X11)!=k1_xboole_0|(X10=k1_xboole_0|X11=k1_xboole_0))&((X10!=k1_xboole_0|k2_zfmisc_1(X10,X11)=k1_xboole_0)&(X11!=k1_xboole_0|k2_zfmisc_1(X10,X11)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.19/0.57  cnf(c_0_38, plain, (m1_subset_1(esk1_5(X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~r2_hidden(X5,X4)|X4!=k5_partfun1(X1,X2,X3)|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.57  cnf(c_0_39, plain, (v1_funct_1(esk1_5(X1,X2,X3,X4,X5))|~r2_hidden(X5,X4)|X4!=k5_partfun1(X1,X2,X3)|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.57  cnf(c_0_40, plain, (k5_partfun1(X2,X3,X1)=k1_enumset1(X1,X1,X1)|~v1_funct_1(X1)|~v1_partfun1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_16]), c_0_17])).
% 0.19/0.57  cnf(c_0_41, plain, (X1=k1_xboole_0|k2_zfmisc_1(X1,k1_tarski(X2))!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.57  cnf(c_0_42, negated_conjecture, (v1_partfun1(X1,esk4_0)|~r2_hidden(X1,k5_partfun1(esk4_0,k1_enumset1(esk5_0,esk5_0,esk5_0),esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_23]), c_0_24])])).
% 0.19/0.57  cnf(c_0_43, negated_conjecture, (k1_enumset1(esk5_0,esk5_0,esk5_0)=k1_xboole_0|r2_hidden(esk7_0,k5_partfun1(esk4_0,k1_enumset1(esk5_0,esk5_0,esk5_0),esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_23]), c_0_35]), c_0_36]), c_0_24])])).
% 0.19/0.57  cnf(c_0_44, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.19/0.57  cnf(c_0_45, plain, (m1_subset_1(esk1_5(X1,X2,X3,k5_partfun1(X1,X2,X3),X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~r2_hidden(X4,k5_partfun1(X1,X2,X3))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X3)), inference(er,[status(thm)],[c_0_38])).
% 0.19/0.57  cnf(c_0_46, plain, (v1_funct_1(esk1_5(X1,X2,X3,k5_partfun1(X1,X2,X3),X4))|~r2_hidden(X4,k5_partfun1(X1,X2,X3))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X3)), inference(er,[status(thm)],[c_0_39])).
% 0.19/0.57  cnf(c_0_47, negated_conjecture, (k5_partfun1(esk4_0,k1_enumset1(esk5_0,esk5_0,esk5_0),esk7_0)=k1_enumset1(esk7_0,esk7_0,esk7_0)|~v1_partfun1(esk7_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_23]), c_0_24])])).
% 0.19/0.57  cnf(c_0_48, negated_conjecture, (k5_partfun1(esk4_0,k1_tarski(esk5_0),esk6_0)!=k1_tarski(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.57  cnf(c_0_49, plain, (X1=k1_xboole_0|k2_zfmisc_1(X1,k1_enumset1(X2,X2,X2))!=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_16]), c_0_17])).
% 0.19/0.57  cnf(c_0_50, negated_conjecture, (k1_enumset1(esk5_0,esk5_0,esk5_0)=k1_xboole_0|v1_partfun1(esk7_0,esk4_0)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.19/0.57  cnf(c_0_51, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_44])).
% 0.19/0.57  cnf(c_0_52, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r2_hidden(X1,k5_partfun1(X2,X3,X4))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_funct_1(X4)), inference(spm,[status(thm)],[c_0_45, c_0_27])).
% 0.19/0.57  cnf(c_0_53, negated_conjecture, (v1_funct_1(esk1_5(esk4_0,k1_enumset1(esk5_0,esk5_0,esk5_0),esk7_0,k1_enumset1(esk7_0,esk7_0,esk7_0),X1))|~v1_partfun1(esk7_0,esk4_0)|~r2_hidden(X1,k1_enumset1(esk7_0,esk7_0,esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_23]), c_0_24])])).
% 0.19/0.57  cnf(c_0_54, negated_conjecture, (esk1_5(esk4_0,k1_enumset1(esk5_0,esk5_0,esk5_0),esk7_0,k1_enumset1(esk7_0,esk7_0,esk7_0),X1)=X1|~v1_partfun1(esk7_0,esk4_0)|~r2_hidden(X1,k1_enumset1(esk7_0,esk7_0,esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_47]), c_0_23]), c_0_24])])).
% 0.19/0.57  cnf(c_0_55, negated_conjecture, (k5_partfun1(esk4_0,k1_enumset1(esk5_0,esk5_0,esk5_0),esk6_0)!=k1_enumset1(esk7_0,esk7_0,esk7_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48, c_0_16]), c_0_16]), c_0_17]), c_0_17])).
% 0.19/0.57  cnf(c_0_56, negated_conjecture, (X1=k1_xboole_0|v1_partfun1(esk7_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_51])])).
% 0.19/0.57  cnf(c_0_57, negated_conjecture, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk4_0,k1_enumset1(esk5_0,esk5_0,esk5_0))))|~v1_partfun1(esk7_0,esk4_0)|~r2_hidden(X1,k1_enumset1(esk7_0,esk7_0,esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_47]), c_0_23]), c_0_24])])).
% 0.19/0.57  cnf(c_0_58, negated_conjecture, (v1_funct_1(X1)|~v1_partfun1(esk7_0,esk4_0)|~r2_hidden(X1,k1_enumset1(esk7_0,esk7_0,esk7_0))), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.19/0.57  cnf(c_0_59, plain, (X4=k5_partfun1(X1,X2,X3)|~r2_hidden(esk2_4(X1,X2,X3,X4),X4)|~v1_funct_1(X5)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|X5!=esk2_4(X1,X2,X3,X4)|~v1_partfun1(X5,X1)|~r1_partfun1(X3,X5)|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.57  cnf(c_0_60, negated_conjecture, (v1_partfun1(esk7_0,esk4_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_56])).
% 0.19/0.57  cnf(c_0_61, negated_conjecture, (v1_partfun1(X1,esk4_0)|~v1_partfun1(esk7_0,esk4_0)|~r2_hidden(X1,k1_enumset1(esk7_0,esk7_0,esk7_0))), inference(spm,[status(thm)],[c_0_42, c_0_47])).
% 0.19/0.57  cnf(c_0_62, negated_conjecture, (r1_partfun1(X1,X2)|~v1_partfun1(esk7_0,esk4_0)|~r2_hidden(X2,k1_enumset1(esk7_0,esk7_0,esk7_0))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk4_0,k1_enumset1(esk5_0,esk5_0,esk5_0))))|~v1_funct_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_57]), c_0_58])).
% 0.19/0.57  cnf(c_0_63, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,k1_tarski(esk5_0))))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.57  cnf(c_0_64, plain, (X1=k5_partfun1(X2,X3,X4)|~r1_partfun1(X4,esk2_4(X2,X3,X4,X1))|~v1_partfun1(esk2_4(X2,X3,X4,X1),X2)|~r2_hidden(esk2_4(X2,X3,X4,X1),X1)|~m1_subset_1(esk2_4(X2,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_funct_1(esk2_4(X2,X3,X4,X1))|~v1_funct_1(X4)), inference(er,[status(thm)],[c_0_59])).
% 0.19/0.57  cnf(c_0_65, negated_conjecture, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk4_0,k1_enumset1(esk5_0,esk5_0,esk5_0))))|~r2_hidden(X1,k1_enumset1(esk7_0,esk7_0,esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_57, c_0_60])])).
% 0.19/0.57  cnf(c_0_66, negated_conjecture, (v1_funct_1(X1)|~r2_hidden(X1,k1_enumset1(esk7_0,esk7_0,esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_58, c_0_60])])).
% 0.19/0.57  cnf(c_0_67, negated_conjecture, (v1_partfun1(X1,esk4_0)|~r2_hidden(X1,k1_enumset1(esk7_0,esk7_0,esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_61, c_0_60])])).
% 0.19/0.57  cnf(c_0_68, negated_conjecture, (r1_partfun1(X1,X2)|~r2_hidden(X2,k1_enumset1(esk7_0,esk7_0,esk7_0))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk4_0,k1_enumset1(esk5_0,esk5_0,esk5_0))))|~v1_funct_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_62, c_0_60])])).
% 0.19/0.57  cnf(c_0_69, plain, (esk3_4(X1,X2,X3,X4)=esk2_4(X1,X2,X3,X4)|r2_hidden(esk2_4(X1,X2,X3,X4),X4)|X4=k5_partfun1(X1,X2,X3)|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.57  cnf(c_0_70, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,k1_enumset1(esk5_0,esk5_0,esk5_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_63, c_0_16]), c_0_17])).
% 0.19/0.57  cnf(c_0_71, negated_conjecture, (v1_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.57  cnf(c_0_72, plain, (r1_partfun1(X1,esk3_4(X2,X3,X1,X4))|r2_hidden(esk2_4(X2,X3,X1,X4),X4)|X4=k5_partfun1(X2,X3,X1)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.57  cnf(c_0_73, plain, (v1_partfun1(esk3_4(X1,X2,X3,X4),X1)|r2_hidden(esk2_4(X1,X2,X3,X4),X4)|X4=k5_partfun1(X1,X2,X3)|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.57  cnf(c_0_74, plain, (v1_funct_1(esk3_4(X1,X2,X3,X4))|r2_hidden(esk2_4(X1,X2,X3,X4),X4)|X4=k5_partfun1(X1,X2,X3)|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.57  cnf(c_0_75, negated_conjecture, (X1=k5_partfun1(esk4_0,k1_enumset1(esk5_0,esk5_0,esk5_0),X2)|~r2_hidden(esk2_4(esk4_0,k1_enumset1(esk5_0,esk5_0,esk5_0),X2,X1),k1_enumset1(esk7_0,esk7_0,esk7_0))|~r2_hidden(esk2_4(esk4_0,k1_enumset1(esk5_0,esk5_0,esk5_0),X2,X1),X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(esk4_0,k1_enumset1(esk5_0,esk5_0,esk5_0))))|~v1_funct_1(X2)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_66]), c_0_67]), c_0_68])).
% 0.19/0.57  cnf(c_0_76, negated_conjecture, (esk3_4(esk4_0,k1_enumset1(esk5_0,esk5_0,esk5_0),esk6_0,X1)=esk2_4(esk4_0,k1_enumset1(esk5_0,esk5_0,esk5_0),esk6_0,X1)|X1=k5_partfun1(esk4_0,k1_enumset1(esk5_0,esk5_0,esk5_0),esk6_0)|r2_hidden(esk2_4(esk4_0,k1_enumset1(esk5_0,esk5_0,esk5_0),esk6_0,X1),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_71])])).
% 0.19/0.57  cnf(c_0_77, negated_conjecture, (X1=k5_partfun1(esk4_0,k1_enumset1(esk5_0,esk5_0,esk5_0),esk6_0)|r1_partfun1(esk6_0,esk3_4(esk4_0,k1_enumset1(esk5_0,esk5_0,esk5_0),esk6_0,X1))|r2_hidden(esk2_4(esk4_0,k1_enumset1(esk5_0,esk5_0,esk5_0),esk6_0,X1),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_70]), c_0_71])])).
% 0.19/0.57  cnf(c_0_78, negated_conjecture, (X1=k5_partfun1(esk4_0,k1_enumset1(esk5_0,esk5_0,esk5_0),esk6_0)|v1_partfun1(esk3_4(esk4_0,k1_enumset1(esk5_0,esk5_0,esk5_0),esk6_0,X1),esk4_0)|r2_hidden(esk2_4(esk4_0,k1_enumset1(esk5_0,esk5_0,esk5_0),esk6_0,X1),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_70]), c_0_71])])).
% 0.19/0.57  cnf(c_0_79, negated_conjecture, (X1=k5_partfun1(esk4_0,k1_enumset1(esk5_0,esk5_0,esk5_0),esk6_0)|r2_hidden(esk2_4(esk4_0,k1_enumset1(esk5_0,esk5_0,esk5_0),esk6_0,X1),X1)|v1_funct_1(esk3_4(esk4_0,k1_enumset1(esk5_0,esk5_0,esk5_0),esk6_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_70]), c_0_71])])).
% 0.19/0.57  cnf(c_0_80, plain, (r2_hidden(X4,X6)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|X1!=X4|~v1_partfun1(X1,X2)|~r1_partfun1(X5,X1)|X6!=k5_partfun1(X2,X3,X5)|~v1_funct_1(X5)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.57  cnf(c_0_81, plain, (m1_subset_1(esk3_4(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|r2_hidden(esk2_4(X1,X2,X3,X4),X4)|X4=k5_partfun1(X1,X2,X3)|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.57  cnf(c_0_82, negated_conjecture, (esk3_4(esk4_0,k1_enumset1(esk5_0,esk5_0,esk5_0),esk6_0,k1_enumset1(esk7_0,esk7_0,esk7_0))=esk2_4(esk4_0,k1_enumset1(esk5_0,esk5_0,esk5_0),esk6_0,k1_enumset1(esk7_0,esk7_0,esk7_0))|~r2_hidden(esk2_4(esk4_0,k1_enumset1(esk5_0,esk5_0,esk5_0),esk6_0,k1_enumset1(esk7_0,esk7_0,esk7_0)),k1_enumset1(esk7_0,esk7_0,esk7_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_76]), c_0_70]), c_0_71])]), c_0_55])).
% 0.19/0.57  cnf(c_0_83, negated_conjecture, (r1_partfun1(esk6_0,esk3_4(esk4_0,k1_enumset1(esk5_0,esk5_0,esk5_0),esk6_0,k1_enumset1(esk7_0,esk7_0,esk7_0)))|~r2_hidden(esk2_4(esk4_0,k1_enumset1(esk5_0,esk5_0,esk5_0),esk6_0,k1_enumset1(esk7_0,esk7_0,esk7_0)),k1_enumset1(esk7_0,esk7_0,esk7_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_77]), c_0_70]), c_0_71])]), c_0_55])).
% 0.19/0.57  cnf(c_0_84, negated_conjecture, (v1_partfun1(esk3_4(esk4_0,k1_enumset1(esk5_0,esk5_0,esk5_0),esk6_0,k1_enumset1(esk7_0,esk7_0,esk7_0)),esk4_0)|~r2_hidden(esk2_4(esk4_0,k1_enumset1(esk5_0,esk5_0,esk5_0),esk6_0,k1_enumset1(esk7_0,esk7_0,esk7_0)),k1_enumset1(esk7_0,esk7_0,esk7_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_78]), c_0_70]), c_0_71])]), c_0_55])).
% 0.19/0.57  cnf(c_0_85, negated_conjecture, (v1_funct_1(esk3_4(esk4_0,k1_enumset1(esk5_0,esk5_0,esk5_0),esk6_0,k1_enumset1(esk7_0,esk7_0,esk7_0)))|v1_funct_1(esk2_4(esk4_0,k1_enumset1(esk5_0,esk5_0,esk5_0),esk6_0,k1_enumset1(esk7_0,esk7_0,esk7_0)))|~v1_partfun1(esk7_0,esk4_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_79]), c_0_55])).
% 0.19/0.57  cnf(c_0_86, plain, (r2_hidden(X1,k5_partfun1(X2,X3,X4))|~r1_partfun1(X4,X1)|~v1_partfun1(X1,X2)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_funct_1(X4)|~v1_funct_1(X1)), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_80])])).
% 0.19/0.57  cnf(c_0_87, negated_conjecture, (X1=k5_partfun1(esk4_0,k1_enumset1(esk5_0,esk5_0,esk5_0),esk6_0)|r2_hidden(esk2_4(esk4_0,k1_enumset1(esk5_0,esk5_0,esk5_0),esk6_0,X1),X1)|m1_subset_1(esk3_4(esk4_0,k1_enumset1(esk5_0,esk5_0,esk5_0),esk6_0,X1),k1_zfmisc_1(k2_zfmisc_1(esk4_0,k1_enumset1(esk5_0,esk5_0,esk5_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_70]), c_0_71])])).
% 0.19/0.57  cnf(c_0_88, negated_conjecture, (esk3_4(esk4_0,k1_enumset1(esk5_0,esk5_0,esk5_0),esk6_0,k1_enumset1(esk7_0,esk7_0,esk7_0))=esk2_4(esk4_0,k1_enumset1(esk5_0,esk5_0,esk5_0),esk6_0,k1_enumset1(esk7_0,esk7_0,esk7_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_76]), c_0_55])).
% 0.19/0.57  cnf(c_0_89, negated_conjecture, (r1_partfun1(esk6_0,esk3_4(esk4_0,k1_enumset1(esk5_0,esk5_0,esk5_0),esk6_0,k1_enumset1(esk7_0,esk7_0,esk7_0)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_77]), c_0_55])).
% 0.19/0.57  cnf(c_0_90, negated_conjecture, (v1_partfun1(esk3_4(esk4_0,k1_enumset1(esk5_0,esk5_0,esk5_0),esk6_0,k1_enumset1(esk7_0,esk7_0,esk7_0)),esk4_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_78]), c_0_55])).
% 0.19/0.57  cnf(c_0_91, negated_conjecture, (v1_funct_1(esk2_4(esk4_0,k1_enumset1(esk5_0,esk5_0,esk5_0),esk6_0,k1_enumset1(esk7_0,esk7_0,esk7_0)))|v1_funct_1(esk3_4(esk4_0,k1_enumset1(esk5_0,esk5_0,esk5_0),esk6_0,k1_enumset1(esk7_0,esk7_0,esk7_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_85, c_0_60])])).
% 0.19/0.57  cnf(c_0_92, negated_conjecture, (esk3_4(esk4_0,k1_enumset1(esk5_0,esk5_0,esk5_0),esk6_0,k1_enumset1(esk7_0,esk7_0,esk7_0))=esk2_4(esk4_0,k1_enumset1(esk5_0,esk5_0,esk5_0),esk6_0,k1_enumset1(esk7_0,esk7_0,esk7_0))|v1_funct_1(esk2_4(esk4_0,k1_enumset1(esk5_0,esk5_0,esk5_0),esk6_0,k1_enumset1(esk7_0,esk7_0,esk7_0)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_76]), c_0_55])).
% 0.19/0.57  cnf(c_0_93, negated_conjecture, (r2_hidden(X1,k5_partfun1(esk4_0,k1_enumset1(esk5_0,esk5_0,esk5_0),esk7_0))|~r1_partfun1(esk7_0,X1)|~v1_partfun1(X1,esk4_0)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk4_0,k1_enumset1(esk5_0,esk5_0,esk5_0))))|~v1_funct_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_23]), c_0_24])])).
% 0.19/0.57  cnf(c_0_94, negated_conjecture, (k5_partfun1(esk4_0,k1_enumset1(esk5_0,esk5_0,esk5_0),esk7_0)=k1_enumset1(esk7_0,esk7_0,esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_47, c_0_60])])).
% 0.19/0.57  cnf(c_0_95, negated_conjecture, (m1_subset_1(esk2_4(esk4_0,k1_enumset1(esk5_0,esk5_0,esk5_0),esk6_0,k1_enumset1(esk7_0,esk7_0,esk7_0)),k1_zfmisc_1(k2_zfmisc_1(esk4_0,k1_enumset1(esk5_0,esk5_0,esk5_0))))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_88]), c_0_55]), c_0_65])).
% 0.19/0.57  cnf(c_0_96, negated_conjecture, (r1_partfun1(esk6_0,esk2_4(esk4_0,k1_enumset1(esk5_0,esk5_0,esk5_0),esk6_0,k1_enumset1(esk7_0,esk7_0,esk7_0)))), inference(rw,[status(thm)],[c_0_89, c_0_88])).
% 0.19/0.57  cnf(c_0_97, negated_conjecture, (v1_partfun1(esk2_4(esk4_0,k1_enumset1(esk5_0,esk5_0,esk5_0),esk6_0,k1_enumset1(esk7_0,esk7_0,esk7_0)),esk4_0)), inference(rw,[status(thm)],[c_0_90, c_0_88])).
% 0.19/0.57  cnf(c_0_98, negated_conjecture, (v1_funct_1(esk2_4(esk4_0,k1_enumset1(esk5_0,esk5_0,esk5_0),esk6_0,k1_enumset1(esk7_0,esk7_0,esk7_0)))), inference(spm,[status(thm)],[c_0_91, c_0_92])).
% 0.19/0.57  cnf(c_0_99, negated_conjecture, (r2_hidden(X1,k1_enumset1(esk7_0,esk7_0,esk7_0))|~r1_partfun1(esk7_0,X1)|~v1_partfun1(X1,esk4_0)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk4_0,k1_enumset1(esk5_0,esk5_0,esk5_0))))|~v1_funct_1(X1)), inference(rw,[status(thm)],[c_0_93, c_0_94])).
% 0.19/0.57  cnf(c_0_100, negated_conjecture, (~r2_hidden(esk2_4(esk4_0,k1_enumset1(esk5_0,esk5_0,esk5_0),esk6_0,k1_enumset1(esk7_0,esk7_0,esk7_0)),k1_enumset1(esk7_0,esk7_0,esk7_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_95]), c_0_96]), c_0_97]), c_0_70]), c_0_98]), c_0_71])]), c_0_55])).
% 0.19/0.57  cnf(c_0_101, negated_conjecture, (~r1_partfun1(esk7_0,esk2_4(esk4_0,k1_enumset1(esk5_0,esk5_0,esk5_0),esk6_0,k1_enumset1(esk7_0,esk7_0,esk7_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_95]), c_0_97]), c_0_98])]), c_0_100])).
% 0.19/0.57  cnf(c_0_102, negated_conjecture, (r1_partfun1(X1,esk2_4(esk4_0,k1_enumset1(esk5_0,esk5_0,esk5_0),esk6_0,k1_enumset1(esk7_0,esk7_0,esk7_0)))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk4_0,k1_enumset1(esk5_0,esk5_0,esk5_0))))|~v1_funct_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_95]), c_0_98])])).
% 0.19/0.57  cnf(c_0_103, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101, c_0_102]), c_0_23]), c_0_24])]), ['proof']).
% 0.19/0.57  # SZS output end CNFRefutation
% 0.19/0.57  # Proof object total steps             : 104
% 0.19/0.57  # Proof object clause steps            : 85
% 0.19/0.57  # Proof object formula steps           : 19
% 0.19/0.57  # Proof object conjectures             : 58
% 0.19/0.57  # Proof object clause conjectures      : 55
% 0.19/0.57  # Proof object formula conjectures     : 3
% 0.19/0.57  # Proof object initial clauses used    : 24
% 0.19/0.57  # Proof object initial formulas used   : 9
% 0.19/0.57  # Proof object generating inferences   : 38
% 0.19/0.57  # Proof object simplifying inferences  : 118
% 0.19/0.57  # Training examples: 0 positive, 0 negative
% 0.19/0.57  # Parsed axioms                        : 9
% 0.19/0.57  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.57  # Initial clauses                      : 30
% 0.19/0.57  # Removed in clause preprocessing      : 2
% 0.19/0.57  # Initial clauses in saturation        : 28
% 0.19/0.57  # Processed clauses                    : 1695
% 0.19/0.57  # ...of these trivial                  : 0
% 0.19/0.57  # ...subsumed                          : 810
% 0.19/0.57  # ...remaining for further processing  : 885
% 0.19/0.57  # Other redundant clauses eliminated   : 11
% 0.19/0.57  # Clauses deleted for lack of memory   : 0
% 0.19/0.57  # Backward-subsumed                    : 62
% 0.19/0.57  # Backward-rewritten                   : 93
% 0.19/0.57  # Generated clauses                    : 4687
% 0.19/0.57  # ...of the previous two non-trivial   : 4266
% 0.19/0.57  # Contextual simplify-reflections      : 166
% 0.19/0.57  # Paramodulations                      : 4677
% 0.19/0.57  # Factorizations                       : 0
% 0.19/0.57  # Equation resolutions                 : 11
% 0.19/0.57  # Propositional unsat checks           : 0
% 0.19/0.57  #    Propositional check models        : 0
% 0.19/0.57  #    Propositional check unsatisfiable : 0
% 0.19/0.57  #    Propositional clauses             : 0
% 0.19/0.57  #    Propositional clauses after purity: 0
% 0.19/0.57  #    Propositional unsat core size     : 0
% 0.19/0.57  #    Propositional preprocessing time  : 0.000
% 0.19/0.57  #    Propositional encoding time       : 0.000
% 0.19/0.57  #    Propositional solver time         : 0.000
% 0.19/0.57  #    Success case prop preproc time    : 0.000
% 0.19/0.57  #    Success case prop encoding time   : 0.000
% 0.19/0.57  #    Success case prop solver time     : 0.000
% 0.19/0.57  # Current number of processed clauses  : 692
% 0.19/0.57  #    Positive orientable unit clauses  : 21
% 0.19/0.57  #    Positive unorientable unit clauses: 0
% 0.19/0.57  #    Negative unit clauses             : 3
% 0.19/0.57  #    Non-unit-clauses                  : 668
% 0.19/0.57  # Current number of unprocessed clauses: 2275
% 0.19/0.57  # ...number of literals in the above   : 14563
% 0.19/0.57  # Current number of archived formulas  : 0
% 0.19/0.57  # Current number of archived clauses   : 185
% 0.19/0.57  # Clause-clause subsumption calls (NU) : 92090
% 0.19/0.57  # Rec. Clause-clause subsumption calls : 7269
% 0.19/0.57  # Non-unit clause-clause subsumptions  : 1020
% 0.19/0.57  # Unit Clause-clause subsumption calls : 1088
% 0.19/0.57  # Rewrite failures with RHS unbound    : 0
% 0.19/0.57  # BW rewrite match attempts            : 68
% 0.19/0.57  # BW rewrite match successes           : 8
% 0.19/0.57  # Condensation attempts                : 0
% 0.19/0.57  # Condensation successes               : 0
% 0.19/0.57  # Termbank termtop insertions          : 195993
% 0.19/0.57  
% 0.19/0.57  # -------------------------------------------------
% 0.19/0.57  # User time                : 0.220 s
% 0.19/0.57  # System time              : 0.009 s
% 0.19/0.57  # Total time               : 0.229 s
% 0.19/0.57  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
