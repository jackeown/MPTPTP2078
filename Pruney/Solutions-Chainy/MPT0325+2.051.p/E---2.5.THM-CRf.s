%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:44:12 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   71 (3097 expanded)
%              Number of clauses        :   52 (1444 expanded)
%              Number of leaves         :    9 ( 744 expanded)
%              Depth                    :   25
%              Number of atoms          :  171 (7998 expanded)
%              Number of equality atoms :  122 (5164 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t138_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))
     => ( k2_zfmisc_1(X1,X2) = k1_xboole_0
        | ( r1_tarski(X1,X3)
          & r1_tarski(X2,X4) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_zfmisc_1)).

fof(t134_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( k2_zfmisc_1(X1,X2) = k2_zfmisc_1(X3,X4)
     => ( X1 = k1_xboole_0
        | X2 = k1_xboole_0
        | ( X1 = X3
          & X2 = X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t134_zfmisc_1)).

fof(t123_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] : k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4)) = k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_zfmisc_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t92_xboole_1,axiom,(
    ! [X1] : k5_xboole_0(X1,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(t127_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( r1_xboole_0(X1,X2)
        | r1_xboole_0(X3,X4) )
     => r1_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t127_zfmisc_1)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))
       => ( k2_zfmisc_1(X1,X2) = k1_xboole_0
          | ( r1_tarski(X1,X3)
            & r1_tarski(X2,X4) ) ) ) ),
    inference(assume_negation,[status(cth)],[t138_zfmisc_1])).

fof(c_0_10,plain,(
    ! [X30,X31,X32,X33] :
      ( ( X30 = X32
        | X30 = k1_xboole_0
        | X31 = k1_xboole_0
        | k2_zfmisc_1(X30,X31) != k2_zfmisc_1(X32,X33) )
      & ( X31 = X33
        | X30 = k1_xboole_0
        | X31 = k1_xboole_0
        | k2_zfmisc_1(X30,X31) != k2_zfmisc_1(X32,X33) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t134_zfmisc_1])])])).

fof(c_0_11,plain,(
    ! [X22,X23,X24,X25] : k2_zfmisc_1(k3_xboole_0(X22,X23),k3_xboole_0(X24,X25)) = k3_xboole_0(k2_zfmisc_1(X22,X24),k2_zfmisc_1(X23,X25)) ),
    inference(variable_rename,[status(thm)],[t123_zfmisc_1])).

fof(c_0_12,plain,(
    ! [X19,X20] :
      ( ~ r1_tarski(X19,X20)
      | k3_xboole_0(X19,X20) = X19 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

fof(c_0_13,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk5_0,esk6_0))
    & k2_zfmisc_1(esk3_0,esk4_0) != k1_xboole_0
    & ( ~ r1_tarski(esk3_0,esk5_0)
      | ~ r1_tarski(esk4_0,esk6_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).

cnf(c_0_14,plain,
    ( X1 = X2
    | X1 = k1_xboole_0
    | X3 = k1_xboole_0
    | k2_zfmisc_1(X1,X3) != k2_zfmisc_1(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4)) = k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk5_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( X1 = X2
    | X3 = k1_xboole_0
    | X1 = k1_xboole_0
    | k2_zfmisc_1(X3,X1) != k2_zfmisc_1(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_19,plain,(
    ! [X15,X16] :
      ( ( k4_xboole_0(X15,X16) != k1_xboole_0
        | r1_tarski(X15,X16) )
      & ( ~ r1_tarski(X15,X16)
        | k4_xboole_0(X15,X16) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

fof(c_0_20,plain,(
    ! [X17,X18] : k4_xboole_0(X17,X18) = k5_xboole_0(X17,k3_xboole_0(X17,X18)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_21,plain,
    ( X1 = k3_xboole_0(X2,X3)
    | X1 = k1_xboole_0
    | X4 = k1_xboole_0
    | k2_zfmisc_1(X1,X4) != k3_xboole_0(k2_zfmisc_1(X2,X5),k2_zfmisc_1(X3,X6)) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_22,negated_conjecture,
    ( k3_xboole_0(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk5_0,esk6_0)) = k2_zfmisc_1(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_23,plain,
    ( X1 = k3_xboole_0(X2,X3)
    | X1 = k1_xboole_0
    | X4 = k1_xboole_0
    | k2_zfmisc_1(X4,X1) != k3_xboole_0(k2_zfmisc_1(X5,X2),k2_zfmisc_1(X6,X3)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_15])).

cnf(c_0_24,plain,
    ( r1_tarski(X1,X2)
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,negated_conjecture,
    ( X1 = k3_xboole_0(esk3_0,esk5_0)
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k2_zfmisc_1(X1,X2) != k2_zfmisc_1(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

fof(c_0_27,plain,(
    ! [X21] : k5_xboole_0(X21,X21) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t92_xboole_1])).

cnf(c_0_28,negated_conjecture,
    ( X1 = k3_xboole_0(esk4_0,esk6_0)
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k2_zfmisc_1(X2,X1) != k2_zfmisc_1(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_22])).

cnf(c_0_29,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | k2_zfmisc_1(X2,X1) != k2_zfmisc_1(X3,k1_xboole_0) ),
    inference(ef,[status(thm)],[c_0_18])).

cnf(c_0_30,plain,
    ( r1_tarski(X1,X2)
    | k5_xboole_0(X1,k3_xboole_0(X1,X2)) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_31,negated_conjecture,
    ( k3_xboole_0(esk3_0,esk5_0) = esk3_0
    | esk3_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_26])).

cnf(c_0_32,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_33,negated_conjecture,
    ( k3_xboole_0(esk4_0,esk6_0) = esk4_0
    | esk4_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_28])).

cnf(c_0_34,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | k3_xboole_0(X3,X4) = k1_xboole_0
    | k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) != k2_zfmisc_1(X5,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_15])).

cnf(c_0_35,negated_conjecture,
    ( ~ r1_tarski(esk3_0,esk5_0)
    | ~ r1_tarski(esk4_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_36,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | r1_tarski(esk3_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32])])).

cnf(c_0_37,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | r1_tarski(esk4_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_33]),c_0_32])])).

cnf(c_0_38,negated_conjecture,
    ( k3_xboole_0(esk4_0,esk6_0) = k1_xboole_0
    | k3_xboole_0(esk3_0,esk5_0) = k1_xboole_0
    | k2_zfmisc_1(esk3_0,esk4_0) != k2_zfmisc_1(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_22])).

cnf(c_0_39,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37])).

fof(c_0_40,plain,(
    ! [X5,X6] :
      ( ( ~ r1_xboole_0(X5,X6)
        | k3_xboole_0(X5,X6) = k1_xboole_0 )
      & ( k3_xboole_0(X5,X6) != k1_xboole_0
        | r1_xboole_0(X5,X6) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

cnf(c_0_41,negated_conjecture,
    ( k3_xboole_0(esk3_0,esk5_0) = k1_xboole_0
    | k3_xboole_0(k1_xboole_0,esk6_0) = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | k2_zfmisc_1(esk3_0,k1_xboole_0) != k2_zfmisc_1(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_42,negated_conjecture,
    ( k2_zfmisc_1(esk3_0,esk4_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_43,plain,(
    ! [X26,X27,X28,X29] :
      ( ( ~ r1_xboole_0(X26,X27)
        | r1_xboole_0(k2_zfmisc_1(X26,X28),k2_zfmisc_1(X27,X29)) )
      & ( ~ r1_xboole_0(X28,X29)
        | r1_xboole_0(k2_zfmisc_1(X26,X28),k2_zfmisc_1(X27,X29)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t127_zfmisc_1])])])).

cnf(c_0_44,plain,
    ( r1_xboole_0(X1,X2)
    | k3_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_45,negated_conjecture,
    ( k3_xboole_0(k1_xboole_0,esk6_0) = k1_xboole_0
    | k3_xboole_0(esk3_0,esk5_0) = k1_xboole_0
    | esk3_0 = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_41])).

cnf(c_0_46,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_47,negated_conjecture,
    ( k3_xboole_0(k2_zfmisc_1(esk3_0,k1_xboole_0),k2_zfmisc_1(esk5_0,esk6_0)) = k2_zfmisc_1(esk3_0,k1_xboole_0)
    | esk3_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_22,c_0_39])).

cnf(c_0_48,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | k2_zfmisc_1(esk3_0,k1_xboole_0) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_42,c_0_39])).

cnf(c_0_49,plain,
    ( r1_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_50,negated_conjecture,
    ( k3_xboole_0(k1_xboole_0,esk6_0) = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | r1_xboole_0(esk3_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_51,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | ~ r1_xboole_0(k2_zfmisc_1(esk3_0,k1_xboole_0),k2_zfmisc_1(esk5_0,esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_48])).

cnf(c_0_52,negated_conjecture,
    ( k3_xboole_0(k1_xboole_0,esk6_0) = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | r1_xboole_0(k2_zfmisc_1(esk3_0,X1),k2_zfmisc_1(esk5_0,X2)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_53,negated_conjecture,
    ( k3_xboole_0(k1_xboole_0,esk6_0) = k1_xboole_0
    | esk3_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_54,plain,
    ( r1_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X4,X2))
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_55,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | r1_xboole_0(k1_xboole_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_53])).

cnf(c_0_56,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | r1_xboole_0(k2_zfmisc_1(X1,k1_xboole_0),k2_zfmisc_1(X2,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_57,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | k2_zfmisc_1(X1,X2) != k2_zfmisc_1(k1_xboole_0,X3) ),
    inference(ef,[status(thm)],[c_0_14])).

cnf(c_0_58,negated_conjecture,
    ( esk3_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_51,c_0_56])).

cnf(c_0_59,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | k3_xboole_0(X3,X4) = k1_xboole_0
    | k3_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X4,X2)) != k2_zfmisc_1(k1_xboole_0,X5) ),
    inference(spm,[status(thm)],[c_0_57,c_0_15])).

cnf(c_0_60,negated_conjecture,
    ( k3_xboole_0(k2_zfmisc_1(k1_xboole_0,esk4_0),k2_zfmisc_1(esk5_0,esk6_0)) = k2_zfmisc_1(k1_xboole_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22,c_0_58]),c_0_58])).

cnf(c_0_61,negated_conjecture,
    ( k3_xboole_0(k1_xboole_0,esk5_0) = k1_xboole_0
    | k3_xboole_0(esk4_0,esk6_0) = k1_xboole_0
    | k2_zfmisc_1(k1_xboole_0,esk4_0) != k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_62,negated_conjecture,
    ( k3_xboole_0(esk4_0,esk6_0) = k1_xboole_0
    | k3_xboole_0(k1_xboole_0,esk5_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_61])).

cnf(c_0_63,negated_conjecture,
    ( k2_zfmisc_1(k1_xboole_0,esk4_0) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_42,c_0_58])).

cnf(c_0_64,negated_conjecture,
    ( k3_xboole_0(k1_xboole_0,esk5_0) = k1_xboole_0
    | r1_xboole_0(esk4_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_62])).

cnf(c_0_65,negated_conjecture,
    ( ~ r1_xboole_0(k2_zfmisc_1(k1_xboole_0,esk4_0),k2_zfmisc_1(esk5_0,esk6_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_60]),c_0_63])).

cnf(c_0_66,negated_conjecture,
    ( k3_xboole_0(k1_xboole_0,esk5_0) = k1_xboole_0
    | r1_xboole_0(k2_zfmisc_1(X1,esk4_0),k2_zfmisc_1(X2,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_64])).

cnf(c_0_67,negated_conjecture,
    ( k3_xboole_0(k1_xboole_0,esk5_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_68,negated_conjecture,
    ( r1_xboole_0(k1_xboole_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_67])).

cnf(c_0_69,negated_conjecture,
    ( r1_xboole_0(k2_zfmisc_1(k1_xboole_0,X1),k2_zfmisc_1(esk5_0,X2)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_68])).

cnf(c_0_70,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_65,c_0_69])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 16:52:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S053N
% 0.19/0.38  # and selection function HSelectMinInfpos.
% 0.19/0.38  #
% 0.19/0.38  # Preprocessing time       : 0.015 s
% 0.19/0.38  # Presaturation interreduction done
% 0.19/0.38  
% 0.19/0.38  # Proof found!
% 0.19/0.38  # SZS status Theorem
% 0.19/0.38  # SZS output start CNFRefutation
% 0.19/0.38  fof(t138_zfmisc_1, conjecture, ![X1, X2, X3, X4]:(r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))=>(k2_zfmisc_1(X1,X2)=k1_xboole_0|(r1_tarski(X1,X3)&r1_tarski(X2,X4)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t138_zfmisc_1)).
% 0.19/0.38  fof(t134_zfmisc_1, axiom, ![X1, X2, X3, X4]:(k2_zfmisc_1(X1,X2)=k2_zfmisc_1(X3,X4)=>(X1=k1_xboole_0|X2=k1_xboole_0|(X1=X3&X2=X4))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t134_zfmisc_1)).
% 0.19/0.38  fof(t123_zfmisc_1, axiom, ![X1, X2, X3, X4]:k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4))=k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_zfmisc_1)).
% 0.19/0.38  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.19/0.38  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.19/0.38  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.19/0.38  fof(t92_xboole_1, axiom, ![X1]:k5_xboole_0(X1,X1)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 0.19/0.38  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 0.19/0.38  fof(t127_zfmisc_1, axiom, ![X1, X2, X3, X4]:((r1_xboole_0(X1,X2)|r1_xboole_0(X3,X4))=>r1_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t127_zfmisc_1)).
% 0.19/0.38  fof(c_0_9, negated_conjecture, ~(![X1, X2, X3, X4]:(r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))=>(k2_zfmisc_1(X1,X2)=k1_xboole_0|(r1_tarski(X1,X3)&r1_tarski(X2,X4))))), inference(assume_negation,[status(cth)],[t138_zfmisc_1])).
% 0.19/0.38  fof(c_0_10, plain, ![X30, X31, X32, X33]:((X30=X32|(X30=k1_xboole_0|X31=k1_xboole_0)|k2_zfmisc_1(X30,X31)!=k2_zfmisc_1(X32,X33))&(X31=X33|(X30=k1_xboole_0|X31=k1_xboole_0)|k2_zfmisc_1(X30,X31)!=k2_zfmisc_1(X32,X33))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t134_zfmisc_1])])])).
% 0.19/0.38  fof(c_0_11, plain, ![X22, X23, X24, X25]:k2_zfmisc_1(k3_xboole_0(X22,X23),k3_xboole_0(X24,X25))=k3_xboole_0(k2_zfmisc_1(X22,X24),k2_zfmisc_1(X23,X25)), inference(variable_rename,[status(thm)],[t123_zfmisc_1])).
% 0.19/0.38  fof(c_0_12, plain, ![X19, X20]:(~r1_tarski(X19,X20)|k3_xboole_0(X19,X20)=X19), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.19/0.38  fof(c_0_13, negated_conjecture, (r1_tarski(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk5_0,esk6_0))&(k2_zfmisc_1(esk3_0,esk4_0)!=k1_xboole_0&(~r1_tarski(esk3_0,esk5_0)|~r1_tarski(esk4_0,esk6_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).
% 0.19/0.38  cnf(c_0_14, plain, (X1=X2|X1=k1_xboole_0|X3=k1_xboole_0|k2_zfmisc_1(X1,X3)!=k2_zfmisc_1(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.38  cnf(c_0_15, plain, (k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4))=k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.38  cnf(c_0_16, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.38  cnf(c_0_17, negated_conjecture, (r1_tarski(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk5_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.38  cnf(c_0_18, plain, (X1=X2|X3=k1_xboole_0|X1=k1_xboole_0|k2_zfmisc_1(X3,X1)!=k2_zfmisc_1(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.38  fof(c_0_19, plain, ![X15, X16]:((k4_xboole_0(X15,X16)!=k1_xboole_0|r1_tarski(X15,X16))&(~r1_tarski(X15,X16)|k4_xboole_0(X15,X16)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.19/0.38  fof(c_0_20, plain, ![X17, X18]:k4_xboole_0(X17,X18)=k5_xboole_0(X17,k3_xboole_0(X17,X18)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.19/0.38  cnf(c_0_21, plain, (X1=k3_xboole_0(X2,X3)|X1=k1_xboole_0|X4=k1_xboole_0|k2_zfmisc_1(X1,X4)!=k3_xboole_0(k2_zfmisc_1(X2,X5),k2_zfmisc_1(X3,X6))), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.19/0.38  cnf(c_0_22, negated_conjecture, (k3_xboole_0(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk5_0,esk6_0))=k2_zfmisc_1(esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.19/0.38  cnf(c_0_23, plain, (X1=k3_xboole_0(X2,X3)|X1=k1_xboole_0|X4=k1_xboole_0|k2_zfmisc_1(X4,X1)!=k3_xboole_0(k2_zfmisc_1(X5,X2),k2_zfmisc_1(X6,X3))), inference(spm,[status(thm)],[c_0_18, c_0_15])).
% 0.19/0.38  cnf(c_0_24, plain, (r1_tarski(X1,X2)|k4_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.38  cnf(c_0_25, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.38  cnf(c_0_26, negated_conjecture, (X1=k3_xboole_0(esk3_0,esk5_0)|X2=k1_xboole_0|X1=k1_xboole_0|k2_zfmisc_1(X1,X2)!=k2_zfmisc_1(esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.19/0.38  fof(c_0_27, plain, ![X21]:k5_xboole_0(X21,X21)=k1_xboole_0, inference(variable_rename,[status(thm)],[t92_xboole_1])).
% 0.19/0.38  cnf(c_0_28, negated_conjecture, (X1=k3_xboole_0(esk4_0,esk6_0)|X2=k1_xboole_0|X1=k1_xboole_0|k2_zfmisc_1(X2,X1)!=k2_zfmisc_1(esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_23, c_0_22])).
% 0.19/0.38  cnf(c_0_29, plain, (X1=k1_xboole_0|X2=k1_xboole_0|k2_zfmisc_1(X2,X1)!=k2_zfmisc_1(X3,k1_xboole_0)), inference(ef,[status(thm)],[c_0_18])).
% 0.19/0.38  cnf(c_0_30, plain, (r1_tarski(X1,X2)|k5_xboole_0(X1,k3_xboole_0(X1,X2))!=k1_xboole_0), inference(rw,[status(thm)],[c_0_24, c_0_25])).
% 0.19/0.38  cnf(c_0_31, negated_conjecture, (k3_xboole_0(esk3_0,esk5_0)=esk3_0|esk3_0=k1_xboole_0|esk4_0=k1_xboole_0), inference(er,[status(thm)],[c_0_26])).
% 0.19/0.38  cnf(c_0_32, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.38  cnf(c_0_33, negated_conjecture, (k3_xboole_0(esk4_0,esk6_0)=esk4_0|esk4_0=k1_xboole_0|esk3_0=k1_xboole_0), inference(er,[status(thm)],[c_0_28])).
% 0.19/0.38  cnf(c_0_34, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|k3_xboole_0(X3,X4)=k1_xboole_0|k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))!=k2_zfmisc_1(X5,k1_xboole_0)), inference(spm,[status(thm)],[c_0_29, c_0_15])).
% 0.19/0.38  cnf(c_0_35, negated_conjecture, (~r1_tarski(esk3_0,esk5_0)|~r1_tarski(esk4_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.38  cnf(c_0_36, negated_conjecture, (esk4_0=k1_xboole_0|esk3_0=k1_xboole_0|r1_tarski(esk3_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32])])).
% 0.19/0.38  cnf(c_0_37, negated_conjecture, (esk3_0=k1_xboole_0|esk4_0=k1_xboole_0|r1_tarski(esk4_0,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_33]), c_0_32])])).
% 0.19/0.38  cnf(c_0_38, negated_conjecture, (k3_xboole_0(esk4_0,esk6_0)=k1_xboole_0|k3_xboole_0(esk3_0,esk5_0)=k1_xboole_0|k2_zfmisc_1(esk3_0,esk4_0)!=k2_zfmisc_1(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_34, c_0_22])).
% 0.19/0.38  cnf(c_0_39, negated_conjecture, (esk3_0=k1_xboole_0|esk4_0=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_37])).
% 0.19/0.38  fof(c_0_40, plain, ![X5, X6]:((~r1_xboole_0(X5,X6)|k3_xboole_0(X5,X6)=k1_xboole_0)&(k3_xboole_0(X5,X6)!=k1_xboole_0|r1_xboole_0(X5,X6))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 0.19/0.38  cnf(c_0_41, negated_conjecture, (k3_xboole_0(esk3_0,esk5_0)=k1_xboole_0|k3_xboole_0(k1_xboole_0,esk6_0)=k1_xboole_0|esk3_0=k1_xboole_0|k2_zfmisc_1(esk3_0,k1_xboole_0)!=k2_zfmisc_1(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.19/0.38  cnf(c_0_42, negated_conjecture, (k2_zfmisc_1(esk3_0,esk4_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.38  fof(c_0_43, plain, ![X26, X27, X28, X29]:((~r1_xboole_0(X26,X27)|r1_xboole_0(k2_zfmisc_1(X26,X28),k2_zfmisc_1(X27,X29)))&(~r1_xboole_0(X28,X29)|r1_xboole_0(k2_zfmisc_1(X26,X28),k2_zfmisc_1(X27,X29)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t127_zfmisc_1])])])).
% 0.19/0.38  cnf(c_0_44, plain, (r1_xboole_0(X1,X2)|k3_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.19/0.38  cnf(c_0_45, negated_conjecture, (k3_xboole_0(k1_xboole_0,esk6_0)=k1_xboole_0|k3_xboole_0(esk3_0,esk5_0)=k1_xboole_0|esk3_0=k1_xboole_0), inference(er,[status(thm)],[c_0_41])).
% 0.19/0.38  cnf(c_0_46, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.19/0.38  cnf(c_0_47, negated_conjecture, (k3_xboole_0(k2_zfmisc_1(esk3_0,k1_xboole_0),k2_zfmisc_1(esk5_0,esk6_0))=k2_zfmisc_1(esk3_0,k1_xboole_0)|esk3_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_22, c_0_39])).
% 0.19/0.38  cnf(c_0_48, negated_conjecture, (esk3_0=k1_xboole_0|k2_zfmisc_1(esk3_0,k1_xboole_0)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_42, c_0_39])).
% 0.19/0.38  cnf(c_0_49, plain, (r1_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.19/0.38  cnf(c_0_50, negated_conjecture, (k3_xboole_0(k1_xboole_0,esk6_0)=k1_xboole_0|esk3_0=k1_xboole_0|r1_xboole_0(esk3_0,esk5_0)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.19/0.38  cnf(c_0_51, negated_conjecture, (esk3_0=k1_xboole_0|~r1_xboole_0(k2_zfmisc_1(esk3_0,k1_xboole_0),k2_zfmisc_1(esk5_0,esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_48])).
% 0.19/0.38  cnf(c_0_52, negated_conjecture, (k3_xboole_0(k1_xboole_0,esk6_0)=k1_xboole_0|esk3_0=k1_xboole_0|r1_xboole_0(k2_zfmisc_1(esk3_0,X1),k2_zfmisc_1(esk5_0,X2))), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.19/0.38  cnf(c_0_53, negated_conjecture, (k3_xboole_0(k1_xboole_0,esk6_0)=k1_xboole_0|esk3_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.19/0.38  cnf(c_0_54, plain, (r1_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X4,X2))|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.19/0.38  cnf(c_0_55, negated_conjecture, (esk3_0=k1_xboole_0|r1_xboole_0(k1_xboole_0,esk6_0)), inference(spm,[status(thm)],[c_0_44, c_0_53])).
% 0.19/0.38  cnf(c_0_56, negated_conjecture, (esk3_0=k1_xboole_0|r1_xboole_0(k2_zfmisc_1(X1,k1_xboole_0),k2_zfmisc_1(X2,esk6_0))), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.19/0.38  cnf(c_0_57, plain, (X1=k1_xboole_0|X2=k1_xboole_0|k2_zfmisc_1(X1,X2)!=k2_zfmisc_1(k1_xboole_0,X3)), inference(ef,[status(thm)],[c_0_14])).
% 0.19/0.38  cnf(c_0_58, negated_conjecture, (esk3_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_51, c_0_56])).
% 0.19/0.38  cnf(c_0_59, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|k3_xboole_0(X3,X4)=k1_xboole_0|k3_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X4,X2))!=k2_zfmisc_1(k1_xboole_0,X5)), inference(spm,[status(thm)],[c_0_57, c_0_15])).
% 0.19/0.38  cnf(c_0_60, negated_conjecture, (k3_xboole_0(k2_zfmisc_1(k1_xboole_0,esk4_0),k2_zfmisc_1(esk5_0,esk6_0))=k2_zfmisc_1(k1_xboole_0,esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22, c_0_58]), c_0_58])).
% 0.19/0.38  cnf(c_0_61, negated_conjecture, (k3_xboole_0(k1_xboole_0,esk5_0)=k1_xboole_0|k3_xboole_0(esk4_0,esk6_0)=k1_xboole_0|k2_zfmisc_1(k1_xboole_0,esk4_0)!=k2_zfmisc_1(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 0.19/0.38  cnf(c_0_62, negated_conjecture, (k3_xboole_0(esk4_0,esk6_0)=k1_xboole_0|k3_xboole_0(k1_xboole_0,esk5_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_61])).
% 0.19/0.38  cnf(c_0_63, negated_conjecture, (k2_zfmisc_1(k1_xboole_0,esk4_0)!=k1_xboole_0), inference(rw,[status(thm)],[c_0_42, c_0_58])).
% 0.19/0.38  cnf(c_0_64, negated_conjecture, (k3_xboole_0(k1_xboole_0,esk5_0)=k1_xboole_0|r1_xboole_0(esk4_0,esk6_0)), inference(spm,[status(thm)],[c_0_44, c_0_62])).
% 0.19/0.38  cnf(c_0_65, negated_conjecture, (~r1_xboole_0(k2_zfmisc_1(k1_xboole_0,esk4_0),k2_zfmisc_1(esk5_0,esk6_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_60]), c_0_63])).
% 0.19/0.38  cnf(c_0_66, negated_conjecture, (k3_xboole_0(k1_xboole_0,esk5_0)=k1_xboole_0|r1_xboole_0(k2_zfmisc_1(X1,esk4_0),k2_zfmisc_1(X2,esk6_0))), inference(spm,[status(thm)],[c_0_54, c_0_64])).
% 0.19/0.38  cnf(c_0_67, negated_conjecture, (k3_xboole_0(k1_xboole_0,esk5_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 0.19/0.38  cnf(c_0_68, negated_conjecture, (r1_xboole_0(k1_xboole_0,esk5_0)), inference(spm,[status(thm)],[c_0_44, c_0_67])).
% 0.19/0.38  cnf(c_0_69, negated_conjecture, (r1_xboole_0(k2_zfmisc_1(k1_xboole_0,X1),k2_zfmisc_1(esk5_0,X2))), inference(spm,[status(thm)],[c_0_49, c_0_68])).
% 0.19/0.38  cnf(c_0_70, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_65, c_0_69])]), ['proof']).
% 0.19/0.38  # SZS output end CNFRefutation
% 0.19/0.38  # Proof object total steps             : 71
% 0.19/0.38  # Proof object clause steps            : 52
% 0.19/0.38  # Proof object formula steps           : 19
% 0.19/0.38  # Proof object conjectures             : 37
% 0.19/0.38  # Proof object clause conjectures      : 34
% 0.19/0.38  # Proof object formula conjectures     : 3
% 0.19/0.38  # Proof object initial clauses used    : 14
% 0.19/0.38  # Proof object initial formulas used   : 9
% 0.19/0.38  # Proof object generating inferences   : 34
% 0.19/0.38  # Proof object simplifying inferences  : 13
% 0.19/0.38  # Training examples: 0 positive, 0 negative
% 0.19/0.38  # Parsed axioms                        : 11
% 0.19/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.38  # Initial clauses                      : 18
% 0.19/0.38  # Removed in clause preprocessing      : 1
% 0.19/0.38  # Initial clauses in saturation        : 17
% 0.19/0.38  # Processed clauses                    : 414
% 0.19/0.38  # ...of these trivial                  : 2
% 0.19/0.38  # ...subsumed                          : 171
% 0.19/0.38  # ...remaining for further processing  : 241
% 0.19/0.38  # Other redundant clauses eliminated   : 43
% 0.19/0.38  # Clauses deleted for lack of memory   : 0
% 0.19/0.38  # Backward-subsumed                    : 42
% 0.19/0.38  # Backward-rewritten                   : 114
% 0.19/0.38  # Generated clauses                    : 1625
% 0.19/0.38  # ...of the previous two non-trivial   : 1481
% 0.19/0.38  # Contextual simplify-reflections      : 7
% 0.19/0.38  # Paramodulations                      : 1409
% 0.19/0.38  # Factorizations                       : 154
% 0.19/0.38  # Equation resolutions                 : 62
% 0.19/0.38  # Propositional unsat checks           : 0
% 0.19/0.38  #    Propositional check models        : 0
% 0.19/0.38  #    Propositional check unsatisfiable : 0
% 0.19/0.38  #    Propositional clauses             : 0
% 0.19/0.38  #    Propositional clauses after purity: 0
% 0.19/0.38  #    Propositional unsat core size     : 0
% 0.19/0.38  #    Propositional preprocessing time  : 0.000
% 0.19/0.38  #    Propositional encoding time       : 0.000
% 0.19/0.38  #    Propositional solver time         : 0.000
% 0.19/0.38  #    Success case prop preproc time    : 0.000
% 0.19/0.38  #    Success case prop encoding time   : 0.000
% 0.19/0.38  #    Success case prop solver time     : 0.000
% 0.19/0.38  # Current number of processed clauses  : 68
% 0.19/0.38  #    Positive orientable unit clauses  : 11
% 0.19/0.38  #    Positive unorientable unit clauses: 0
% 0.19/0.38  #    Negative unit clauses             : 4
% 0.19/0.38  #    Non-unit-clauses                  : 53
% 0.19/0.38  # Current number of unprocessed clauses: 978
% 0.19/0.38  # ...number of literals in the above   : 2880
% 0.19/0.38  # Current number of archived formulas  : 0
% 0.19/0.38  # Current number of archived clauses   : 174
% 0.19/0.38  # Clause-clause subsumption calls (NU) : 2482
% 0.19/0.38  # Rec. Clause-clause subsumption calls : 2132
% 0.19/0.38  # Non-unit clause-clause subsumptions  : 188
% 0.19/0.38  # Unit Clause-clause subsumption calls : 50
% 0.19/0.38  # Rewrite failures with RHS unbound    : 0
% 0.19/0.38  # BW rewrite match attempts            : 11
% 0.19/0.38  # BW rewrite match successes           : 5
% 0.19/0.38  # Condensation attempts                : 0
% 0.19/0.38  # Condensation successes               : 0
% 0.19/0.38  # Termbank termtop insertions          : 29592
% 0.19/0.38  
% 0.19/0.38  # -------------------------------------------------
% 0.19/0.38  # User time                : 0.041 s
% 0.19/0.38  # System time              : 0.000 s
% 0.19/0.38  # Total time               : 0.041 s
% 0.19/0.38  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
