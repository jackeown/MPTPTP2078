%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:44:09 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 456 expanded)
%              Number of clauses        :   48 ( 213 expanded)
%              Number of leaves         :   10 ( 117 expanded)
%              Depth                    :   16
%              Number of atoms          :  147 ( 981 expanded)
%              Number of equality atoms :   57 ( 359 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t9_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_tarski(k2_xboole_0(X1,X3),k2_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_xboole_1)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(t126_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] : k4_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4)) = k2_xboole_0(k2_zfmisc_1(k4_xboole_0(X1,X3),X2),k2_zfmisc_1(X1,k4_xboole_0(X2,X4))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t126_zfmisc_1)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(t37_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_xboole_1)).

fof(t138_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))
     => ( k2_zfmisc_1(X1,X2) = k1_xboole_0
        | ( r1_tarski(X1,X3)
          & r1_tarski(X2,X4) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_zfmisc_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t117_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( X1 != k1_xboole_0
        & ( r1_tarski(k2_zfmisc_1(X2,X1),k2_zfmisc_1(X3,X1))
          | r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)) )
        & ~ r1_tarski(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_zfmisc_1)).

fof(c_0_10,plain,(
    ! [X14,X15,X16] :
      ( ~ r1_tarski(X14,X15)
      | r1_tarski(k2_xboole_0(X14,X16),k2_xboole_0(X15,X16)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_xboole_1])])).

fof(c_0_11,plain,(
    ! [X7,X8] :
      ( ~ r1_tarski(X7,X8)
      | k2_xboole_0(X7,X8) = X8 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_12,plain,
    ( r1_tarski(k2_xboole_0(X1,X3),k2_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_13,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_14,plain,(
    ! [X9] : r1_tarski(k1_xboole_0,X9) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

fof(c_0_15,plain,(
    ! [X12,X13] : r1_tarski(X12,k2_xboole_0(X12,X13)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

fof(c_0_16,plain,(
    ! [X22,X23,X24,X25] : k4_xboole_0(k2_zfmisc_1(X22,X23),k2_zfmisc_1(X24,X25)) = k2_xboole_0(k2_zfmisc_1(k4_xboole_0(X22,X24),X23),k2_zfmisc_1(X22,k4_xboole_0(X23,X25))) ),
    inference(variable_rename,[status(thm)],[t126_zfmisc_1])).

cnf(c_0_17,plain,
    ( r1_tarski(k2_xboole_0(X1,X2),X2)
    | ~ r1_tarski(X1,X3)
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_18,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_19,plain,(
    ! [X17,X18] :
      ( ( k2_zfmisc_1(X17,X18) != k1_xboole_0
        | X17 = k1_xboole_0
        | X18 = k1_xboole_0 )
      & ( X17 != k1_xboole_0
        | k2_zfmisc_1(X17,X18) = k1_xboole_0 )
      & ( X18 != k1_xboole_0
        | k2_zfmisc_1(X17,X18) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_20,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( k4_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4)) = k2_xboole_0(k2_zfmisc_1(k4_xboole_0(X1,X3),X2),k2_zfmisc_1(X1,k4_xboole_0(X2,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_22,plain,(
    ! [X10,X11] :
      ( ( k4_xboole_0(X10,X11) != k1_xboole_0
        | r1_tarski(X10,X11) )
      & ( ~ r1_tarski(X10,X11)
        | k4_xboole_0(X10,X11) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_xboole_1])])).

fof(c_0_23,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))
       => ( k2_zfmisc_1(X1,X2) = k1_xboole_0
          | ( r1_tarski(X1,X3)
            & r1_tarski(X2,X4) ) ) ) ),
    inference(assume_negation,[status(cth)],[t138_zfmisc_1])).

fof(c_0_24,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | X5 != X6 )
      & ( r1_tarski(X6,X5)
        | X5 != X6 )
      & ( ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X5)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_25,plain,
    ( r1_tarski(k2_xboole_0(k1_xboole_0,X1),X1)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_26,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,plain,
    ( r1_tarski(k2_zfmisc_1(k4_xboole_0(X1,X2),X3),k4_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_28,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_29,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk3_0,esk4_0))
    & k2_zfmisc_1(esk1_0,esk2_0) != k1_xboole_0
    & ( ~ r1_tarski(esk1_0,esk3_0)
      | ~ r1_tarski(esk2_0,esk4_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_23])])])).

cnf(c_0_30,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,plain,
    ( r1_tarski(k2_xboole_0(k1_xboole_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_18])).

cnf(c_0_32,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X1))
    | ~ r1_tarski(X3,X2)
    | ~ r1_tarski(X3,X1) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_33,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_26])).

cnf(c_0_34,plain,
    ( r1_tarski(k2_zfmisc_1(k4_xboole_0(X1,X2),X3),k1_xboole_0)
    | ~ r1_tarski(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_35,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_36,plain,
    ( k2_xboole_0(k1_xboole_0,X1) = X1
    | ~ r1_tarski(X1,k2_xboole_0(k1_xboole_0,X1)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_37,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_18]),c_0_18])])).

fof(c_0_38,plain,(
    ! [X19,X20,X21] :
      ( ( ~ r1_tarski(k2_zfmisc_1(X20,X19),k2_zfmisc_1(X21,X19))
        | X19 = k1_xboole_0
        | r1_tarski(X20,X21) )
      & ( ~ r1_tarski(k2_zfmisc_1(X19,X20),k2_zfmisc_1(X19,X21))
        | X19 = k1_xboole_0
        | r1_tarski(X20,X21) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t117_zfmisc_1])])])])).

cnf(c_0_39,plain,
    ( r1_tarski(X1,X2)
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_40,plain,
    ( k2_xboole_0(k2_zfmisc_1(k4_xboole_0(X1,X2),X3),k1_xboole_0) = k4_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))
    | ~ r1_tarski(X3,X4) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_28]),c_0_33])).

cnf(c_0_41,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(k4_xboole_0(esk1_0,esk3_0),esk2_0),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_42,plain,
    ( k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_37])])).

cnf(c_0_43,plain,
    ( X1 = k1_xboole_0
    | r1_tarski(X2,X3)
    | ~ r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_44,plain,
    ( r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))
    | k2_xboole_0(k2_zfmisc_1(k4_xboole_0(X1,X3),X2),k1_xboole_0) != k1_xboole_0
    | ~ r1_tarski(X2,X4) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_45,negated_conjecture,
    ( k2_zfmisc_1(k4_xboole_0(esk1_0,esk3_0),esk2_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_41]),c_0_18])])).

cnf(c_0_46,plain,
    ( r1_tarski(k2_xboole_0(X1,X2),X2)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_12,c_0_42])).

cnf(c_0_47,plain,
    ( X1 = k1_xboole_0
    | r1_tarski(X2,k1_xboole_0)
    | ~ r1_tarski(k2_zfmisc_1(X1,X2),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_33])).

cnf(c_0_48,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_49,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk3_0,X1))
    | ~ r1_tarski(esk2_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_42])])).

cnf(c_0_50,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_46]),c_0_37])])).

cnf(c_0_51,negated_conjecture,
    ( k4_xboole_0(esk1_0,esk3_0) = k1_xboole_0
    | r1_tarski(esk2_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_45]),c_0_18])])).

cnf(c_0_52,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_48])).

cnf(c_0_53,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(esk1_0,esk2_0),k1_xboole_0)
    | ~ r1_tarski(esk2_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_33])).

cnf(c_0_54,negated_conjecture,
    ( k2_zfmisc_1(esk1_0,esk2_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_55,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_50])).

cnf(c_0_56,negated_conjecture,
    ( r1_tarski(esk2_0,k1_xboole_0)
    | r1_tarski(esk1_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_51])).

cnf(c_0_57,plain,
    ( k4_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4)) = k2_zfmisc_1(X1,k4_xboole_0(X2,X4))
    | ~ r1_tarski(X1,X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_28]),c_0_52]),c_0_42])).

cnf(c_0_58,negated_conjecture,
    ( ~ r1_tarski(esk2_0,k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_53]),c_0_18])]),c_0_54])).

cnf(c_0_59,negated_conjecture,
    ( r1_tarski(esk1_0,esk3_0)
    | r1_tarski(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_60,plain,
    ( k2_zfmisc_1(X1,k4_xboole_0(X2,X3)) = k1_xboole_0
    | ~ r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X4,X3))
    | ~ r1_tarski(X1,X4) ),
    inference(spm,[status(thm)],[c_0_28,c_0_57])).

cnf(c_0_61,negated_conjecture,
    ( r1_tarski(esk1_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_62,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | k2_zfmisc_1(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_63,negated_conjecture,
    ( k2_zfmisc_1(esk1_0,k4_xboole_0(esk2_0,esk4_0)) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_35]),c_0_61])])).

cnf(c_0_64,negated_conjecture,
    ( ~ r1_tarski(esk1_0,esk3_0)
    | ~ r1_tarski(esk2_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_65,negated_conjecture,
    ( k4_xboole_0(esk2_0,esk4_0) = k1_xboole_0
    | esk1_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_66,negated_conjecture,
    ( ~ r1_tarski(esk2_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_64,c_0_61])])).

cnf(c_0_67,negated_conjecture,
    ( esk1_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_65]),c_0_66])).

cnf(c_0_68,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54,c_0_67]),c_0_52])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:13:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.44  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.19/0.44  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.44  #
% 0.19/0.44  # Preprocessing time       : 0.027 s
% 0.19/0.44  # Presaturation interreduction done
% 0.19/0.44  
% 0.19/0.44  # Proof found!
% 0.19/0.44  # SZS status Theorem
% 0.19/0.44  # SZS output start CNFRefutation
% 0.19/0.44  fof(t9_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_tarski(k2_xboole_0(X1,X3),k2_xboole_0(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_xboole_1)).
% 0.19/0.44  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.19/0.44  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.19/0.44  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.19/0.44  fof(t126_zfmisc_1, axiom, ![X1, X2, X3, X4]:k4_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))=k2_xboole_0(k2_zfmisc_1(k4_xboole_0(X1,X3),X2),k2_zfmisc_1(X1,k4_xboole_0(X2,X4))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t126_zfmisc_1)).
% 0.19/0.44  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.19/0.44  fof(t37_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_xboole_1)).
% 0.19/0.44  fof(t138_zfmisc_1, conjecture, ![X1, X2, X3, X4]:(r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))=>(k2_zfmisc_1(X1,X2)=k1_xboole_0|(r1_tarski(X1,X3)&r1_tarski(X2,X4)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t138_zfmisc_1)).
% 0.19/0.44  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.19/0.44  fof(t117_zfmisc_1, axiom, ![X1, X2, X3]:~(((X1!=k1_xboole_0&(r1_tarski(k2_zfmisc_1(X2,X1),k2_zfmisc_1(X3,X1))|r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))))&~(r1_tarski(X2,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t117_zfmisc_1)).
% 0.19/0.44  fof(c_0_10, plain, ![X14, X15, X16]:(~r1_tarski(X14,X15)|r1_tarski(k2_xboole_0(X14,X16),k2_xboole_0(X15,X16))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_xboole_1])])).
% 0.19/0.44  fof(c_0_11, plain, ![X7, X8]:(~r1_tarski(X7,X8)|k2_xboole_0(X7,X8)=X8), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.19/0.44  cnf(c_0_12, plain, (r1_tarski(k2_xboole_0(X1,X3),k2_xboole_0(X2,X3))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.44  cnf(c_0_13, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.44  fof(c_0_14, plain, ![X9]:r1_tarski(k1_xboole_0,X9), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.19/0.44  fof(c_0_15, plain, ![X12, X13]:r1_tarski(X12,k2_xboole_0(X12,X13)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.19/0.44  fof(c_0_16, plain, ![X22, X23, X24, X25]:k4_xboole_0(k2_zfmisc_1(X22,X23),k2_zfmisc_1(X24,X25))=k2_xboole_0(k2_zfmisc_1(k4_xboole_0(X22,X24),X23),k2_zfmisc_1(X22,k4_xboole_0(X23,X25))), inference(variable_rename,[status(thm)],[t126_zfmisc_1])).
% 0.19/0.44  cnf(c_0_17, plain, (r1_tarski(k2_xboole_0(X1,X2),X2)|~r1_tarski(X1,X3)|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.19/0.44  cnf(c_0_18, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.44  fof(c_0_19, plain, ![X17, X18]:((k2_zfmisc_1(X17,X18)!=k1_xboole_0|(X17=k1_xboole_0|X18=k1_xboole_0))&((X17!=k1_xboole_0|k2_zfmisc_1(X17,X18)=k1_xboole_0)&(X18!=k1_xboole_0|k2_zfmisc_1(X17,X18)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.19/0.44  cnf(c_0_20, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.44  cnf(c_0_21, plain, (k4_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))=k2_xboole_0(k2_zfmisc_1(k4_xboole_0(X1,X3),X2),k2_zfmisc_1(X1,k4_xboole_0(X2,X4)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.44  fof(c_0_22, plain, ![X10, X11]:((k4_xboole_0(X10,X11)!=k1_xboole_0|r1_tarski(X10,X11))&(~r1_tarski(X10,X11)|k4_xboole_0(X10,X11)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_xboole_1])])).
% 0.19/0.44  fof(c_0_23, negated_conjecture, ~(![X1, X2, X3, X4]:(r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))=>(k2_zfmisc_1(X1,X2)=k1_xboole_0|(r1_tarski(X1,X3)&r1_tarski(X2,X4))))), inference(assume_negation,[status(cth)],[t138_zfmisc_1])).
% 0.19/0.44  fof(c_0_24, plain, ![X5, X6]:(((r1_tarski(X5,X6)|X5!=X6)&(r1_tarski(X6,X5)|X5!=X6))&(~r1_tarski(X5,X6)|~r1_tarski(X6,X5)|X5=X6)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.19/0.44  cnf(c_0_25, plain, (r1_tarski(k2_xboole_0(k1_xboole_0,X1),X1)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.19/0.44  cnf(c_0_26, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.44  cnf(c_0_27, plain, (r1_tarski(k2_zfmisc_1(k4_xboole_0(X1,X2),X3),k4_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)))), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.19/0.44  cnf(c_0_28, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.44  fof(c_0_29, negated_conjecture, (r1_tarski(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk3_0,esk4_0))&(k2_zfmisc_1(esk1_0,esk2_0)!=k1_xboole_0&(~r1_tarski(esk1_0,esk3_0)|~r1_tarski(esk2_0,esk4_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_23])])])).
% 0.19/0.44  cnf(c_0_30, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.44  cnf(c_0_31, plain, (r1_tarski(k2_xboole_0(k1_xboole_0,X1),X1)), inference(spm,[status(thm)],[c_0_25, c_0_18])).
% 0.19/0.44  cnf(c_0_32, plain, (r1_tarski(X1,k2_xboole_0(X2,X1))|~r1_tarski(X3,X2)|~r1_tarski(X3,X1)), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.19/0.44  cnf(c_0_33, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_26])).
% 0.19/0.44  cnf(c_0_34, plain, (r1_tarski(k2_zfmisc_1(k4_xboole_0(X1,X2),X3),k1_xboole_0)|~r1_tarski(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.19/0.44  cnf(c_0_35, negated_conjecture, (r1_tarski(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk3_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.44  cnf(c_0_36, plain, (k2_xboole_0(k1_xboole_0,X1)=X1|~r1_tarski(X1,k2_xboole_0(k1_xboole_0,X1))), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.19/0.44  cnf(c_0_37, plain, (r1_tarski(X1,k2_xboole_0(X2,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_18]), c_0_18])])).
% 0.19/0.44  fof(c_0_38, plain, ![X19, X20, X21]:((~r1_tarski(k2_zfmisc_1(X20,X19),k2_zfmisc_1(X21,X19))|X19=k1_xboole_0|r1_tarski(X20,X21))&(~r1_tarski(k2_zfmisc_1(X19,X20),k2_zfmisc_1(X19,X21))|X19=k1_xboole_0|r1_tarski(X20,X21))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t117_zfmisc_1])])])])).
% 0.19/0.44  cnf(c_0_39, plain, (r1_tarski(X1,X2)|k4_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.44  cnf(c_0_40, plain, (k2_xboole_0(k2_zfmisc_1(k4_xboole_0(X1,X2),X3),k1_xboole_0)=k4_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))|~r1_tarski(X3,X4)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_28]), c_0_33])).
% 0.19/0.44  cnf(c_0_41, negated_conjecture, (r1_tarski(k2_zfmisc_1(k4_xboole_0(esk1_0,esk3_0),esk2_0),k1_xboole_0)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.19/0.44  cnf(c_0_42, plain, (k2_xboole_0(k1_xboole_0,X1)=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_36, c_0_37])])).
% 0.19/0.44  cnf(c_0_43, plain, (X1=k1_xboole_0|r1_tarski(X2,X3)|~r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.19/0.44  cnf(c_0_44, plain, (r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))|k2_xboole_0(k2_zfmisc_1(k4_xboole_0(X1,X3),X2),k1_xboole_0)!=k1_xboole_0|~r1_tarski(X2,X4)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.19/0.44  cnf(c_0_45, negated_conjecture, (k2_zfmisc_1(k4_xboole_0(esk1_0,esk3_0),esk2_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_41]), c_0_18])])).
% 0.19/0.44  cnf(c_0_46, plain, (r1_tarski(k2_xboole_0(X1,X2),X2)|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_12, c_0_42])).
% 0.19/0.44  cnf(c_0_47, plain, (X1=k1_xboole_0|r1_tarski(X2,k1_xboole_0)|~r1_tarski(k2_zfmisc_1(X1,X2),k1_xboole_0)), inference(spm,[status(thm)],[c_0_43, c_0_33])).
% 0.19/0.44  cnf(c_0_48, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.44  cnf(c_0_49, negated_conjecture, (r1_tarski(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk3_0,X1))|~r1_tarski(esk2_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_42])])).
% 0.19/0.44  cnf(c_0_50, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_46]), c_0_37])])).
% 0.19/0.44  cnf(c_0_51, negated_conjecture, (k4_xboole_0(esk1_0,esk3_0)=k1_xboole_0|r1_tarski(esk2_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_45]), c_0_18])])).
% 0.19/0.44  cnf(c_0_52, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(er,[status(thm)],[c_0_48])).
% 0.19/0.44  cnf(c_0_53, negated_conjecture, (r1_tarski(k2_zfmisc_1(esk1_0,esk2_0),k1_xboole_0)|~r1_tarski(esk2_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_49, c_0_33])).
% 0.19/0.44  cnf(c_0_54, negated_conjecture, (k2_zfmisc_1(esk1_0,esk2_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.44  cnf(c_0_55, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_20, c_0_50])).
% 0.19/0.44  cnf(c_0_56, negated_conjecture, (r1_tarski(esk2_0,k1_xboole_0)|r1_tarski(esk1_0,esk3_0)), inference(spm,[status(thm)],[c_0_39, c_0_51])).
% 0.19/0.44  cnf(c_0_57, plain, (k4_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))=k2_zfmisc_1(X1,k4_xboole_0(X2,X4))|~r1_tarski(X1,X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_28]), c_0_52]), c_0_42])).
% 0.19/0.44  cnf(c_0_58, negated_conjecture, (~r1_tarski(esk2_0,k1_xboole_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_53]), c_0_18])]), c_0_54])).
% 0.19/0.44  cnf(c_0_59, negated_conjecture, (r1_tarski(esk1_0,esk3_0)|r1_tarski(esk2_0,X1)), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.19/0.44  cnf(c_0_60, plain, (k2_zfmisc_1(X1,k4_xboole_0(X2,X3))=k1_xboole_0|~r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X4,X3))|~r1_tarski(X1,X4)), inference(spm,[status(thm)],[c_0_28, c_0_57])).
% 0.19/0.44  cnf(c_0_61, negated_conjecture, (r1_tarski(esk1_0,esk3_0)), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.19/0.44  cnf(c_0_62, plain, (X1=k1_xboole_0|X2=k1_xboole_0|k2_zfmisc_1(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.44  cnf(c_0_63, negated_conjecture, (k2_zfmisc_1(esk1_0,k4_xboole_0(esk2_0,esk4_0))=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_35]), c_0_61])])).
% 0.19/0.44  cnf(c_0_64, negated_conjecture, (~r1_tarski(esk1_0,esk3_0)|~r1_tarski(esk2_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.44  cnf(c_0_65, negated_conjecture, (k4_xboole_0(esk2_0,esk4_0)=k1_xboole_0|esk1_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 0.19/0.44  cnf(c_0_66, negated_conjecture, (~r1_tarski(esk2_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_64, c_0_61])])).
% 0.19/0.44  cnf(c_0_67, negated_conjecture, (esk1_0=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_65]), c_0_66])).
% 0.19/0.44  cnf(c_0_68, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54, c_0_67]), c_0_52])]), ['proof']).
% 0.19/0.44  # SZS output end CNFRefutation
% 0.19/0.44  # Proof object total steps             : 69
% 0.19/0.44  # Proof object clause steps            : 48
% 0.19/0.44  # Proof object formula steps           : 21
% 0.19/0.44  # Proof object conjectures             : 20
% 0.19/0.44  # Proof object clause conjectures      : 17
% 0.19/0.44  # Proof object formula conjectures     : 3
% 0.19/0.44  # Proof object initial clauses used    : 15
% 0.19/0.44  # Proof object initial formulas used   : 10
% 0.19/0.44  # Proof object generating inferences   : 28
% 0.19/0.44  # Proof object simplifying inferences  : 28
% 0.19/0.44  # Training examples: 0 positive, 0 negative
% 0.19/0.44  # Parsed axioms                        : 10
% 0.19/0.44  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.44  # Initial clauses                      : 18
% 0.19/0.44  # Removed in clause preprocessing      : 0
% 0.19/0.44  # Initial clauses in saturation        : 18
% 0.19/0.44  # Processed clauses                    : 783
% 0.19/0.44  # ...of these trivial                  : 18
% 0.19/0.44  # ...subsumed                          : 488
% 0.19/0.44  # ...remaining for further processing  : 277
% 0.19/0.44  # Other redundant clauses eliminated   : 5
% 0.19/0.44  # Clauses deleted for lack of memory   : 0
% 0.19/0.44  # Backward-subsumed                    : 22
% 0.19/0.44  # Backward-rewritten                   : 141
% 0.19/0.44  # Generated clauses                    : 4265
% 0.19/0.44  # ...of the previous two non-trivial   : 3199
% 0.19/0.44  # Contextual simplify-reflections      : 1
% 0.19/0.44  # Paramodulations                      : 4256
% 0.19/0.44  # Factorizations                       : 3
% 0.19/0.44  # Equation resolutions                 : 5
% 0.19/0.44  # Propositional unsat checks           : 0
% 0.19/0.44  #    Propositional check models        : 0
% 0.19/0.44  #    Propositional check unsatisfiable : 0
% 0.19/0.44  #    Propositional clauses             : 0
% 0.19/0.44  #    Propositional clauses after purity: 0
% 0.19/0.44  #    Propositional unsat core size     : 0
% 0.19/0.44  #    Propositional preprocessing time  : 0.000
% 0.19/0.44  #    Propositional encoding time       : 0.000
% 0.19/0.44  #    Propositional solver time         : 0.000
% 0.19/0.44  #    Success case prop preproc time    : 0.000
% 0.19/0.44  #    Success case prop encoding time   : 0.000
% 0.19/0.44  #    Success case prop solver time     : 0.000
% 0.19/0.44  # Current number of processed clauses  : 92
% 0.19/0.44  #    Positive orientable unit clauses  : 20
% 0.19/0.44  #    Positive unorientable unit clauses: 0
% 0.19/0.44  #    Negative unit clauses             : 3
% 0.19/0.44  #    Non-unit-clauses                  : 69
% 0.19/0.44  # Current number of unprocessed clauses: 2279
% 0.19/0.44  # ...number of literals in the above   : 6491
% 0.19/0.44  # Current number of archived formulas  : 0
% 0.19/0.44  # Current number of archived clauses   : 181
% 0.19/0.44  # Clause-clause subsumption calls (NU) : 4707
% 0.19/0.44  # Rec. Clause-clause subsumption calls : 4584
% 0.19/0.44  # Non-unit clause-clause subsumptions  : 466
% 0.19/0.44  # Unit Clause-clause subsumption calls : 119
% 0.19/0.44  # Rewrite failures with RHS unbound    : 0
% 0.19/0.44  # BW rewrite match attempts            : 77
% 0.19/0.44  # BW rewrite match successes           : 25
% 0.19/0.44  # Condensation attempts                : 0
% 0.19/0.44  # Condensation successes               : 0
% 0.19/0.44  # Termbank termtop insertions          : 54060
% 0.19/0.44  
% 0.19/0.44  # -------------------------------------------------
% 0.19/0.44  # User time                : 0.091 s
% 0.19/0.44  # System time              : 0.009 s
% 0.19/0.44  # Total time               : 0.101 s
% 0.19/0.44  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
