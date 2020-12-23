%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:38:59 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   90 (15758 expanded)
%              Number of clauses        :   63 (6208 expanded)
%              Number of leaves         :   13 (4659 expanded)
%              Depth                    :   32
%              Number of atoms          :  195 (24778 expanded)
%              Number of equality atoms :  138 (20093 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :   13 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t28_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ~ ( r1_tarski(k2_tarski(X1,X2),k2_tarski(X3,X4))
        & X1 != X3
        & X1 != X4 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_zfmisc_1)).

fof(l45_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k2_tarski(X2,X3))
    <=> ~ ( X1 != k1_xboole_0
          & X1 != k1_tarski(X2)
          & X1 != k1_tarski(X3)
          & X1 != k2_tarski(X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(t25_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( r1_tarski(k1_tarski(X1),k2_tarski(X2,X3))
        & X1 != X2
        & X1 != X3 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_zfmisc_1)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(t10_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_tarski(X1,k2_xboole_0(X3,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ~ ( r1_tarski(k2_tarski(X1,X2),k2_tarski(X3,X4))
          & X1 != X3
          & X1 != X4 ) ),
    inference(assume_negation,[status(cth)],[t28_zfmisc_1])).

fof(c_0_14,plain,(
    ! [X27,X28,X29] :
      ( ( ~ r1_tarski(X27,k2_tarski(X28,X29))
        | X27 = k1_xboole_0
        | X27 = k1_tarski(X28)
        | X27 = k1_tarski(X29)
        | X27 = k2_tarski(X28,X29) )
      & ( X27 != k1_xboole_0
        | r1_tarski(X27,k2_tarski(X28,X29)) )
      & ( X27 != k1_tarski(X28)
        | r1_tarski(X27,k2_tarski(X28,X29)) )
      & ( X27 != k1_tarski(X29)
        | r1_tarski(X27,k2_tarski(X28,X29)) )
      & ( X27 != k2_tarski(X28,X29)
        | r1_tarski(X27,k2_tarski(X28,X29)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l45_zfmisc_1])])])).

fof(c_0_15,plain,(
    ! [X17] : k2_tarski(X17,X17) = k1_tarski(X17) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_16,plain,(
    ! [X18,X19] : k1_enumset1(X18,X18,X19) = k2_tarski(X18,X19) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_17,plain,(
    ! [X20,X21,X22] : k2_enumset1(X20,X20,X21,X22) = k1_enumset1(X20,X21,X22) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_18,plain,(
    ! [X23,X24,X25,X26] : k3_enumset1(X23,X23,X24,X25,X26) = k2_enumset1(X23,X24,X25,X26) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_19,negated_conjecture,
    ( r1_tarski(k2_tarski(esk1_0,esk2_0),k2_tarski(esk3_0,esk4_0))
    & esk1_0 != esk3_0
    & esk1_0 != esk4_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).

cnf(c_0_20,plain,
    ( r1_tarski(X1,k2_tarski(X2,X3))
    | X1 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( X1 = k1_xboole_0
    | X1 = k1_tarski(X2)
    | X1 = k1_tarski(X3)
    | X1 = k2_tarski(X2,X3)
    | ~ r1_tarski(X1,k2_tarski(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_26,negated_conjecture,
    ( r1_tarski(k2_tarski(esk1_0,esk2_0),k2_tarski(esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_27,plain,(
    ! [X30,X31,X32] :
      ( ~ r1_tarski(k1_tarski(X30),k2_tarski(X31,X32))
      | X30 = X31
      | X30 = X32 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_zfmisc_1])])).

cnf(c_0_28,plain,
    ( r1_tarski(X1,k3_enumset1(X2,X2,X2,X2,X3))
    | X1 != k3_enumset1(X2,X2,X2,X2,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20,c_0_21]),c_0_22]),c_0_22]),c_0_23]),c_0_23]),c_0_24]),c_0_24])).

cnf(c_0_29,plain,
    ( X1 = k1_xboole_0
    | X1 = k3_enumset1(X3,X3,X3,X3,X3)
    | X1 = k3_enumset1(X2,X2,X2,X2,X3)
    | X1 = k3_enumset1(X2,X2,X2,X2,X2)
    | ~ r1_tarski(X1,k3_enumset1(X2,X2,X2,X2,X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_21]),c_0_21]),c_0_22]),c_0_22]),c_0_22]),c_0_22]),c_0_23]),c_0_23]),c_0_23]),c_0_23]),c_0_24]),c_0_24]),c_0_24]),c_0_24])).

cnf(c_0_30,negated_conjecture,
    ( r1_tarski(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_22]),c_0_22]),c_0_23]),c_0_23]),c_0_24]),c_0_24])).

cnf(c_0_31,plain,
    ( X1 = X2
    | X1 = X3
    | ~ r1_tarski(k1_tarski(X1),k2_tarski(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_32,plain,
    ( r1_tarski(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X1,X1,X1,X1,X2)) ),
    inference(er,[status(thm)],[c_0_28])).

cnf(c_0_33,negated_conjecture,
    ( k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0) = k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0)
    | k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0) = k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0)
    | k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0) = k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0)
    | k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_34,plain,
    ( X1 = X3
    | X1 = X2
    | ~ r1_tarski(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X2,X2,X2,X2,X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_21]),c_0_22]),c_0_22]),c_0_23]),c_0_23]),c_0_24]),c_0_24])).

cnf(c_0_35,negated_conjecture,
    ( k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0) = k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0)
    | k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0) = k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0)
    | k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0) = k1_xboole_0
    | r1_tarski(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_36,negated_conjecture,
    ( esk1_0 != esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_37,negated_conjecture,
    ( k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0) = k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0)
    | k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0) = k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0)
    | k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0) = k1_xboole_0
    | esk2_0 = esk4_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36])).

fof(c_0_38,plain,(
    ! [X12] : k2_xboole_0(X12,k1_xboole_0) = X12 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

fof(c_0_39,plain,(
    ! [X5,X6] : k2_xboole_0(X5,X6) = k2_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_40,negated_conjecture,
    ( k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0) = k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0)
    | k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0) = k1_xboole_0
    | esk2_0 = esk4_0
    | X1 = esk3_0
    | X1 = esk4_0
    | ~ r1_tarski(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_37])).

cnf(c_0_41,negated_conjecture,
    ( esk1_0 != esk3_0 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_42,plain,(
    ! [X13,X14] : k2_xboole_0(X13,k4_xboole_0(X14,X13)) = k2_xboole_0(X13,X14) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

cnf(c_0_43,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_44,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_45,negated_conjecture,
    ( k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0) = k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0)
    | k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0) = k1_xboole_0
    | esk2_0 = esk4_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_32]),c_0_41]),c_0_36])).

fof(c_0_46,plain,(
    ! [X7,X8] :
      ( ( k4_xboole_0(X7,X8) != k1_xboole_0
        | r1_tarski(X7,X8) )
      & ( ~ r1_tarski(X7,X8)
        | k4_xboole_0(X7,X8) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

cnf(c_0_47,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_48,plain,
    ( k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_49,negated_conjecture,
    ( k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0) = k1_xboole_0
    | esk2_0 = esk4_0
    | X1 = esk3_0
    | ~ r1_tarski(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_45])).

fof(c_0_50,plain,(
    ! [X9,X10,X11] :
      ( ~ r1_tarski(X9,X10)
      | r1_tarski(X9,k2_xboole_0(X11,X10)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_xboole_1])])).

fof(c_0_51,plain,(
    ! [X15,X16] : r1_tarski(X15,k2_xboole_0(X15,X16)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

cnf(c_0_52,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_53,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_48])).

cnf(c_0_54,negated_conjecture,
    ( k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0) = k1_xboole_0
    | esk2_0 = esk4_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_32]),c_0_41])).

cnf(c_0_55,plain,
    ( r1_tarski(X1,k2_xboole_0(X3,X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_56,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_57,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_58,negated_conjecture,
    ( esk2_0 = esk4_0
    | r1_tarski(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_54])).

cnf(c_0_59,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_55,c_0_43])).

cnf(c_0_60,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_56,c_0_43])).

cnf(c_0_61,negated_conjecture,
    ( k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0) = k1_xboole_0
    | esk2_0 = esk4_0 ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_62,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_63,negated_conjecture,
    ( esk2_0 = esk4_0
    | esk1_0 = X1
    | esk1_0 = X2 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_61]),c_0_62])])).

cnf(c_0_64,negated_conjecture,
    ( esk2_0 = esk4_0
    | esk1_0 = X1 ),
    inference(ef,[status(thm)],[c_0_63])).

cnf(c_0_65,negated_conjecture,
    ( esk2_0 = esk4_0
    | X1 = X2 ),
    inference(spm,[status(thm)],[c_0_64,c_0_64])).

cnf(c_0_66,negated_conjecture,
    ( esk2_0 = esk4_0 ),
    inference(er,[status(thm)],[inference(ef,[status(thm)],[c_0_65])])).

cnf(c_0_67,negated_conjecture,
    ( k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0) = k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk4_0)
    | k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0) = k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk4_0)
    | k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0) = k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk4_0)
    | k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk4_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_66]),c_0_66]),c_0_66]),c_0_66])).

cnf(c_0_68,negated_conjecture,
    ( k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0) = k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk4_0)
    | k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0) = k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk4_0)
    | k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk4_0) = k1_xboole_0
    | X1 = esk4_0
    | ~ r1_tarski(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_67])).

cnf(c_0_69,negated_conjecture,
    ( k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0) = k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk4_0)
    | k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0) = k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk4_0)
    | k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk4_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_32]),c_0_36])).

cnf(c_0_70,negated_conjecture,
    ( k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0) = k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk4_0)
    | k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk4_0) = k1_xboole_0
    | r1_tarski(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_69])).

cnf(c_0_71,negated_conjecture,
    ( k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0) = k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk4_0)
    | k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk4_0) = k1_xboole_0
    | esk4_0 = esk3_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_70]),c_0_41])).

cnf(c_0_72,plain,
    ( k2_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X2,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_52]),c_0_43])).

cnf(c_0_73,negated_conjecture,
    ( k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk4_0) = k1_xboole_0
    | esk4_0 = esk3_0
    | r1_tarski(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_71])).

cnf(c_0_74,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_44,c_0_72])).

cnf(c_0_75,negated_conjecture,
    ( k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk4_0) = k1_xboole_0
    | esk4_0 = esk3_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_73]),c_0_41])).

cnf(c_0_76,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_72,c_0_74])).

cnf(c_0_77,negated_conjecture,
    ( esk4_0 = esk3_0
    | r1_tarski(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_75])).

cnf(c_0_78,negated_conjecture,
    ( k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0) = k1_xboole_0
    | esk4_0 = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_62])])).

cnf(c_0_79,negated_conjecture,
    ( esk4_0 = esk3_0
    | esk1_0 = X1
    | esk1_0 = X2 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_78]),c_0_62])])).

cnf(c_0_80,plain,
    ( r1_tarski(X1,k2_tarski(X3,X2))
    | X1 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_81,negated_conjecture,
    ( r1_tarski(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk4_0),k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)) ),
    inference(rw,[status(thm)],[c_0_30,c_0_66])).

cnf(c_0_82,negated_conjecture,
    ( esk4_0 = esk3_0
    | esk1_0 = X1 ),
    inference(ef,[status(thm)],[c_0_79])).

cnf(c_0_83,plain,
    ( r1_tarski(X1,k3_enumset1(X3,X3,X3,X3,X2))
    | X1 != k3_enumset1(X2,X2,X2,X2,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_80,c_0_21]),c_0_22]),c_0_22]),c_0_23]),c_0_23]),c_0_24]),c_0_24])).

cnf(c_0_84,negated_conjecture,
    ( k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0) = k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk4_0)
    | ~ r1_tarski(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_76,c_0_81])).

cnf(c_0_85,negated_conjecture,
    ( esk4_0 = esk3_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_82]),c_0_36])).

cnf(c_0_86,plain,
    ( r1_tarski(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X2,X2,X2,X2,X1)) ),
    inference(er,[status(thm)],[c_0_83])).

cnf(c_0_87,negated_conjecture,
    ( k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0) = k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_84,c_0_85]),c_0_85]),c_0_85]),c_0_85]),c_0_86])])).

cnf(c_0_88,negated_conjecture,
    ( X1 = esk3_0
    | ~ r1_tarski(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_87])).

cnf(c_0_89,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_32]),c_0_41]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:29:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.40  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.20/0.40  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.20/0.40  #
% 0.20/0.40  # Preprocessing time       : 0.027 s
% 0.20/0.40  # Presaturation interreduction done
% 0.20/0.40  
% 0.20/0.40  # Proof found!
% 0.20/0.40  # SZS status Theorem
% 0.20/0.40  # SZS output start CNFRefutation
% 0.20/0.40  fof(t28_zfmisc_1, conjecture, ![X1, X2, X3, X4]:~(((r1_tarski(k2_tarski(X1,X2),k2_tarski(X3,X4))&X1!=X3)&X1!=X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_zfmisc_1)).
% 0.20/0.40  fof(l45_zfmisc_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k2_tarski(X2,X3))<=>~((((X1!=k1_xboole_0&X1!=k1_tarski(X2))&X1!=k1_tarski(X3))&X1!=k2_tarski(X2,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l45_zfmisc_1)).
% 0.20/0.40  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.20/0.40  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.20/0.40  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.20/0.40  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.20/0.40  fof(t25_zfmisc_1, axiom, ![X1, X2, X3]:~(((r1_tarski(k1_tarski(X1),k2_tarski(X2,X3))&X1!=X2)&X1!=X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_zfmisc_1)).
% 0.20/0.40  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 0.20/0.40  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.20/0.40  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 0.20/0.40  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.20/0.40  fof(t10_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_tarski(X1,k2_xboole_0(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_xboole_1)).
% 0.20/0.40  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.20/0.40  fof(c_0_13, negated_conjecture, ~(![X1, X2, X3, X4]:~(((r1_tarski(k2_tarski(X1,X2),k2_tarski(X3,X4))&X1!=X3)&X1!=X4))), inference(assume_negation,[status(cth)],[t28_zfmisc_1])).
% 0.20/0.40  fof(c_0_14, plain, ![X27, X28, X29]:((~r1_tarski(X27,k2_tarski(X28,X29))|(X27=k1_xboole_0|X27=k1_tarski(X28)|X27=k1_tarski(X29)|X27=k2_tarski(X28,X29)))&((((X27!=k1_xboole_0|r1_tarski(X27,k2_tarski(X28,X29)))&(X27!=k1_tarski(X28)|r1_tarski(X27,k2_tarski(X28,X29))))&(X27!=k1_tarski(X29)|r1_tarski(X27,k2_tarski(X28,X29))))&(X27!=k2_tarski(X28,X29)|r1_tarski(X27,k2_tarski(X28,X29))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l45_zfmisc_1])])])).
% 0.20/0.40  fof(c_0_15, plain, ![X17]:k2_tarski(X17,X17)=k1_tarski(X17), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.20/0.40  fof(c_0_16, plain, ![X18, X19]:k1_enumset1(X18,X18,X19)=k2_tarski(X18,X19), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.20/0.40  fof(c_0_17, plain, ![X20, X21, X22]:k2_enumset1(X20,X20,X21,X22)=k1_enumset1(X20,X21,X22), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.20/0.40  fof(c_0_18, plain, ![X23, X24, X25, X26]:k3_enumset1(X23,X23,X24,X25,X26)=k2_enumset1(X23,X24,X25,X26), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.20/0.40  fof(c_0_19, negated_conjecture, ((r1_tarski(k2_tarski(esk1_0,esk2_0),k2_tarski(esk3_0,esk4_0))&esk1_0!=esk3_0)&esk1_0!=esk4_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).
% 0.20/0.40  cnf(c_0_20, plain, (r1_tarski(X1,k2_tarski(X2,X3))|X1!=k1_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.40  cnf(c_0_21, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.40  cnf(c_0_22, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.40  cnf(c_0_23, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.40  cnf(c_0_24, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.40  cnf(c_0_25, plain, (X1=k1_xboole_0|X1=k1_tarski(X2)|X1=k1_tarski(X3)|X1=k2_tarski(X2,X3)|~r1_tarski(X1,k2_tarski(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.40  cnf(c_0_26, negated_conjecture, (r1_tarski(k2_tarski(esk1_0,esk2_0),k2_tarski(esk3_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.40  fof(c_0_27, plain, ![X30, X31, X32]:(~r1_tarski(k1_tarski(X30),k2_tarski(X31,X32))|X30=X31|X30=X32), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_zfmisc_1])])).
% 0.20/0.40  cnf(c_0_28, plain, (r1_tarski(X1,k3_enumset1(X2,X2,X2,X2,X3))|X1!=k3_enumset1(X2,X2,X2,X2,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20, c_0_21]), c_0_22]), c_0_22]), c_0_23]), c_0_23]), c_0_24]), c_0_24])).
% 0.20/0.40  cnf(c_0_29, plain, (X1=k1_xboole_0|X1=k3_enumset1(X3,X3,X3,X3,X3)|X1=k3_enumset1(X2,X2,X2,X2,X3)|X1=k3_enumset1(X2,X2,X2,X2,X2)|~r1_tarski(X1,k3_enumset1(X2,X2,X2,X2,X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25, c_0_21]), c_0_21]), c_0_22]), c_0_22]), c_0_22]), c_0_22]), c_0_23]), c_0_23]), c_0_23]), c_0_23]), c_0_24]), c_0_24]), c_0_24]), c_0_24])).
% 0.20/0.40  cnf(c_0_30, negated_conjecture, (r1_tarski(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26, c_0_22]), c_0_22]), c_0_23]), c_0_23]), c_0_24]), c_0_24])).
% 0.20/0.40  cnf(c_0_31, plain, (X1=X2|X1=X3|~r1_tarski(k1_tarski(X1),k2_tarski(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.40  cnf(c_0_32, plain, (r1_tarski(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X1,X1,X1,X1,X2))), inference(er,[status(thm)],[c_0_28])).
% 0.20/0.40  cnf(c_0_33, negated_conjecture, (k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)=k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0)|k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)=k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0)|k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)=k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0)|k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.20/0.40  cnf(c_0_34, plain, (X1=X3|X1=X2|~r1_tarski(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X2,X2,X2,X2,X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_21]), c_0_22]), c_0_22]), c_0_23]), c_0_23]), c_0_24]), c_0_24])).
% 0.20/0.40  cnf(c_0_35, negated_conjecture, (k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)=k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0)|k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)=k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0)|k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0)=k1_xboole_0|r1_tarski(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0))), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.20/0.40  cnf(c_0_36, negated_conjecture, (esk1_0!=esk4_0), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.40  cnf(c_0_37, negated_conjecture, (k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)=k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0)|k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)=k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0)|k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0)=k1_xboole_0|esk2_0=esk4_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_36])).
% 0.20/0.40  fof(c_0_38, plain, ![X12]:k2_xboole_0(X12,k1_xboole_0)=X12, inference(variable_rename,[status(thm)],[t1_boole])).
% 0.20/0.40  fof(c_0_39, plain, ![X5, X6]:k2_xboole_0(X5,X6)=k2_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.20/0.40  cnf(c_0_40, negated_conjecture, (k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)=k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0)|k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0)=k1_xboole_0|esk2_0=esk4_0|X1=esk3_0|X1=esk4_0|~r1_tarski(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0))), inference(spm,[status(thm)],[c_0_34, c_0_37])).
% 0.20/0.40  cnf(c_0_41, negated_conjecture, (esk1_0!=esk3_0), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.40  fof(c_0_42, plain, ![X13, X14]:k2_xboole_0(X13,k4_xboole_0(X14,X13))=k2_xboole_0(X13,X14), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 0.20/0.40  cnf(c_0_43, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.20/0.40  cnf(c_0_44, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.20/0.40  cnf(c_0_45, negated_conjecture, (k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)=k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0)|k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0)=k1_xboole_0|esk2_0=esk4_0), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_32]), c_0_41]), c_0_36])).
% 0.20/0.40  fof(c_0_46, plain, ![X7, X8]:((k4_xboole_0(X7,X8)!=k1_xboole_0|r1_tarski(X7,X8))&(~r1_tarski(X7,X8)|k4_xboole_0(X7,X8)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.20/0.40  cnf(c_0_47, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.20/0.40  cnf(c_0_48, plain, (k2_xboole_0(k1_xboole_0,X1)=X1), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.20/0.40  cnf(c_0_49, negated_conjecture, (k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0)=k1_xboole_0|esk2_0=esk4_0|X1=esk3_0|~r1_tarski(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0))), inference(spm,[status(thm)],[c_0_34, c_0_45])).
% 0.20/0.40  fof(c_0_50, plain, ![X9, X10, X11]:(~r1_tarski(X9,X10)|r1_tarski(X9,k2_xboole_0(X11,X10))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_xboole_1])])).
% 0.20/0.40  fof(c_0_51, plain, ![X15, X16]:r1_tarski(X15,k2_xboole_0(X15,X16)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.20/0.40  cnf(c_0_52, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.20/0.40  cnf(c_0_53, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_48])).
% 0.20/0.40  cnf(c_0_54, negated_conjecture, (k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0)=k1_xboole_0|esk2_0=esk4_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_32]), c_0_41])).
% 0.20/0.40  cnf(c_0_55, plain, (r1_tarski(X1,k2_xboole_0(X3,X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.20/0.40  cnf(c_0_56, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.20/0.40  cnf(c_0_57, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.20/0.40  cnf(c_0_58, negated_conjecture, (esk2_0=esk4_0|r1_tarski(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k1_xboole_0)), inference(spm,[status(thm)],[c_0_32, c_0_54])).
% 0.20/0.40  cnf(c_0_59, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_55, c_0_43])).
% 0.20/0.40  cnf(c_0_60, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_56, c_0_43])).
% 0.20/0.40  cnf(c_0_61, negated_conjecture, (k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0)=k1_xboole_0|esk2_0=esk4_0), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 0.20/0.40  cnf(c_0_62, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 0.20/0.40  cnf(c_0_63, negated_conjecture, (esk2_0=esk4_0|esk1_0=X1|esk1_0=X2), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_61]), c_0_62])])).
% 0.20/0.40  cnf(c_0_64, negated_conjecture, (esk2_0=esk4_0|esk1_0=X1), inference(ef,[status(thm)],[c_0_63])).
% 0.20/0.40  cnf(c_0_65, negated_conjecture, (esk2_0=esk4_0|X1=X2), inference(spm,[status(thm)],[c_0_64, c_0_64])).
% 0.20/0.40  cnf(c_0_66, negated_conjecture, (esk2_0=esk4_0), inference(er,[status(thm)],[inference(ef,[status(thm)],[c_0_65])])).
% 0.20/0.40  cnf(c_0_67, negated_conjecture, (k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)=k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk4_0)|k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)=k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk4_0)|k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)=k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk4_0)|k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk4_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33, c_0_66]), c_0_66]), c_0_66]), c_0_66])).
% 0.20/0.40  cnf(c_0_68, negated_conjecture, (k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)=k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk4_0)|k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)=k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk4_0)|k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk4_0)=k1_xboole_0|X1=esk4_0|~r1_tarski(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk4_0))), inference(spm,[status(thm)],[c_0_34, c_0_67])).
% 0.20/0.40  cnf(c_0_69, negated_conjecture, (k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)=k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk4_0)|k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)=k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk4_0)|k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk4_0)=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_32]), c_0_36])).
% 0.20/0.40  cnf(c_0_70, negated_conjecture, (k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)=k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk4_0)|k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk4_0)=k1_xboole_0|r1_tarski(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk4_0))), inference(spm,[status(thm)],[c_0_32, c_0_69])).
% 0.20/0.40  cnf(c_0_71, negated_conjecture, (k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)=k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk4_0)|k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk4_0)=k1_xboole_0|esk4_0=esk3_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_70]), c_0_41])).
% 0.20/0.40  cnf(c_0_72, plain, (k2_xboole_0(X1,X2)=X1|~r1_tarski(X2,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_52]), c_0_43])).
% 0.20/0.40  cnf(c_0_73, negated_conjecture, (k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk4_0)=k1_xboole_0|esk4_0=esk3_0|r1_tarski(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk4_0))), inference(spm,[status(thm)],[c_0_32, c_0_71])).
% 0.20/0.40  cnf(c_0_74, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_44, c_0_72])).
% 0.20/0.40  cnf(c_0_75, negated_conjecture, (k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk4_0)=k1_xboole_0|esk4_0=esk3_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_73]), c_0_41])).
% 0.20/0.40  cnf(c_0_76, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_72, c_0_74])).
% 0.20/0.40  cnf(c_0_77, negated_conjecture, (esk4_0=esk3_0|r1_tarski(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k1_xboole_0)), inference(spm,[status(thm)],[c_0_32, c_0_75])).
% 0.20/0.40  cnf(c_0_78, negated_conjecture, (k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0)=k1_xboole_0|esk4_0=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_77]), c_0_62])])).
% 0.20/0.40  cnf(c_0_79, negated_conjecture, (esk4_0=esk3_0|esk1_0=X1|esk1_0=X2), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_78]), c_0_62])])).
% 0.20/0.40  cnf(c_0_80, plain, (r1_tarski(X1,k2_tarski(X3,X2))|X1!=k1_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.40  cnf(c_0_81, negated_conjecture, (r1_tarski(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk4_0),k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))), inference(rw,[status(thm)],[c_0_30, c_0_66])).
% 0.20/0.40  cnf(c_0_82, negated_conjecture, (esk4_0=esk3_0|esk1_0=X1), inference(ef,[status(thm)],[c_0_79])).
% 0.20/0.40  cnf(c_0_83, plain, (r1_tarski(X1,k3_enumset1(X3,X3,X3,X3,X2))|X1!=k3_enumset1(X2,X2,X2,X2,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_80, c_0_21]), c_0_22]), c_0_22]), c_0_23]), c_0_23]), c_0_24]), c_0_24])).
% 0.20/0.40  cnf(c_0_84, negated_conjecture, (k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)=k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk4_0)|~r1_tarski(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk4_0))), inference(spm,[status(thm)],[c_0_76, c_0_81])).
% 0.20/0.40  cnf(c_0_85, negated_conjecture, (esk4_0=esk3_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_82]), c_0_36])).
% 0.20/0.40  cnf(c_0_86, plain, (r1_tarski(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X2,X2,X2,X2,X1))), inference(er,[status(thm)],[c_0_83])).
% 0.20/0.40  cnf(c_0_87, negated_conjecture, (k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)=k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_84, c_0_85]), c_0_85]), c_0_85]), c_0_85]), c_0_86])])).
% 0.20/0.40  cnf(c_0_88, negated_conjecture, (X1=esk3_0|~r1_tarski(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk3_0))), inference(spm,[status(thm)],[c_0_34, c_0_87])).
% 0.20/0.40  cnf(c_0_89, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_32]), c_0_41]), ['proof']).
% 0.20/0.40  # SZS output end CNFRefutation
% 0.20/0.40  # Proof object total steps             : 90
% 0.20/0.40  # Proof object clause steps            : 63
% 0.20/0.40  # Proof object formula steps           : 27
% 0.20/0.40  # Proof object conjectures             : 37
% 0.20/0.40  # Proof object clause conjectures      : 34
% 0.20/0.40  # Proof object formula conjectures     : 3
% 0.20/0.40  # Proof object initial clauses used    : 17
% 0.20/0.40  # Proof object initial formulas used   : 13
% 0.20/0.40  # Proof object generating inferences   : 36
% 0.20/0.40  # Proof object simplifying inferences  : 72
% 0.20/0.40  # Training examples: 0 positive, 0 negative
% 0.20/0.40  # Parsed axioms                        : 13
% 0.20/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.40  # Initial clauses                      : 20
% 0.20/0.40  # Removed in clause preprocessing      : 4
% 0.20/0.40  # Initial clauses in saturation        : 16
% 0.20/0.40  # Processed clauses                    : 261
% 0.20/0.40  # ...of these trivial                  : 9
% 0.20/0.40  # ...subsumed                          : 109
% 0.20/0.40  # ...remaining for further processing  : 143
% 0.20/0.40  # Other redundant clauses eliminated   : 51
% 0.20/0.40  # Clauses deleted for lack of memory   : 0
% 0.20/0.40  # Backward-subsumed                    : 34
% 0.20/0.40  # Backward-rewritten                   : 49
% 0.20/0.40  # Generated clauses                    : 1587
% 0.20/0.40  # ...of the previous two non-trivial   : 1379
% 0.20/0.40  # Contextual simplify-reflections      : 0
% 0.20/0.40  # Paramodulations                      : 1489
% 0.20/0.40  # Factorizations                       : 47
% 0.20/0.40  # Equation resolutions                 : 51
% 0.20/0.40  # Propositional unsat checks           : 0
% 0.20/0.40  #    Propositional check models        : 0
% 0.20/0.40  #    Propositional check unsatisfiable : 0
% 0.20/0.40  #    Propositional clauses             : 0
% 0.20/0.40  #    Propositional clauses after purity: 0
% 0.20/0.40  #    Propositional unsat core size     : 0
% 0.20/0.40  #    Propositional preprocessing time  : 0.000
% 0.20/0.40  #    Propositional encoding time       : 0.000
% 0.20/0.40  #    Propositional solver time         : 0.000
% 0.20/0.40  #    Success case prop preproc time    : 0.000
% 0.20/0.40  #    Success case prop encoding time   : 0.000
% 0.20/0.40  #    Success case prop solver time     : 0.000
% 0.20/0.40  # Current number of processed clauses  : 40
% 0.20/0.40  #    Positive orientable unit clauses  : 15
% 0.20/0.40  #    Positive unorientable unit clauses: 1
% 0.20/0.40  #    Negative unit clauses             : 1
% 0.20/0.40  #    Non-unit-clauses                  : 23
% 0.20/0.40  # Current number of unprocessed clauses: 455
% 0.20/0.40  # ...number of literals in the above   : 1408
% 0.20/0.40  # Current number of archived formulas  : 0
% 0.20/0.40  # Current number of archived clauses   : 103
% 0.20/0.40  # Clause-clause subsumption calls (NU) : 1001
% 0.20/0.40  # Rec. Clause-clause subsumption calls : 783
% 0.20/0.40  # Non-unit clause-clause subsumptions  : 130
% 0.20/0.40  # Unit Clause-clause subsumption calls : 9
% 0.20/0.40  # Rewrite failures with RHS unbound    : 0
% 0.20/0.40  # BW rewrite match attempts            : 33
% 0.20/0.40  # BW rewrite match successes           : 13
% 0.20/0.40  # Condensation attempts                : 0
% 0.20/0.40  # Condensation successes               : 0
% 0.20/0.40  # Termbank termtop insertions          : 20101
% 0.20/0.40  
% 0.20/0.40  # -------------------------------------------------
% 0.20/0.40  # User time                : 0.052 s
% 0.20/0.40  # System time              : 0.004 s
% 0.20/0.40  # Total time               : 0.056 s
% 0.20/0.40  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
