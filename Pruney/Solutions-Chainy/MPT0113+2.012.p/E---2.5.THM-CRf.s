%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:34:36 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 528 expanded)
%              Number of clauses        :   58 ( 230 expanded)
%              Number of leaves         :   20 ( 145 expanded)
%              Depth                    :   13
%              Number of atoms          :  151 ( 684 expanded)
%              Number of equality atoms :   76 ( 435 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    7 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t106_xboole_1,conjecture,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k4_xboole_0(X2,X3))
     => ( r1_tarski(X1,X2)
        & r1_xboole_0(X1,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t49_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(t84_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( ~ r1_xboole_0(X1,X2)
        & r1_xboole_0(X1,X3)
        & r1_xboole_0(X1,k4_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_xboole_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(l97_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l97_xboole_1)).

fof(t92_xboole_1,axiom,(
    ! [X1] : k5_xboole_0(X1,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t50_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_xboole_1)).

fof(t16_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

fof(t23_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(commutativity_k5_xboole_0,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(d8_xboole_0,axiom,(
    ! [X1,X2] :
      ( r2_xboole_0(X1,X2)
    <=> ( r1_tarski(X1,X2)
        & X1 != X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(t5_boole,axiom,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(t60_xboole_1,axiom,(
    ! [X1,X2] :
      ~ ( r1_tarski(X1,X2)
        & r2_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_xboole_1)).

fof(c_0_20,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( r1_tarski(X1,k4_xboole_0(X2,X3))
       => ( r1_tarski(X1,X2)
          & r1_xboole_0(X1,X3) ) ) ),
    inference(assume_negation,[status(cth)],[t106_xboole_1])).

fof(c_0_21,negated_conjecture,
    ( r1_tarski(esk2_0,k4_xboole_0(esk3_0,esk4_0))
    & ( ~ r1_tarski(esk2_0,esk3_0)
      | ~ r1_xboole_0(esk2_0,esk4_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_20])])])).

fof(c_0_22,plain,(
    ! [X21,X22] : k4_xboole_0(X21,X22) = k5_xboole_0(X21,k3_xboole_0(X21,X22)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_23,plain,(
    ! [X39,X40,X41] : k3_xboole_0(X39,k4_xboole_0(X40,X41)) = k4_xboole_0(k3_xboole_0(X39,X40),X41) ),
    inference(variable_rename,[status(thm)],[t49_xboole_1])).

fof(c_0_24,plain,(
    ! [X52,X53,X54] :
      ( r1_xboole_0(X52,X53)
      | ~ r1_xboole_0(X52,X54)
      | ~ r1_xboole_0(X52,k4_xboole_0(X53,X54)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t84_xboole_1])])])).

fof(c_0_25,plain,(
    ! [X36,X37] :
      ( ~ r1_tarski(X36,X37)
      | k3_xboole_0(X36,X37) = X36 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_26,negated_conjecture,
    ( r1_tarski(esk2_0,k4_xboole_0(esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_28,plain,(
    ! [X19,X20] : r1_xboole_0(k3_xboole_0(X19,X20),k5_xboole_0(X19,X20)) ),
    inference(variable_rename,[status(thm)],[l97_xboole_1])).

fof(c_0_29,plain,(
    ! [X61] : k5_xboole_0(X61,X61) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t92_xboole_1])).

fof(c_0_30,plain,(
    ! [X12] : k3_xboole_0(X12,X12) = X12 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

fof(c_0_31,plain,(
    ! [X64,X65] : k2_xboole_0(X64,X65) = k5_xboole_0(X64,k4_xboole_0(X65,X64)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_32,plain,(
    ! [X42,X43,X44] : k3_xboole_0(X42,k4_xboole_0(X43,X44)) = k4_xboole_0(k3_xboole_0(X42,X43),k3_xboole_0(X42,X44)) ),
    inference(variable_rename,[status(thm)],[t50_xboole_1])).

cnf(c_0_33,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_34,plain,(
    ! [X23,X24,X25] : k3_xboole_0(k3_xboole_0(X23,X24),X25) = k3_xboole_0(X23,k3_xboole_0(X24,X25)) ),
    inference(variable_rename,[status(thm)],[t16_xboole_1])).

cnf(c_0_35,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X1,X3)
    | ~ r1_xboole_0(X1,k4_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_36,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_37,negated_conjecture,
    ( r1_tarski(esk2_0,k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,esk4_0))) ),
    inference(rw,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_38,plain,
    ( r1_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_39,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_40,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_41,plain,(
    ! [X30,X31,X32] : k3_xboole_0(X30,k2_xboole_0(X31,X32)) = k2_xboole_0(k3_xboole_0(X30,X31),k3_xboole_0(X30,X32)) ),
    inference(variable_rename,[status(thm)],[t23_xboole_1])).

cnf(c_0_42,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_43,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_44,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))) = k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k3_xboole_0(X1,X2),X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_27]),c_0_27])).

cnf(c_0_45,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_46,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X1,X3)
    | ~ r1_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))) ),
    inference(rw,[status(thm)],[c_0_35,c_0_27])).

cnf(c_0_47,negated_conjecture,
    ( k3_xboole_0(esk2_0,k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,esk4_0))) = esk2_0 ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_48,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40])).

fof(c_0_49,plain,(
    ! [X4,X5] : k3_xboole_0(X4,X5) = k3_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_50,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_51,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(rw,[status(thm)],[c_0_42,c_0_27])).

cnf(c_0_52,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))) = k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_27]),c_0_27])).

cnf(c_0_53,plain,
    ( k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,k3_xboole_0(X2,X3))) = k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))) ),
    inference(rw,[status(thm)],[c_0_44,c_0_45])).

fof(c_0_54,plain,(
    ! [X8,X9] :
      ( ( ~ r1_xboole_0(X8,X9)
        | k3_xboole_0(X8,X9) = k1_xboole_0 )
      & ( k3_xboole_0(X8,X9) != k1_xboole_0
        | r1_xboole_0(X8,X9) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

cnf(c_0_55,negated_conjecture,
    ( r1_xboole_0(X1,esk2_0)
    | ~ r1_xboole_0(X1,k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_39]),c_0_48])])).

cnf(c_0_56,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_45,c_0_40])).

cnf(c_0_57,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

fof(c_0_58,plain,(
    ! [X17,X18] :
      ( ( k4_xboole_0(X17,X18) != k1_xboole_0
        | r1_tarski(X17,X18) )
      & ( ~ r1_tarski(X17,X18)
        | k4_xboole_0(X17,X18) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

cnf(c_0_59,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2)))) = k5_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(k3_xboole_0(X1,X3),k3_xboole_0(k3_xboole_0(X1,X3),k3_xboole_0(X1,X2)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50,c_0_51]),c_0_51])).

cnf(c_0_60,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,k3_xboole_0(X1,X3)))) = k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_45]),c_0_53])).

fof(c_0_61,plain,(
    ! [X6,X7] : k5_xboole_0(X6,X7) = k5_xboole_0(X7,X6) ),
    inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).

fof(c_0_62,plain,(
    ! [X10,X11] :
      ( ( r1_tarski(X10,X11)
        | ~ r2_xboole_0(X10,X11) )
      & ( X10 != X11
        | ~ r2_xboole_0(X10,X11) )
      & ( ~ r1_tarski(X10,X11)
        | X10 = X11
        | r2_xboole_0(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_xboole_0])])])).

fof(c_0_63,plain,(
    ! [X26,X27] : r1_tarski(k3_xboole_0(X26,X27),X26) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

cnf(c_0_64,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_65,negated_conjecture,
    ( r1_xboole_0(k3_xboole_0(esk3_0,esk4_0),esk2_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_38]),c_0_56])).

cnf(c_0_66,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,X3)) = k3_xboole_0(X2,k3_xboole_0(X1,X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_57]),c_0_45])).

fof(c_0_67,plain,(
    ! [X45] : k5_xboole_0(X45,k1_xboole_0) = X45 ),
    inference(variable_rename,[status(thm)],[t5_boole])).

cnf(c_0_68,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_69,plain,
    ( k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,k5_xboole_0(X3,k3_xboole_0(X3,X2)))) = k3_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59,c_0_45]),c_0_53]),c_0_60])).

cnf(c_0_70,plain,
    ( k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

fof(c_0_71,plain,(
    ! [X46,X47] :
      ( ~ r1_tarski(X46,X47)
      | ~ r2_xboole_0(X47,X46) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t60_xboole_1])])).

cnf(c_0_72,plain,
    ( X1 = X2
    | r2_xboole_0(X1,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_73,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_74,plain,
    ( r1_tarski(X1,X2)
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_75,negated_conjecture,
    ( k3_xboole_0(esk2_0,k3_xboole_0(esk3_0,esk4_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_45]),c_0_57]),c_0_66])).

cnf(c_0_76,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_77,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_68,c_0_27])).

cnf(c_0_78,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,k5_xboole_0(X1,X2))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_38]),c_0_45])).

cnf(c_0_79,negated_conjecture,
    ( k3_xboole_0(esk2_0,k5_xboole_0(esk4_0,k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,esk4_0)))) = k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk4_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_47]),c_0_70])).

cnf(c_0_80,plain,
    ( ~ r1_tarski(X1,X2)
    | ~ r2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_81,plain,
    ( k3_xboole_0(X1,X2) = X1
    | r2_xboole_0(k3_xboole_0(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_82,plain,
    ( r1_tarski(X1,X2)
    | k5_xboole_0(X1,k3_xboole_0(X1,X2)) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_74,c_0_27])).

cnf(c_0_83,negated_conjecture,
    ( k3_xboole_0(esk2_0,esk3_0) = esk2_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_75]),c_0_76]),c_0_47])).

cnf(c_0_84,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k3_xboole_0(X2,k5_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_76])).

cnf(c_0_85,negated_conjecture,
    ( r1_tarski(k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk4_0)),esk2_0) ),
    inference(spm,[status(thm)],[c_0_73,c_0_79])).

cnf(c_0_86,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,k3_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_80,c_0_81])).

cnf(c_0_87,negated_conjecture,
    ( ~ r1_tarski(esk2_0,esk3_0)
    | ~ r1_xboole_0(esk2_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_88,negated_conjecture,
    ( r1_tarski(esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_39])])).

cnf(c_0_89,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k3_xboole_0(X2,k5_xboole_0(X2,X1))) ),
    inference(spm,[status(thm)],[c_0_84,c_0_70])).

cnf(c_0_90,negated_conjecture,
    ( k3_xboole_0(esk2_0,k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk4_0))) = k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk4_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_85]),c_0_57])).

cnf(c_0_91,plain,
    ( k3_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X2,k3_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_86,c_0_57])).

cnf(c_0_92,negated_conjecture,
    ( k3_xboole_0(esk3_0,k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk4_0))) = esk2_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_75]),c_0_76]),c_0_57]),c_0_83])).

cnf(c_0_93,negated_conjecture,
    ( ~ r1_xboole_0(esk2_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_87,c_0_88])])).

cnf(c_0_94,plain,
    ( r1_xboole_0(X1,X2)
    | k3_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_95,negated_conjecture,
    ( k3_xboole_0(esk2_0,esk4_0) = k1_xboole_0
    | ~ r1_tarski(k3_xboole_0(esk2_0,esk4_0),k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk4_0))) ),
    inference(spm,[status(thm)],[c_0_89,c_0_90])).

cnf(c_0_96,negated_conjecture,
    ( k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk4_0)) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_92]),c_0_85])])).

cnf(c_0_97,negated_conjecture,
    ( k3_xboole_0(esk2_0,esk4_0) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_93,c_0_94])).

cnf(c_0_98,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_95,c_0_96]),c_0_73])]),c_0_97]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:03:35 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.42  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.20/0.42  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.20/0.42  #
% 0.20/0.42  # Preprocessing time       : 0.028 s
% 0.20/0.42  # Presaturation interreduction done
% 0.20/0.42  
% 0.20/0.42  # Proof found!
% 0.20/0.42  # SZS status Theorem
% 0.20/0.42  # SZS output start CNFRefutation
% 0.20/0.42  fof(t106_xboole_1, conjecture, ![X1, X2, X3]:(r1_tarski(X1,k4_xboole_0(X2,X3))=>(r1_tarski(X1,X2)&r1_xboole_0(X1,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 0.20/0.42  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.20/0.42  fof(t49_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 0.20/0.42  fof(t84_xboole_1, axiom, ![X1, X2, X3]:~(((~(r1_xboole_0(X1,X2))&r1_xboole_0(X1,X3))&r1_xboole_0(X1,k4_xboole_0(X2,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_xboole_1)).
% 0.20/0.42  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.20/0.42  fof(l97_xboole_1, axiom, ![X1, X2]:r1_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l97_xboole_1)).
% 0.20/0.42  fof(t92_xboole_1, axiom, ![X1]:k5_xboole_0(X1,X1)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 0.20/0.42  fof(idempotence_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 0.20/0.42  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.20/0.42  fof(t50_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_xboole_1)).
% 0.20/0.42  fof(t16_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(k3_xboole_0(X1,X2),X3)=k3_xboole_0(X1,k3_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_xboole_1)).
% 0.20/0.42  fof(t23_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(X1,k2_xboole_0(X2,X3))=k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_xboole_1)).
% 0.20/0.42  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.20/0.42  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 0.20/0.42  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.20/0.42  fof(commutativity_k5_xboole_0, axiom, ![X1, X2]:k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 0.20/0.42  fof(d8_xboole_0, axiom, ![X1, X2]:(r2_xboole_0(X1,X2)<=>(r1_tarski(X1,X2)&X1!=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 0.20/0.42  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 0.20/0.42  fof(t5_boole, axiom, ![X1]:k5_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 0.20/0.42  fof(t60_xboole_1, axiom, ![X1, X2]:~((r1_tarski(X1,X2)&r2_xboole_0(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_xboole_1)).
% 0.20/0.42  fof(c_0_20, negated_conjecture, ~(![X1, X2, X3]:(r1_tarski(X1,k4_xboole_0(X2,X3))=>(r1_tarski(X1,X2)&r1_xboole_0(X1,X3)))), inference(assume_negation,[status(cth)],[t106_xboole_1])).
% 0.20/0.42  fof(c_0_21, negated_conjecture, (r1_tarski(esk2_0,k4_xboole_0(esk3_0,esk4_0))&(~r1_tarski(esk2_0,esk3_0)|~r1_xboole_0(esk2_0,esk4_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_20])])])).
% 0.20/0.42  fof(c_0_22, plain, ![X21, X22]:k4_xboole_0(X21,X22)=k5_xboole_0(X21,k3_xboole_0(X21,X22)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.20/0.42  fof(c_0_23, plain, ![X39, X40, X41]:k3_xboole_0(X39,k4_xboole_0(X40,X41))=k4_xboole_0(k3_xboole_0(X39,X40),X41), inference(variable_rename,[status(thm)],[t49_xboole_1])).
% 0.20/0.42  fof(c_0_24, plain, ![X52, X53, X54]:(r1_xboole_0(X52,X53)|~r1_xboole_0(X52,X54)|~r1_xboole_0(X52,k4_xboole_0(X53,X54))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t84_xboole_1])])])).
% 0.20/0.42  fof(c_0_25, plain, ![X36, X37]:(~r1_tarski(X36,X37)|k3_xboole_0(X36,X37)=X36), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.20/0.42  cnf(c_0_26, negated_conjecture, (r1_tarski(esk2_0,k4_xboole_0(esk3_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.42  cnf(c_0_27, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.42  fof(c_0_28, plain, ![X19, X20]:r1_xboole_0(k3_xboole_0(X19,X20),k5_xboole_0(X19,X20)), inference(variable_rename,[status(thm)],[l97_xboole_1])).
% 0.20/0.42  fof(c_0_29, plain, ![X61]:k5_xboole_0(X61,X61)=k1_xboole_0, inference(variable_rename,[status(thm)],[t92_xboole_1])).
% 0.20/0.42  fof(c_0_30, plain, ![X12]:k3_xboole_0(X12,X12)=X12, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).
% 0.20/0.42  fof(c_0_31, plain, ![X64, X65]:k2_xboole_0(X64,X65)=k5_xboole_0(X64,k4_xboole_0(X65,X64)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.20/0.42  fof(c_0_32, plain, ![X42, X43, X44]:k3_xboole_0(X42,k4_xboole_0(X43,X44))=k4_xboole_0(k3_xboole_0(X42,X43),k3_xboole_0(X42,X44)), inference(variable_rename,[status(thm)],[t50_xboole_1])).
% 0.20/0.42  cnf(c_0_33, plain, (k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.42  fof(c_0_34, plain, ![X23, X24, X25]:k3_xboole_0(k3_xboole_0(X23,X24),X25)=k3_xboole_0(X23,k3_xboole_0(X24,X25)), inference(variable_rename,[status(thm)],[t16_xboole_1])).
% 0.20/0.42  cnf(c_0_35, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(X1,X3)|~r1_xboole_0(X1,k4_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.42  cnf(c_0_36, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.42  cnf(c_0_37, negated_conjecture, (r1_tarski(esk2_0,k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,esk4_0)))), inference(rw,[status(thm)],[c_0_26, c_0_27])).
% 0.20/0.42  cnf(c_0_38, plain, (r1_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.42  cnf(c_0_39, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.20/0.42  cnf(c_0_40, plain, (k3_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.42  fof(c_0_41, plain, ![X30, X31, X32]:k3_xboole_0(X30,k2_xboole_0(X31,X32))=k2_xboole_0(k3_xboole_0(X30,X31),k3_xboole_0(X30,X32)), inference(variable_rename,[status(thm)],[t23_xboole_1])).
% 0.20/0.42  cnf(c_0_42, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.20/0.42  cnf(c_0_43, plain, (k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.42  cnf(c_0_44, plain, (k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))=k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k3_xboole_0(X1,X2),X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33, c_0_27]), c_0_27])).
% 0.20/0.42  cnf(c_0_45, plain, (k3_xboole_0(k3_xboole_0(X1,X2),X3)=k3_xboole_0(X1,k3_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.20/0.42  cnf(c_0_46, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(X1,X3)|~r1_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))), inference(rw,[status(thm)],[c_0_35, c_0_27])).
% 0.20/0.42  cnf(c_0_47, negated_conjecture, (k3_xboole_0(esk2_0,k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,esk4_0)))=esk2_0), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.20/0.42  cnf(c_0_48, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_40])).
% 0.20/0.42  fof(c_0_49, plain, ![X4, X5]:k3_xboole_0(X4,X5)=k3_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.20/0.42  cnf(c_0_50, plain, (k3_xboole_0(X1,k2_xboole_0(X2,X3))=k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.20/0.42  cnf(c_0_51, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))), inference(rw,[status(thm)],[c_0_42, c_0_27])).
% 0.20/0.42  cnf(c_0_52, plain, (k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))=k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43, c_0_27]), c_0_27])).
% 0.20/0.42  cnf(c_0_53, plain, (k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,k3_xboole_0(X2,X3)))=k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))), inference(rw,[status(thm)],[c_0_44, c_0_45])).
% 0.20/0.42  fof(c_0_54, plain, ![X8, X9]:((~r1_xboole_0(X8,X9)|k3_xboole_0(X8,X9)=k1_xboole_0)&(k3_xboole_0(X8,X9)!=k1_xboole_0|r1_xboole_0(X8,X9))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 0.20/0.42  cnf(c_0_55, negated_conjecture, (r1_xboole_0(X1,esk2_0)|~r1_xboole_0(X1,k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_39]), c_0_48])])).
% 0.20/0.42  cnf(c_0_56, plain, (k3_xboole_0(X1,k3_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_45, c_0_40])).
% 0.20/0.42  cnf(c_0_57, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.20/0.42  fof(c_0_58, plain, ![X17, X18]:((k4_xboole_0(X17,X18)!=k1_xboole_0|r1_tarski(X17,X18))&(~r1_tarski(X17,X18)|k4_xboole_0(X17,X18)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.20/0.42  cnf(c_0_59, plain, (k3_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2))))=k5_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(k3_xboole_0(X1,X3),k3_xboole_0(k3_xboole_0(X1,X3),k3_xboole_0(X1,X2))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50, c_0_51]), c_0_51])).
% 0.20/0.42  cnf(c_0_60, plain, (k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,k3_xboole_0(X1,X3))))=k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52, c_0_45]), c_0_53])).
% 0.20/0.42  fof(c_0_61, plain, ![X6, X7]:k5_xboole_0(X6,X7)=k5_xboole_0(X7,X6), inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).
% 0.20/0.42  fof(c_0_62, plain, ![X10, X11]:(((r1_tarski(X10,X11)|~r2_xboole_0(X10,X11))&(X10!=X11|~r2_xboole_0(X10,X11)))&(~r1_tarski(X10,X11)|X10=X11|r2_xboole_0(X10,X11))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_xboole_0])])])).
% 0.20/0.42  fof(c_0_63, plain, ![X26, X27]:r1_tarski(k3_xboole_0(X26,X27),X26), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 0.20/0.42  cnf(c_0_64, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.20/0.42  cnf(c_0_65, negated_conjecture, (r1_xboole_0(k3_xboole_0(esk3_0,esk4_0),esk2_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_38]), c_0_56])).
% 0.20/0.42  cnf(c_0_66, plain, (k3_xboole_0(X1,k3_xboole_0(X2,X3))=k3_xboole_0(X2,k3_xboole_0(X1,X3))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_57]), c_0_45])).
% 0.20/0.42  fof(c_0_67, plain, ![X45]:k5_xboole_0(X45,k1_xboole_0)=X45, inference(variable_rename,[status(thm)],[t5_boole])).
% 0.20/0.42  cnf(c_0_68, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.20/0.42  cnf(c_0_69, plain, (k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,k5_xboole_0(X3,k3_xboole_0(X3,X2))))=k3_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59, c_0_45]), c_0_53]), c_0_60])).
% 0.20/0.42  cnf(c_0_70, plain, (k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.20/0.42  fof(c_0_71, plain, ![X46, X47]:(~r1_tarski(X46,X47)|~r2_xboole_0(X47,X46)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t60_xboole_1])])).
% 0.20/0.42  cnf(c_0_72, plain, (X1=X2|r2_xboole_0(X1,X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.20/0.42  cnf(c_0_73, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.20/0.42  cnf(c_0_74, plain, (r1_tarski(X1,X2)|k4_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.20/0.42  cnf(c_0_75, negated_conjecture, (k3_xboole_0(esk2_0,k3_xboole_0(esk3_0,esk4_0))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_45]), c_0_57]), c_0_66])).
% 0.20/0.42  cnf(c_0_76, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.20/0.42  cnf(c_0_77, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X2))=k1_xboole_0|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_68, c_0_27])).
% 0.20/0.42  cnf(c_0_78, plain, (k3_xboole_0(X1,k3_xboole_0(X2,k5_xboole_0(X1,X2)))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_38]), c_0_45])).
% 0.20/0.42  cnf(c_0_79, negated_conjecture, (k3_xboole_0(esk2_0,k5_xboole_0(esk4_0,k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,esk4_0))))=k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk4_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_47]), c_0_70])).
% 0.20/0.42  cnf(c_0_80, plain, (~r1_tarski(X1,X2)|~r2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_71])).
% 0.20/0.42  cnf(c_0_81, plain, (k3_xboole_0(X1,X2)=X1|r2_xboole_0(k3_xboole_0(X1,X2),X1)), inference(spm,[status(thm)],[c_0_72, c_0_73])).
% 0.20/0.42  cnf(c_0_82, plain, (r1_tarski(X1,X2)|k5_xboole_0(X1,k3_xboole_0(X1,X2))!=k1_xboole_0), inference(rw,[status(thm)],[c_0_74, c_0_27])).
% 0.20/0.42  cnf(c_0_83, negated_conjecture, (k3_xboole_0(esk2_0,esk3_0)=esk2_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_75]), c_0_76]), c_0_47])).
% 0.20/0.42  cnf(c_0_84, plain, (X1=k1_xboole_0|~r1_tarski(X1,k3_xboole_0(X2,k5_xboole_0(X1,X2)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_78]), c_0_76])).
% 0.20/0.42  cnf(c_0_85, negated_conjecture, (r1_tarski(k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk4_0)),esk2_0)), inference(spm,[status(thm)],[c_0_73, c_0_79])).
% 0.20/0.42  cnf(c_0_86, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,k3_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_80, c_0_81])).
% 0.20/0.42  cnf(c_0_87, negated_conjecture, (~r1_tarski(esk2_0,esk3_0)|~r1_xboole_0(esk2_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.42  cnf(c_0_88, negated_conjecture, (r1_tarski(esk2_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_83]), c_0_39])])).
% 0.20/0.42  cnf(c_0_89, plain, (X1=k1_xboole_0|~r1_tarski(X1,k3_xboole_0(X2,k5_xboole_0(X2,X1)))), inference(spm,[status(thm)],[c_0_84, c_0_70])).
% 0.20/0.42  cnf(c_0_90, negated_conjecture, (k3_xboole_0(esk2_0,k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk4_0)))=k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk4_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_85]), c_0_57])).
% 0.20/0.42  cnf(c_0_91, plain, (k3_xboole_0(X1,X2)=X2|~r1_tarski(X2,k3_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_86, c_0_57])).
% 0.20/0.42  cnf(c_0_92, negated_conjecture, (k3_xboole_0(esk3_0,k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk4_0)))=esk2_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_75]), c_0_76]), c_0_57]), c_0_83])).
% 0.20/0.42  cnf(c_0_93, negated_conjecture, (~r1_xboole_0(esk2_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_87, c_0_88])])).
% 0.20/0.42  cnf(c_0_94, plain, (r1_xboole_0(X1,X2)|k3_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.20/0.42  cnf(c_0_95, negated_conjecture, (k3_xboole_0(esk2_0,esk4_0)=k1_xboole_0|~r1_tarski(k3_xboole_0(esk2_0,esk4_0),k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk4_0)))), inference(spm,[status(thm)],[c_0_89, c_0_90])).
% 0.20/0.42  cnf(c_0_96, negated_conjecture, (k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk4_0))=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_92]), c_0_85])])).
% 0.20/0.42  cnf(c_0_97, negated_conjecture, (k3_xboole_0(esk2_0,esk4_0)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_93, c_0_94])).
% 0.20/0.42  cnf(c_0_98, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_95, c_0_96]), c_0_73])]), c_0_97]), ['proof']).
% 0.20/0.42  # SZS output end CNFRefutation
% 0.20/0.42  # Proof object total steps             : 99
% 0.20/0.42  # Proof object clause steps            : 58
% 0.20/0.42  # Proof object formula steps           : 41
% 0.20/0.42  # Proof object conjectures             : 21
% 0.20/0.42  # Proof object clause conjectures      : 18
% 0.20/0.42  # Proof object formula conjectures     : 3
% 0.20/0.42  # Proof object initial clauses used    : 23
% 0.20/0.42  # Proof object initial formulas used   : 20
% 0.20/0.42  # Proof object generating inferences   : 22
% 0.20/0.42  # Proof object simplifying inferences  : 45
% 0.20/0.42  # Training examples: 0 positive, 0 negative
% 0.20/0.42  # Parsed axioms                        : 32
% 0.20/0.42  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.42  # Initial clauses                      : 38
% 0.20/0.42  # Removed in clause preprocessing      : 2
% 0.20/0.42  # Initial clauses in saturation        : 36
% 0.20/0.42  # Processed clauses                    : 524
% 0.20/0.42  # ...of these trivial                  : 23
% 0.20/0.42  # ...subsumed                          : 279
% 0.20/0.42  # ...remaining for further processing  : 222
% 0.20/0.42  # Other redundant clauses eliminated   : 11
% 0.20/0.42  # Clauses deleted for lack of memory   : 0
% 0.20/0.42  # Backward-subsumed                    : 3
% 0.20/0.42  # Backward-rewritten                   : 30
% 0.20/0.42  # Generated clauses                    : 2518
% 0.20/0.42  # ...of the previous two non-trivial   : 1860
% 0.20/0.42  # Contextual simplify-reflections      : 1
% 0.20/0.42  # Paramodulations                      : 2507
% 0.20/0.42  # Factorizations                       : 0
% 0.20/0.42  # Equation resolutions                 : 11
% 0.20/0.42  # Propositional unsat checks           : 0
% 0.20/0.42  #    Propositional check models        : 0
% 0.20/0.42  #    Propositional check unsatisfiable : 0
% 0.20/0.42  #    Propositional clauses             : 0
% 0.20/0.42  #    Propositional clauses after purity: 0
% 0.20/0.42  #    Propositional unsat core size     : 0
% 0.20/0.42  #    Propositional preprocessing time  : 0.000
% 0.20/0.42  #    Propositional encoding time       : 0.000
% 0.20/0.42  #    Propositional solver time         : 0.000
% 0.20/0.42  #    Success case prop preproc time    : 0.000
% 0.20/0.42  #    Success case prop encoding time   : 0.000
% 0.20/0.42  #    Success case prop solver time     : 0.000
% 0.20/0.42  # Current number of processed clauses  : 151
% 0.20/0.42  #    Positive orientable unit clauses  : 57
% 0.20/0.42  #    Positive unorientable unit clauses: 4
% 0.20/0.42  #    Negative unit clauses             : 18
% 0.20/0.42  #    Non-unit-clauses                  : 72
% 0.20/0.42  # Current number of unprocessed clauses: 1398
% 0.20/0.42  # ...number of literals in the above   : 2312
% 0.20/0.42  # Current number of archived formulas  : 0
% 0.20/0.42  # Current number of archived clauses   : 71
% 0.20/0.42  # Clause-clause subsumption calls (NU) : 581
% 0.20/0.42  # Rec. Clause-clause subsumption calls : 558
% 0.20/0.42  # Non-unit clause-clause subsumptions  : 85
% 0.20/0.42  # Unit Clause-clause subsumption calls : 170
% 0.20/0.42  # Rewrite failures with RHS unbound    : 0
% 0.20/0.42  # BW rewrite match attempts            : 112
% 0.20/0.42  # BW rewrite match successes           : 69
% 0.20/0.42  # Condensation attempts                : 0
% 0.20/0.42  # Condensation successes               : 0
% 0.20/0.42  # Termbank termtop insertions          : 28699
% 0.20/0.42  
% 0.20/0.42  # -------------------------------------------------
% 0.20/0.42  # User time                : 0.060 s
% 0.20/0.42  # System time              : 0.009 s
% 0.20/0.42  # Total time               : 0.069 s
% 0.20/0.42  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
