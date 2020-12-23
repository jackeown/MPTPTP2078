%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:34:37 EST 2020

% Result     : Theorem 3.10s
% Output     : CNFRefutation 3.10s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 512 expanded)
%              Number of clauses        :   57 ( 230 expanded)
%              Number of leaves         :   15 ( 139 expanded)
%              Depth                    :   19
%              Number of atoms          :  140 ( 744 expanded)
%              Number of equality atoms :   65 ( 435 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal clause size      :    7 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t21_xboole_1,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,k2_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t92_xboole_1,axiom,(
    ! [X1] : k5_xboole_0(X1,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(t5_boole,axiom,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(t3_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X2) ) )
      & ~ ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(X3,X2) )
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(commutativity_k5_xboole_0,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(t91_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(t49_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t106_xboole_1,conjecture,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k4_xboole_0(X2,X3))
     => ( r1_tarski(X1,X2)
        & r1_xboole_0(X1,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

fof(c_0_15,plain,(
    ! [X34,X35] : k2_xboole_0(X34,X35) = k5_xboole_0(X34,k4_xboole_0(X35,X34)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_16,plain,(
    ! [X18,X19] : k4_xboole_0(X18,X19) = k5_xboole_0(X18,k3_xboole_0(X18,X19)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_17,plain,(
    ! [X22,X23] : k3_xboole_0(X22,k2_xboole_0(X22,X23)) = X22 ),
    inference(variable_rename,[status(thm)],[t21_xboole_1])).

cnf(c_0_18,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_21,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(rw,[status(thm)],[c_0_18,c_0_19])).

fof(c_0_22,plain,(
    ! [X24,X25] :
      ( ~ r1_tarski(X24,X25)
      | k3_xboole_0(X24,X25) = X24 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

fof(c_0_23,plain,(
    ! [X33] : k5_xboole_0(X33,X33) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t92_xboole_1])).

fof(c_0_24,plain,(
    ! [X29] : k5_xboole_0(X29,k1_xboole_0) = X29 ),
    inference(variable_rename,[status(thm)],[t5_boole])).

fof(c_0_25,plain,(
    ! [X10,X11,X13,X14,X15] :
      ( ( r2_hidden(esk1_2(X10,X11),X10)
        | r1_xboole_0(X10,X11) )
      & ( r2_hidden(esk1_2(X10,X11),X11)
        | r1_xboole_0(X10,X11) )
      & ( ~ r2_hidden(X15,X13)
        | ~ r2_hidden(X15,X14)
        | ~ r1_xboole_0(X13,X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

cnf(c_0_26,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) = X1 ),
    inference(rw,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_27,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_30,plain,(
    ! [X20,X21] : r1_tarski(k3_xboole_0(X20,X21),X20) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

cnf(c_0_31,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_32,plain,
    ( r2_hidden(esk1_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_33,plain,(
    ! [X8,X9] :
      ( ( ~ r1_xboole_0(X8,X9)
        | k3_xboole_0(X8,X9) = k1_xboole_0 )
      & ( k3_xboole_0(X8,X9) != k1_xboole_0
        | r1_xboole_0(X8,X9) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

cnf(c_0_34,plain,
    ( k3_xboole_0(X1,X1) = X1
    | ~ r1_tarski(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28]),c_0_29])).

cnf(c_0_35,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_36,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X3)
    | ~ r1_xboole_0(X3,X2) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_37,plain,
    ( r1_xboole_0(X1,X2)
    | k3_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_38,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_39,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_40,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X2,X2) ),
    inference(spm,[status(thm)],[c_0_36,c_0_32])).

cnf(c_0_41,plain,
    ( r1_xboole_0(X1,X1)
    | X1 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

fof(c_0_42,plain,(
    ! [X6,X7] : k5_xboole_0(X6,X7) = k5_xboole_0(X7,X6) ),
    inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).

fof(c_0_43,plain,(
    ! [X16,X17] :
      ( ( k4_xboole_0(X16,X17) != k1_xboole_0
        | r1_tarski(X16,X17) )
      & ( ~ r1_tarski(X16,X17)
        | k4_xboole_0(X16,X17) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

cnf(c_0_44,plain,
    ( r1_tarski(k1_xboole_0,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_35,c_0_39])).

cnf(c_0_45,plain,
    ( r1_xboole_0(X1,X2)
    | X2 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

fof(c_0_46,plain,(
    ! [X30,X31,X32] : k5_xboole_0(k5_xboole_0(X30,X31),X32) = k5_xboole_0(X30,k5_xboole_0(X31,X32)) ),
    inference(variable_rename,[status(thm)],[t91_xboole_1])).

cnf(c_0_47,plain,
    ( k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

fof(c_0_48,plain,(
    ! [X26,X27,X28] : k3_xboole_0(X26,k4_xboole_0(X27,X28)) = k4_xboole_0(k3_xboole_0(X26,X27),X28) ),
    inference(variable_rename,[status(thm)],[t49_xboole_1])).

cnf(c_0_49,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_50,plain,
    ( r1_tarski(k1_xboole_0,X1)
    | X2 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_51,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_52,plain,
    ( k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_29,c_0_47])).

cnf(c_0_53,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

fof(c_0_54,plain,(
    ! [X4,X5] : k3_xboole_0(X4,X5) = k3_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_55,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_49,c_0_19])).

cnf(c_0_56,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(er,[status(thm)],[c_0_50])).

cnf(c_0_57,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,X2)) = X2 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_28]),c_0_52])).

cnf(c_0_58,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))) = k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k3_xboole_0(X1,X2),X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53,c_0_19]),c_0_19])).

cnf(c_0_59,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_60,plain,
    ( k3_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_55]),c_0_56])])).

fof(c_0_61,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( r1_tarski(X1,k4_xboole_0(X2,X3))
       => ( r1_tarski(X1,X2)
          & r1_xboole_0(X1,X3) ) ) ),
    inference(assume_negation,[status(cth)],[t106_xboole_1])).

cnf(c_0_62,plain,
    ( k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))) = k3_xboole_0(k3_xboole_0(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_63,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

fof(c_0_64,negated_conjecture,
    ( r1_tarski(esk2_0,k4_xboole_0(esk3_0,esk4_0))
    & ( ~ r1_tarski(esk2_0,esk3_0)
      | ~ r1_xboole_0(esk2_0,esk4_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_61])])])).

cnf(c_0_65,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,k3_xboole_0(X1,X2)))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_38]),c_0_28])).

cnf(c_0_66,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,X1)) = k3_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_38]),c_0_28]),c_0_63]),c_0_29]),c_0_59])).

cnf(c_0_67,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X1))))) = X1 ),
    inference(spm,[status(thm)],[c_0_26,c_0_58])).

cnf(c_0_68,negated_conjecture,
    ( r1_tarski(esk2_0,k4_xboole_0(esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_69,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_70,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_71,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X1,X2)) = X1
    | ~ r1_tarski(X2,k5_xboole_0(X3,k3_xboole_0(X3,X1))) ),
    inference(spm,[status(thm)],[c_0_67,c_0_27])).

cnf(c_0_72,negated_conjecture,
    ( r1_tarski(esk2_0,k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,esk4_0))) ),
    inference(rw,[status(thm)],[c_0_68,c_0_19])).

cnf(c_0_73,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X3)
    | ~ r1_xboole_0(X3,X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_69])).

cnf(c_0_74,plain,
    ( r1_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_37,c_0_70])).

cnf(c_0_75,negated_conjecture,
    ( k3_xboole_0(esk4_0,k5_xboole_0(esk2_0,esk4_0)) = esk4_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_47])).

cnf(c_0_76,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))) = k3_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X1,X3))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_58])).

cnf(c_0_77,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_73,c_0_32])).

cnf(c_0_78,negated_conjecture,
    ( r1_xboole_0(esk4_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_51]),c_0_28]),c_0_29])).

cnf(c_0_79,plain,
    ( r1_tarski(X1,X2)
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_80,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))) = X2
    | ~ r1_tarski(X2,k5_xboole_0(X1,k3_xboole_0(X1,X3))) ),
    inference(spm,[status(thm)],[c_0_27,c_0_76])).

cnf(c_0_81,negated_conjecture,
    ( k3_xboole_0(esk2_0,esk4_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_75]),c_0_51]),c_0_28]),c_0_29]),c_0_59])).

cnf(c_0_82,negated_conjecture,
    ( ~ r1_tarski(esk2_0,esk3_0)
    | ~ r1_xboole_0(esk2_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_83,negated_conjecture,
    ( r1_xboole_0(esk2_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_77,c_0_78])).

cnf(c_0_84,plain,
    ( r1_tarski(X1,X2)
    | k5_xboole_0(X1,k3_xboole_0(X1,X2)) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_79,c_0_19])).

cnf(c_0_85,negated_conjecture,
    ( k3_xboole_0(esk2_0,esk3_0) = esk2_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_72]),c_0_81]),c_0_29]),c_0_59])).

cnf(c_0_86,negated_conjecture,
    ( ~ r1_tarski(esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_82,c_0_83])])).

cnf(c_0_87,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_85]),c_0_28])]),c_0_86]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.15/0.36  % Computer   : n006.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % WCLimit    : 600
% 0.15/0.36  % DateTime   : Tue Dec  1 11:13:07 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.36  # Version: 2.5pre002
% 0.15/0.36  # No SInE strategy applied
% 0.15/0.36  # Trying AutoSched0 for 299 seconds
% 3.10/3.34  # AutoSched0-Mode selected heuristic G_E___208_C48_F1_AE_CS_SP_PS_S0Y
% 3.10/3.34  # and selection function SelectMaxLComplexAvoidPosPred.
% 3.10/3.34  #
% 3.10/3.34  # Preprocessing time       : 0.017 s
% 3.10/3.34  # Presaturation interreduction done
% 3.10/3.34  
% 3.10/3.34  # Proof found!
% 3.10/3.34  # SZS status Theorem
% 3.10/3.34  # SZS output start CNFRefutation
% 3.10/3.34  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 3.10/3.34  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.10/3.34  fof(t21_xboole_1, axiom, ![X1, X2]:k3_xboole_0(X1,k2_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_xboole_1)).
% 3.10/3.34  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.10/3.34  fof(t92_xboole_1, axiom, ![X1]:k5_xboole_0(X1,X1)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 3.10/3.34  fof(t5_boole, axiom, ![X1]:k5_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 3.10/3.34  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.10/3.34  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 3.10/3.34  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 3.10/3.34  fof(commutativity_k5_xboole_0, axiom, ![X1, X2]:k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 3.10/3.34  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.10/3.34  fof(t91_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 3.10/3.34  fof(t49_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 3.10/3.34  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.10/3.34  fof(t106_xboole_1, conjecture, ![X1, X2, X3]:(r1_tarski(X1,k4_xboole_0(X2,X3))=>(r1_tarski(X1,X2)&r1_xboole_0(X1,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 3.10/3.34  fof(c_0_15, plain, ![X34, X35]:k2_xboole_0(X34,X35)=k5_xboole_0(X34,k4_xboole_0(X35,X34)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 3.10/3.34  fof(c_0_16, plain, ![X18, X19]:k4_xboole_0(X18,X19)=k5_xboole_0(X18,k3_xboole_0(X18,X19)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 3.10/3.34  fof(c_0_17, plain, ![X22, X23]:k3_xboole_0(X22,k2_xboole_0(X22,X23))=X22, inference(variable_rename,[status(thm)],[t21_xboole_1])).
% 3.10/3.34  cnf(c_0_18, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 3.10/3.34  cnf(c_0_19, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 3.10/3.34  cnf(c_0_20, plain, (k3_xboole_0(X1,k2_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_17])).
% 3.10/3.34  cnf(c_0_21, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))), inference(rw,[status(thm)],[c_0_18, c_0_19])).
% 3.10/3.34  fof(c_0_22, plain, ![X24, X25]:(~r1_tarski(X24,X25)|k3_xboole_0(X24,X25)=X24), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 3.10/3.34  fof(c_0_23, plain, ![X33]:k5_xboole_0(X33,X33)=k1_xboole_0, inference(variable_rename,[status(thm)],[t92_xboole_1])).
% 3.10/3.34  fof(c_0_24, plain, ![X29]:k5_xboole_0(X29,k1_xboole_0)=X29, inference(variable_rename,[status(thm)],[t5_boole])).
% 3.10/3.34  fof(c_0_25, plain, ![X10, X11, X13, X14, X15]:(((r2_hidden(esk1_2(X10,X11),X10)|r1_xboole_0(X10,X11))&(r2_hidden(esk1_2(X10,X11),X11)|r1_xboole_0(X10,X11)))&(~r2_hidden(X15,X13)|~r2_hidden(X15,X14)|~r1_xboole_0(X13,X14))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 3.10/3.34  cnf(c_0_26, plain, (k3_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))=X1), inference(rw,[status(thm)],[c_0_20, c_0_21])).
% 3.10/3.34  cnf(c_0_27, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 3.10/3.34  cnf(c_0_28, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_23])).
% 3.10/3.34  cnf(c_0_29, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_24])).
% 3.10/3.34  fof(c_0_30, plain, ![X20, X21]:r1_tarski(k3_xboole_0(X20,X21),X20), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 3.10/3.34  cnf(c_0_31, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 3.10/3.34  cnf(c_0_32, plain, (r2_hidden(esk1_2(X1,X2),X2)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 3.10/3.34  fof(c_0_33, plain, ![X8, X9]:((~r1_xboole_0(X8,X9)|k3_xboole_0(X8,X9)=k1_xboole_0)&(k3_xboole_0(X8,X9)!=k1_xboole_0|r1_xboole_0(X8,X9))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 3.10/3.34  cnf(c_0_34, plain, (k3_xboole_0(X1,X1)=X1|~r1_tarski(X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28]), c_0_29])).
% 3.10/3.34  cnf(c_0_35, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 3.10/3.34  cnf(c_0_36, plain, (r1_xboole_0(X1,X2)|~r2_hidden(esk1_2(X1,X2),X3)|~r1_xboole_0(X3,X2)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 3.10/3.34  cnf(c_0_37, plain, (r1_xboole_0(X1,X2)|k3_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_33])).
% 3.10/3.34  cnf(c_0_38, plain, (k3_xboole_0(X1,X1)=X1), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 3.10/3.34  cnf(c_0_39, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 3.10/3.34  cnf(c_0_40, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(X2,X2)), inference(spm,[status(thm)],[c_0_36, c_0_32])).
% 3.10/3.34  cnf(c_0_41, plain, (r1_xboole_0(X1,X1)|X1!=k1_xboole_0), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 3.10/3.34  fof(c_0_42, plain, ![X6, X7]:k5_xboole_0(X6,X7)=k5_xboole_0(X7,X6), inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).
% 3.10/3.34  fof(c_0_43, plain, ![X16, X17]:((k4_xboole_0(X16,X17)!=k1_xboole_0|r1_tarski(X16,X17))&(~r1_tarski(X16,X17)|k4_xboole_0(X16,X17)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 3.10/3.34  cnf(c_0_44, plain, (r1_tarski(k1_xboole_0,X1)|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_35, c_0_39])).
% 3.10/3.34  cnf(c_0_45, plain, (r1_xboole_0(X1,X2)|X2!=k1_xboole_0), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 3.10/3.34  fof(c_0_46, plain, ![X30, X31, X32]:k5_xboole_0(k5_xboole_0(X30,X31),X32)=k5_xboole_0(X30,k5_xboole_0(X31,X32)), inference(variable_rename,[status(thm)],[t91_xboole_1])).
% 3.10/3.34  cnf(c_0_47, plain, (k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 3.10/3.34  fof(c_0_48, plain, ![X26, X27, X28]:k3_xboole_0(X26,k4_xboole_0(X27,X28))=k4_xboole_0(k3_xboole_0(X26,X27),X28), inference(variable_rename,[status(thm)],[t49_xboole_1])).
% 3.10/3.34  cnf(c_0_49, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 3.10/3.34  cnf(c_0_50, plain, (r1_tarski(k1_xboole_0,X1)|X2!=k1_xboole_0), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 3.10/3.34  cnf(c_0_51, plain, (k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 3.10/3.34  cnf(c_0_52, plain, (k5_xboole_0(k1_xboole_0,X1)=X1), inference(spm,[status(thm)],[c_0_29, c_0_47])).
% 3.10/3.34  cnf(c_0_53, plain, (k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 3.10/3.34  fof(c_0_54, plain, ![X4, X5]:k3_xboole_0(X4,X5)=k3_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 3.10/3.34  cnf(c_0_55, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X2))=k1_xboole_0|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_49, c_0_19])).
% 3.10/3.34  cnf(c_0_56, plain, (r1_tarski(k1_xboole_0,X1)), inference(er,[status(thm)],[c_0_50])).
% 3.10/3.34  cnf(c_0_57, plain, (k5_xboole_0(X1,k5_xboole_0(X1,X2))=X2), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_28]), c_0_52])).
% 3.10/3.34  cnf(c_0_58, plain, (k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))=k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k3_xboole_0(X1,X2),X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53, c_0_19]), c_0_19])).
% 3.10/3.34  cnf(c_0_59, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 3.10/3.34  cnf(c_0_60, plain, (k3_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_55]), c_0_56])])).
% 3.10/3.34  fof(c_0_61, negated_conjecture, ~(![X1, X2, X3]:(r1_tarski(X1,k4_xboole_0(X2,X3))=>(r1_tarski(X1,X2)&r1_xboole_0(X1,X3)))), inference(assume_negation,[status(cth)],[t106_xboole_1])).
% 3.10/3.34  cnf(c_0_62, plain, (k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))))=k3_xboole_0(k3_xboole_0(X1,X2),X3)), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 3.10/3.34  cnf(c_0_63, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 3.10/3.34  fof(c_0_64, negated_conjecture, (r1_tarski(esk2_0,k4_xboole_0(esk3_0,esk4_0))&(~r1_tarski(esk2_0,esk3_0)|~r1_xboole_0(esk2_0,esk4_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_61])])])).
% 3.10/3.34  cnf(c_0_65, plain, (k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,k3_xboole_0(X1,X2))))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_38]), c_0_28])).
% 3.10/3.34  cnf(c_0_66, plain, (k3_xboole_0(X1,k3_xboole_0(X2,X1))=k3_xboole_0(X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_38]), c_0_28]), c_0_63]), c_0_29]), c_0_59])).
% 3.10/3.34  cnf(c_0_67, plain, (k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X1)))))=X1), inference(spm,[status(thm)],[c_0_26, c_0_58])).
% 3.10/3.34  cnf(c_0_68, negated_conjecture, (r1_tarski(esk2_0,k4_xboole_0(esk3_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_64])).
% 3.10/3.34  cnf(c_0_69, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 3.10/3.34  cnf(c_0_70, plain, (k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2)))=k1_xboole_0), inference(rw,[status(thm)],[c_0_65, c_0_66])).
% 3.10/3.34  cnf(c_0_71, plain, (k3_xboole_0(X1,k5_xboole_0(X1,X2))=X1|~r1_tarski(X2,k5_xboole_0(X3,k3_xboole_0(X3,X1)))), inference(spm,[status(thm)],[c_0_67, c_0_27])).
% 3.10/3.34  cnf(c_0_72, negated_conjecture, (r1_tarski(esk2_0,k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,esk4_0)))), inference(rw,[status(thm)],[c_0_68, c_0_19])).
% 3.10/3.34  cnf(c_0_73, plain, (r1_xboole_0(X1,X2)|~r2_hidden(esk1_2(X1,X2),X3)|~r1_xboole_0(X3,X1)), inference(spm,[status(thm)],[c_0_31, c_0_69])).
% 3.10/3.34  cnf(c_0_74, plain, (r1_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2)))), inference(spm,[status(thm)],[c_0_37, c_0_70])).
% 3.10/3.34  cnf(c_0_75, negated_conjecture, (k3_xboole_0(esk4_0,k5_xboole_0(esk2_0,esk4_0))=esk4_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_47])).
% 3.10/3.34  cnf(c_0_76, plain, (k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))=k3_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X1,X3)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_58])).
% 3.10/3.34  cnf(c_0_77, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_73, c_0_32])).
% 3.10/3.34  cnf(c_0_78, negated_conjecture, (r1_xboole_0(esk4_0,esk2_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_75]), c_0_51]), c_0_28]), c_0_29])).
% 3.10/3.34  cnf(c_0_79, plain, (r1_tarski(X1,X2)|k4_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_43])).
% 3.10/3.34  cnf(c_0_80, plain, (k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))=X2|~r1_tarski(X2,k5_xboole_0(X1,k3_xboole_0(X1,X3)))), inference(spm,[status(thm)],[c_0_27, c_0_76])).
% 3.10/3.34  cnf(c_0_81, negated_conjecture, (k3_xboole_0(esk2_0,esk4_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_75]), c_0_51]), c_0_28]), c_0_29]), c_0_59])).
% 3.10/3.34  cnf(c_0_82, negated_conjecture, (~r1_tarski(esk2_0,esk3_0)|~r1_xboole_0(esk2_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_64])).
% 3.10/3.34  cnf(c_0_83, negated_conjecture, (r1_xboole_0(esk2_0,esk4_0)), inference(spm,[status(thm)],[c_0_77, c_0_78])).
% 3.10/3.34  cnf(c_0_84, plain, (r1_tarski(X1,X2)|k5_xboole_0(X1,k3_xboole_0(X1,X2))!=k1_xboole_0), inference(rw,[status(thm)],[c_0_79, c_0_19])).
% 3.10/3.34  cnf(c_0_85, negated_conjecture, (k3_xboole_0(esk2_0,esk3_0)=esk2_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_72]), c_0_81]), c_0_29]), c_0_59])).
% 3.10/3.34  cnf(c_0_86, negated_conjecture, (~r1_tarski(esk2_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_82, c_0_83])])).
% 3.10/3.34  cnf(c_0_87, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_85]), c_0_28])]), c_0_86]), ['proof']).
% 3.10/3.34  # SZS output end CNFRefutation
% 3.10/3.34  # Proof object total steps             : 88
% 3.10/3.34  # Proof object clause steps            : 57
% 3.10/3.34  # Proof object formula steps           : 31
% 3.10/3.34  # Proof object conjectures             : 13
% 3.10/3.34  # Proof object clause conjectures      : 10
% 3.10/3.34  # Proof object formula conjectures     : 3
% 3.10/3.34  # Proof object initial clauses used    : 20
% 3.10/3.34  # Proof object initial formulas used   : 15
% 3.10/3.34  # Proof object generating inferences   : 29
% 3.10/3.34  # Proof object simplifying inferences  : 35
% 3.10/3.34  # Training examples: 0 positive, 0 negative
% 3.10/3.34  # Parsed axioms                        : 15
% 3.10/3.34  # Removed by relevancy pruning/SinE    : 0
% 3.10/3.34  # Initial clauses                      : 20
% 3.10/3.34  # Removed in clause preprocessing      : 2
% 3.10/3.34  # Initial clauses in saturation        : 18
% 3.10/3.34  # Processed clauses                    : 12305
% 3.10/3.34  # ...of these trivial                  : 302
% 3.10/3.34  # ...subsumed                          : 10820
% 3.10/3.34  # ...remaining for further processing  : 1183
% 3.10/3.34  # Other redundant clauses eliminated   : 0
% 3.10/3.34  # Clauses deleted for lack of memory   : 0
% 3.10/3.34  # Backward-subsumed                    : 66
% 3.10/3.34  # Backward-rewritten                   : 91
% 3.10/3.34  # Generated clauses                    : 386310
% 3.10/3.34  # ...of the previous two non-trivial   : 339211
% 3.10/3.34  # Contextual simplify-reflections      : 13
% 3.10/3.34  # Paramodulations                      : 386305
% 3.10/3.34  # Factorizations                       : 0
% 3.10/3.34  # Equation resolutions                 : 5
% 3.10/3.34  # Propositional unsat checks           : 0
% 3.10/3.34  #    Propositional check models        : 0
% 3.10/3.34  #    Propositional check unsatisfiable : 0
% 3.10/3.34  #    Propositional clauses             : 0
% 3.10/3.34  #    Propositional clauses after purity: 0
% 3.10/3.34  #    Propositional unsat core size     : 0
% 3.10/3.34  #    Propositional preprocessing time  : 0.000
% 3.10/3.34  #    Propositional encoding time       : 0.000
% 3.10/3.34  #    Propositional solver time         : 0.000
% 3.10/3.34  #    Success case prop preproc time    : 0.000
% 3.10/3.34  #    Success case prop encoding time   : 0.000
% 3.10/3.34  #    Success case prop solver time     : 0.000
% 3.10/3.34  # Current number of processed clauses  : 1008
% 3.10/3.34  #    Positive orientable unit clauses  : 136
% 3.10/3.34  #    Positive unorientable unit clauses: 10
% 3.10/3.34  #    Negative unit clauses             : 41
% 3.10/3.34  #    Non-unit-clauses                  : 821
% 3.10/3.34  # Current number of unprocessed clauses: 326789
% 3.10/3.34  # ...number of literals in the above   : 843880
% 3.10/3.34  # Current number of archived formulas  : 0
% 3.10/3.34  # Current number of archived clauses   : 177
% 3.10/3.34  # Clause-clause subsumption calls (NU) : 63339
% 3.10/3.34  # Rec. Clause-clause subsumption calls : 55608
% 3.10/3.34  # Non-unit clause-clause subsumptions  : 5779
% 3.10/3.34  # Unit Clause-clause subsumption calls : 4419
% 3.10/3.34  # Rewrite failures with RHS unbound    : 0
% 3.10/3.34  # BW rewrite match attempts            : 3070
% 3.10/3.34  # BW rewrite match successes           : 231
% 3.10/3.34  # Condensation attempts                : 0
% 3.10/3.34  # Condensation successes               : 0
% 3.10/3.34  # Termbank termtop insertions          : 8480585
% 3.20/3.35  
% 3.20/3.35  # -------------------------------------------------
% 3.20/3.35  # User time                : 2.857 s
% 3.20/3.35  # System time              : 0.137 s
% 3.20/3.35  # Total time               : 2.995 s
% 3.20/3.35  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
