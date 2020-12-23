%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:34:54 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 272 expanded)
%              Number of clauses        :   47 ( 119 expanded)
%              Number of leaves         :   17 (  74 expanded)
%              Depth                    :   13
%              Number of atoms          :  116 ( 353 expanded)
%              Number of equality atoms :   51 ( 214 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t110_xboole_1,conjecture,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X3,X2) )
     => r1_tarski(k5_xboole_0(X1,X3),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t110_xboole_1)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t49_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t93_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t93_xboole_1)).

fof(t16_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(l97_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l97_xboole_1)).

fof(commutativity_k5_xboole_0,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(t91_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(t92_xboole_1,axiom,(
    ! [X1] : k5_xboole_0(X1,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(t5_boole,axiom,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(t18_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k3_xboole_0(X2,X3))
     => r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_xboole_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t97_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(k4_xboole_0(X1,X2),X3)
        & r1_tarski(k4_xboole_0(X2,X1),X3) )
     => r1_tarski(k5_xboole_0(X1,X2),X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_xboole_1)).

fof(c_0_17,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( r1_tarski(X1,X2)
          & r1_tarski(X3,X2) )
       => r1_tarski(k5_xboole_0(X1,X3),X2) ) ),
    inference(assume_negation,[status(cth)],[t110_xboole_1])).

fof(c_0_18,plain,(
    ! [X41,X42] : k2_xboole_0(X41,X42) = k5_xboole_0(X41,k4_xboole_0(X42,X41)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_19,plain,(
    ! [X16,X17] : k4_xboole_0(X16,X17) = k5_xboole_0(X16,k3_xboole_0(X16,X17)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_20,plain,(
    ! [X28,X29,X30] : k3_xboole_0(X28,k4_xboole_0(X29,X30)) = k4_xboole_0(k3_xboole_0(X28,X29),X30) ),
    inference(variable_rename,[status(thm)],[t49_xboole_1])).

fof(c_0_21,plain,(
    ! [X24,X25] :
      ( ~ r1_tarski(X24,X25)
      | k3_xboole_0(X24,X25) = X24 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

fof(c_0_22,negated_conjecture,
    ( r1_tarski(esk3_0,esk4_0)
    & r1_tarski(esk5_0,esk4_0)
    & ~ r1_tarski(k5_xboole_0(esk3_0,esk5_0),esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).

fof(c_0_23,plain,(
    ! [X36,X37] : k2_xboole_0(X36,X37) = k2_xboole_0(k5_xboole_0(X36,X37),k3_xboole_0(X36,X37)) ),
    inference(variable_rename,[status(thm)],[t93_xboole_1])).

cnf(c_0_24,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_27,plain,(
    ! [X18,X19,X20] : k3_xboole_0(k3_xboole_0(X18,X19),X20) = k3_xboole_0(X18,k3_xboole_0(X19,X20)) ),
    inference(variable_rename,[status(thm)],[t16_xboole_1])).

fof(c_0_28,plain,(
    ! [X6,X7,X9,X10,X11] :
      ( ( r1_xboole_0(X6,X7)
        | r2_hidden(esk1_2(X6,X7),k3_xboole_0(X6,X7)) )
      & ( ~ r2_hidden(X11,k3_xboole_0(X9,X10))
        | ~ r1_xboole_0(X9,X10) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

fof(c_0_29,plain,(
    ! [X12] :
      ( X12 = k1_xboole_0
      | r2_hidden(esk2_1(X12),X12) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

fof(c_0_30,plain,(
    ! [X14,X15] : r1_xboole_0(k3_xboole_0(X14,X15),k5_xboole_0(X14,X15)) ),
    inference(variable_rename,[status(thm)],[l97_xboole_1])).

cnf(c_0_31,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_32,negated_conjecture,
    ( r1_tarski(esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_33,plain,(
    ! [X4,X5] : k5_xboole_0(X4,X5) = k5_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).

fof(c_0_34,plain,(
    ! [X32,X33,X34] : k5_xboole_0(k5_xboole_0(X32,X33),X34) = k5_xboole_0(X32,k5_xboole_0(X33,X34)) ),
    inference(variable_rename,[status(thm)],[t91_xboole_1])).

cnf(c_0_35,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_36,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(rw,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_37,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))) = k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k3_xboole_0(X1,X2),X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_25]),c_0_25])).

cnf(c_0_38,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_39,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_40,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk2_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_41,plain,
    ( r1_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_42,negated_conjecture,
    ( k3_xboole_0(esk5_0,esk4_0) = esk5_0 ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_43,plain,
    ( k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_44,negated_conjecture,
    ( r1_tarski(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_45,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

fof(c_0_46,plain,(
    ! [X35] : k5_xboole_0(X35,X35) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t92_xboole_1])).

fof(c_0_47,plain,(
    ! [X31] : k5_xboole_0(X31,k1_xboole_0) = X31 ),
    inference(variable_rename,[status(thm)],[t5_boole])).

cnf(c_0_48,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) = k5_xboole_0(k5_xboole_0(X1,X2),k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_36]),c_0_36])).

cnf(c_0_49,plain,
    ( k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,k3_xboole_0(X2,X3))) = k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))) ),
    inference(rw,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_50,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_51,negated_conjecture,
    ( r1_xboole_0(esk5_0,k5_xboole_0(esk4_0,esk5_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_43])).

cnf(c_0_52,negated_conjecture,
    ( k3_xboole_0(esk3_0,esk4_0) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_31,c_0_44])).

cnf(c_0_53,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,X3)) = k5_xboole_0(X3,k5_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_45])).

cnf(c_0_54,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_55,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_56,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,k5_xboole_0(X1,X2)))))) = k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_38]),c_0_49]),c_0_45])).

cnf(c_0_57,negated_conjecture,
    ( k3_xboole_0(esk5_0,k5_xboole_0(esk4_0,esk5_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_58,negated_conjecture,
    ( r1_xboole_0(esk3_0,k5_xboole_0(esk4_0,esk3_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_52]),c_0_43])).

cnf(c_0_59,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,X2)) = X2 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_55])).

cnf(c_0_60,negated_conjecture,
    ( k5_xboole_0(esk4_0,k5_xboole_0(esk5_0,k3_xboole_0(esk4_0,esk5_0))) = esk4_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_55]),c_0_42]),c_0_54]),c_0_55])).

cnf(c_0_61,negated_conjecture,
    ( k3_xboole_0(esk3_0,k5_xboole_0(esk4_0,esk3_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_50,c_0_58])).

fof(c_0_62,plain,(
    ! [X21,X22,X23] :
      ( ~ r1_tarski(X21,k3_xboole_0(X22,X23))
      | r1_tarski(X21,X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t18_xboole_1])])).

cnf(c_0_63,negated_conjecture,
    ( k5_xboole_0(esk5_0,k3_xboole_0(esk4_0,esk5_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_54])).

fof(c_0_64,plain,(
    ! [X26,X27] : r1_tarski(k4_xboole_0(X26,X27),X26) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

cnf(c_0_65,negated_conjecture,
    ( k5_xboole_0(esk4_0,k5_xboole_0(esk3_0,k3_xboole_0(esk4_0,esk3_0))) = esk4_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_61]),c_0_55]),c_0_52]),c_0_54]),c_0_55])).

fof(c_0_66,plain,(
    ! [X38,X39,X40] :
      ( ~ r1_tarski(k4_xboole_0(X38,X39),X40)
      | ~ r1_tarski(k4_xboole_0(X39,X38),X40)
      | r1_tarski(k5_xboole_0(X38,X39),X40) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t97_xboole_1])])).

cnf(c_0_67,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k3_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_68,negated_conjecture,
    ( k3_xboole_0(esk4_0,esk5_0) = esk5_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_63]),c_0_55])).

cnf(c_0_69,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_70,negated_conjecture,
    ( k5_xboole_0(esk3_0,k3_xboole_0(esk4_0,esk3_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_65]),c_0_54])).

cnf(c_0_71,plain,
    ( r1_tarski(k5_xboole_0(X1,X2),X3)
    | ~ r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(k4_xboole_0(X2,X1),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_72,negated_conjecture,
    ( r1_tarski(X1,esk4_0)
    | ~ r1_tarski(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_73,plain,
    ( r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X1) ),
    inference(rw,[status(thm)],[c_0_69,c_0_25])).

cnf(c_0_74,negated_conjecture,
    ( k3_xboole_0(esk4_0,esk3_0) = esk3_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_70]),c_0_55])).

cnf(c_0_75,plain,
    ( r1_tarski(k5_xboole_0(X1,X2),X3)
    | ~ r1_tarski(k5_xboole_0(X2,k3_xboole_0(X2,X1)),X3)
    | ~ r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_71,c_0_25]),c_0_25])).

cnf(c_0_76,negated_conjecture,
    ( r1_tarski(k5_xboole_0(esk5_0,k3_xboole_0(esk5_0,X1)),esk4_0) ),
    inference(spm,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_77,negated_conjecture,
    ( r1_tarski(X1,esk4_0)
    | ~ r1_tarski(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_67,c_0_74])).

cnf(c_0_78,negated_conjecture,
    ( r1_tarski(k5_xboole_0(X1,esk5_0),esk4_0)
    | ~ r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,esk5_0)),esk4_0) ),
    inference(spm,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_79,negated_conjecture,
    ( r1_tarski(k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,X1)),esk4_0) ),
    inference(spm,[status(thm)],[c_0_77,c_0_73])).

cnf(c_0_80,negated_conjecture,
    ( ~ r1_tarski(k5_xboole_0(esk3_0,esk5_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_81,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_80]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:16:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.21/0.41  # AutoSched0-Mode selected heuristic G_E___103_C18_F1_PI_AE_Q4_CS_SP_S0Y
% 0.21/0.41  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.21/0.41  #
% 0.21/0.41  # Preprocessing time       : 0.027 s
% 0.21/0.41  
% 0.21/0.41  # Proof found!
% 0.21/0.41  # SZS status Theorem
% 0.21/0.41  # SZS output start CNFRefutation
% 0.21/0.41  fof(t110_xboole_1, conjecture, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X3,X2))=>r1_tarski(k5_xboole_0(X1,X3),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t110_xboole_1)).
% 0.21/0.41  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.21/0.41  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.21/0.41  fof(t49_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 0.21/0.41  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.21/0.41  fof(t93_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t93_xboole_1)).
% 0.21/0.41  fof(t16_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(k3_xboole_0(X1,X2),X3)=k3_xboole_0(X1,k3_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_xboole_1)).
% 0.21/0.41  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 0.21/0.41  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 0.21/0.41  fof(l97_xboole_1, axiom, ![X1, X2]:r1_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l97_xboole_1)).
% 0.21/0.41  fof(commutativity_k5_xboole_0, axiom, ![X1, X2]:k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 0.21/0.41  fof(t91_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 0.21/0.41  fof(t92_xboole_1, axiom, ![X1]:k5_xboole_0(X1,X1)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 0.21/0.41  fof(t5_boole, axiom, ![X1]:k5_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 0.21/0.41  fof(t18_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k3_xboole_0(X2,X3))=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_xboole_1)).
% 0.21/0.41  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.21/0.41  fof(t97_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(k4_xboole_0(X1,X2),X3)&r1_tarski(k4_xboole_0(X2,X1),X3))=>r1_tarski(k5_xboole_0(X1,X2),X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_xboole_1)).
% 0.21/0.41  fof(c_0_17, negated_conjecture, ~(![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X3,X2))=>r1_tarski(k5_xboole_0(X1,X3),X2))), inference(assume_negation,[status(cth)],[t110_xboole_1])).
% 0.21/0.41  fof(c_0_18, plain, ![X41, X42]:k2_xboole_0(X41,X42)=k5_xboole_0(X41,k4_xboole_0(X42,X41)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.21/0.41  fof(c_0_19, plain, ![X16, X17]:k4_xboole_0(X16,X17)=k5_xboole_0(X16,k3_xboole_0(X16,X17)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.21/0.41  fof(c_0_20, plain, ![X28, X29, X30]:k3_xboole_0(X28,k4_xboole_0(X29,X30))=k4_xboole_0(k3_xboole_0(X28,X29),X30), inference(variable_rename,[status(thm)],[t49_xboole_1])).
% 0.21/0.41  fof(c_0_21, plain, ![X24, X25]:(~r1_tarski(X24,X25)|k3_xboole_0(X24,X25)=X24), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.21/0.41  fof(c_0_22, negated_conjecture, ((r1_tarski(esk3_0,esk4_0)&r1_tarski(esk5_0,esk4_0))&~r1_tarski(k5_xboole_0(esk3_0,esk5_0),esk4_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).
% 0.21/0.41  fof(c_0_23, plain, ![X36, X37]:k2_xboole_0(X36,X37)=k2_xboole_0(k5_xboole_0(X36,X37),k3_xboole_0(X36,X37)), inference(variable_rename,[status(thm)],[t93_xboole_1])).
% 0.21/0.41  cnf(c_0_24, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.21/0.41  cnf(c_0_25, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.21/0.41  cnf(c_0_26, plain, (k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.21/0.41  fof(c_0_27, plain, ![X18, X19, X20]:k3_xboole_0(k3_xboole_0(X18,X19),X20)=k3_xboole_0(X18,k3_xboole_0(X19,X20)), inference(variable_rename,[status(thm)],[t16_xboole_1])).
% 0.21/0.41  fof(c_0_28, plain, ![X6, X7, X9, X10, X11]:((r1_xboole_0(X6,X7)|r2_hidden(esk1_2(X6,X7),k3_xboole_0(X6,X7)))&(~r2_hidden(X11,k3_xboole_0(X9,X10))|~r1_xboole_0(X9,X10))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 0.21/0.41  fof(c_0_29, plain, ![X12]:(X12=k1_xboole_0|r2_hidden(esk2_1(X12),X12)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 0.21/0.41  fof(c_0_30, plain, ![X14, X15]:r1_xboole_0(k3_xboole_0(X14,X15),k5_xboole_0(X14,X15)), inference(variable_rename,[status(thm)],[l97_xboole_1])).
% 0.21/0.41  cnf(c_0_31, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.21/0.41  cnf(c_0_32, negated_conjecture, (r1_tarski(esk5_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.21/0.41  fof(c_0_33, plain, ![X4, X5]:k5_xboole_0(X4,X5)=k5_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).
% 0.21/0.41  fof(c_0_34, plain, ![X32, X33, X34]:k5_xboole_0(k5_xboole_0(X32,X33),X34)=k5_xboole_0(X32,k5_xboole_0(X33,X34)), inference(variable_rename,[status(thm)],[t91_xboole_1])).
% 0.21/0.41  cnf(c_0_35, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.21/0.41  cnf(c_0_36, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))), inference(rw,[status(thm)],[c_0_24, c_0_25])).
% 0.21/0.41  cnf(c_0_37, plain, (k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))=k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k3_xboole_0(X1,X2),X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26, c_0_25]), c_0_25])).
% 0.21/0.41  cnf(c_0_38, plain, (k3_xboole_0(k3_xboole_0(X1,X2),X3)=k3_xboole_0(X1,k3_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.21/0.41  cnf(c_0_39, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.21/0.41  cnf(c_0_40, plain, (X1=k1_xboole_0|r2_hidden(esk2_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.21/0.41  cnf(c_0_41, plain, (r1_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.21/0.41  cnf(c_0_42, negated_conjecture, (k3_xboole_0(esk5_0,esk4_0)=esk5_0), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.21/0.41  cnf(c_0_43, plain, (k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.21/0.41  cnf(c_0_44, negated_conjecture, (r1_tarski(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.21/0.41  cnf(c_0_45, plain, (k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.21/0.41  fof(c_0_46, plain, ![X35]:k5_xboole_0(X35,X35)=k1_xboole_0, inference(variable_rename,[status(thm)],[t92_xboole_1])).
% 0.21/0.41  fof(c_0_47, plain, ![X31]:k5_xboole_0(X31,k1_xboole_0)=X31, inference(variable_rename,[status(thm)],[t5_boole])).
% 0.21/0.41  cnf(c_0_48, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))=k5_xboole_0(k5_xboole_0(X1,X2),k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_36]), c_0_36])).
% 0.21/0.41  cnf(c_0_49, plain, (k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,k3_xboole_0(X2,X3)))=k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))), inference(rw,[status(thm)],[c_0_37, c_0_38])).
% 0.21/0.41  cnf(c_0_50, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.21/0.41  cnf(c_0_51, negated_conjecture, (r1_xboole_0(esk5_0,k5_xboole_0(esk4_0,esk5_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_43])).
% 0.21/0.41  cnf(c_0_52, negated_conjecture, (k3_xboole_0(esk3_0,esk4_0)=esk3_0), inference(spm,[status(thm)],[c_0_31, c_0_44])).
% 0.21/0.41  cnf(c_0_53, plain, (k5_xboole_0(X1,k5_xboole_0(X2,X3))=k5_xboole_0(X3,k5_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_43, c_0_45])).
% 0.21/0.41  cnf(c_0_54, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.21/0.41  cnf(c_0_55, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.21/0.41  cnf(c_0_56, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,k5_xboole_0(X1,X2))))))=k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48, c_0_38]), c_0_49]), c_0_45])).
% 0.21/0.41  cnf(c_0_57, negated_conjecture, (k3_xboole_0(esk5_0,k5_xboole_0(esk4_0,esk5_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.21/0.41  cnf(c_0_58, negated_conjecture, (r1_xboole_0(esk3_0,k5_xboole_0(esk4_0,esk3_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_52]), c_0_43])).
% 0.21/0.41  cnf(c_0_59, plain, (k5_xboole_0(X1,k5_xboole_0(X1,X2))=X2), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_55])).
% 0.21/0.41  cnf(c_0_60, negated_conjecture, (k5_xboole_0(esk4_0,k5_xboole_0(esk5_0,k3_xboole_0(esk4_0,esk5_0)))=esk4_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_55]), c_0_42]), c_0_54]), c_0_55])).
% 0.21/0.41  cnf(c_0_61, negated_conjecture, (k3_xboole_0(esk3_0,k5_xboole_0(esk4_0,esk3_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_50, c_0_58])).
% 0.21/0.41  fof(c_0_62, plain, ![X21, X22, X23]:(~r1_tarski(X21,k3_xboole_0(X22,X23))|r1_tarski(X21,X22)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t18_xboole_1])])).
% 0.21/0.41  cnf(c_0_63, negated_conjecture, (k5_xboole_0(esk5_0,k3_xboole_0(esk4_0,esk5_0))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_54])).
% 0.21/0.41  fof(c_0_64, plain, ![X26, X27]:r1_tarski(k4_xboole_0(X26,X27),X26), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.21/0.41  cnf(c_0_65, negated_conjecture, (k5_xboole_0(esk4_0,k5_xboole_0(esk3_0,k3_xboole_0(esk4_0,esk3_0)))=esk4_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_61]), c_0_55]), c_0_52]), c_0_54]), c_0_55])).
% 0.21/0.41  fof(c_0_66, plain, ![X38, X39, X40]:(~r1_tarski(k4_xboole_0(X38,X39),X40)|~r1_tarski(k4_xboole_0(X39,X38),X40)|r1_tarski(k5_xboole_0(X38,X39),X40)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t97_xboole_1])])).
% 0.21/0.41  cnf(c_0_67, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k3_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.21/0.41  cnf(c_0_68, negated_conjecture, (k3_xboole_0(esk4_0,esk5_0)=esk5_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_63]), c_0_55])).
% 0.21/0.41  cnf(c_0_69, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.21/0.41  cnf(c_0_70, negated_conjecture, (k5_xboole_0(esk3_0,k3_xboole_0(esk4_0,esk3_0))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_65]), c_0_54])).
% 0.21/0.41  cnf(c_0_71, plain, (r1_tarski(k5_xboole_0(X1,X2),X3)|~r1_tarski(k4_xboole_0(X1,X2),X3)|~r1_tarski(k4_xboole_0(X2,X1),X3)), inference(split_conjunct,[status(thm)],[c_0_66])).
% 0.21/0.41  cnf(c_0_72, negated_conjecture, (r1_tarski(X1,esk4_0)|~r1_tarski(X1,esk5_0)), inference(spm,[status(thm)],[c_0_67, c_0_68])).
% 0.21/0.41  cnf(c_0_73, plain, (r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X1)), inference(rw,[status(thm)],[c_0_69, c_0_25])).
% 0.21/0.41  cnf(c_0_74, negated_conjecture, (k3_xboole_0(esk4_0,esk3_0)=esk3_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_70]), c_0_55])).
% 0.21/0.41  cnf(c_0_75, plain, (r1_tarski(k5_xboole_0(X1,X2),X3)|~r1_tarski(k5_xboole_0(X2,k3_xboole_0(X2,X1)),X3)|~r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_71, c_0_25]), c_0_25])).
% 0.21/0.41  cnf(c_0_76, negated_conjecture, (r1_tarski(k5_xboole_0(esk5_0,k3_xboole_0(esk5_0,X1)),esk4_0)), inference(spm,[status(thm)],[c_0_72, c_0_73])).
% 0.21/0.41  cnf(c_0_77, negated_conjecture, (r1_tarski(X1,esk4_0)|~r1_tarski(X1,esk3_0)), inference(spm,[status(thm)],[c_0_67, c_0_74])).
% 0.21/0.41  cnf(c_0_78, negated_conjecture, (r1_tarski(k5_xboole_0(X1,esk5_0),esk4_0)|~r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,esk5_0)),esk4_0)), inference(spm,[status(thm)],[c_0_75, c_0_76])).
% 0.21/0.41  cnf(c_0_79, negated_conjecture, (r1_tarski(k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,X1)),esk4_0)), inference(spm,[status(thm)],[c_0_77, c_0_73])).
% 0.21/0.41  cnf(c_0_80, negated_conjecture, (~r1_tarski(k5_xboole_0(esk3_0,esk5_0),esk4_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.21/0.41  cnf(c_0_81, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_79]), c_0_80]), ['proof']).
% 0.21/0.41  # SZS output end CNFRefutation
% 0.21/0.41  # Proof object total steps             : 82
% 0.21/0.41  # Proof object clause steps            : 47
% 0.21/0.41  # Proof object formula steps           : 35
% 0.21/0.41  # Proof object conjectures             : 24
% 0.21/0.41  # Proof object clause conjectures      : 21
% 0.21/0.41  # Proof object formula conjectures     : 3
% 0.21/0.41  # Proof object initial clauses used    : 19
% 0.21/0.41  # Proof object initial formulas used   : 17
% 0.21/0.41  # Proof object generating inferences   : 21
% 0.21/0.41  # Proof object simplifying inferences  : 28
% 0.21/0.41  # Training examples: 0 positive, 0 negative
% 0.21/0.41  # Parsed axioms                        : 17
% 0.21/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.41  # Initial clauses                      : 20
% 0.21/0.41  # Removed in clause preprocessing      : 2
% 0.21/0.41  # Initial clauses in saturation        : 18
% 0.21/0.41  # Processed clauses                    : 301
% 0.21/0.41  # ...of these trivial                  : 61
% 0.21/0.41  # ...subsumed                          : 125
% 0.21/0.41  # ...remaining for further processing  : 115
% 0.21/0.41  # Other redundant clauses eliminated   : 0
% 0.21/0.41  # Clauses deleted for lack of memory   : 0
% 0.21/0.41  # Backward-subsumed                    : 0
% 0.21/0.41  # Backward-rewritten                   : 9
% 0.21/0.41  # Generated clauses                    : 2356
% 0.21/0.41  # ...of the previous two non-trivial   : 1794
% 0.21/0.41  # Contextual simplify-reflections      : 0
% 0.21/0.41  # Paramodulations                      : 2356
% 0.21/0.41  # Factorizations                       : 0
% 0.21/0.41  # Equation resolutions                 : 0
% 0.21/0.41  # Propositional unsat checks           : 0
% 0.21/0.41  #    Propositional check models        : 0
% 0.21/0.41  #    Propositional check unsatisfiable : 0
% 0.21/0.41  #    Propositional clauses             : 0
% 0.21/0.41  #    Propositional clauses after purity: 0
% 0.21/0.41  #    Propositional unsat core size     : 0
% 0.21/0.41  #    Propositional preprocessing time  : 0.000
% 0.21/0.41  #    Propositional encoding time       : 0.000
% 0.21/0.41  #    Propositional solver time         : 0.000
% 0.21/0.41  #    Success case prop preproc time    : 0.000
% 0.21/0.41  #    Success case prop encoding time   : 0.000
% 0.21/0.41  #    Success case prop solver time     : 0.000
% 0.21/0.41  # Current number of processed clauses  : 106
% 0.21/0.41  #    Positive orientable unit clauses  : 65
% 0.21/0.41  #    Positive unorientable unit clauses: 4
% 0.21/0.41  #    Negative unit clauses             : 2
% 0.21/0.41  #    Non-unit-clauses                  : 35
% 0.21/0.41  # Current number of unprocessed clauses: 1477
% 0.21/0.41  # ...number of literals in the above   : 1670
% 0.21/0.41  # Current number of archived formulas  : 0
% 0.21/0.41  # Current number of archived clauses   : 11
% 0.21/0.41  # Clause-clause subsumption calls (NU) : 170
% 0.21/0.41  # Rec. Clause-clause subsumption calls : 150
% 0.21/0.41  # Non-unit clause-clause subsumptions  : 15
% 0.21/0.41  # Unit Clause-clause subsumption calls : 32
% 0.21/0.41  # Rewrite failures with RHS unbound    : 0
% 0.21/0.41  # BW rewrite match attempts            : 134
% 0.21/0.41  # BW rewrite match successes           : 57
% 0.21/0.41  # Condensation attempts                : 0
% 0.21/0.41  # Condensation successes               : 0
% 0.21/0.41  # Termbank termtop insertions          : 51160
% 0.21/0.41  
% 0.21/0.41  # -------------------------------------------------
% 0.21/0.41  # User time                : 0.058 s
% 0.21/0.41  # System time              : 0.009 s
% 0.21/0.41  # Total time               : 0.068 s
% 0.21/0.41  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
