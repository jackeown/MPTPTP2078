%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:42:57 EST 2020

% Result     : Theorem 14.32s
% Output     : CNFRefutation 14.32s
% Verified   : 
% Statistics : Number of formulae       :   99 (1118 expanded)
%              Number of clauses        :   62 ( 508 expanded)
%              Number of leaves         :   18 ( 300 expanded)
%              Depth                    :   20
%              Number of atoms          :  211 (2125 expanded)
%              Number of equality atoms :   95 (1236 expanded)
%              Maximal formula depth    :   17 (   3 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t51_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(t52_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(X1,k4_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(d3_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            | r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(t49_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(t72_zfmisc_1,conjecture,(
    ! [X1,X2,X3] :
      ( k4_xboole_0(k2_tarski(X1,X2),X3) = k2_tarski(X1,X2)
    <=> ( ~ r2_hidden(X1,X3)
        & ~ r2_hidden(X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_zfmisc_1)).

fof(t47_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(t41_enumset1,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t65_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,k1_tarski(X2)) = X1
    <=> ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(c_0_18,plain,(
    ! [X35] : k3_xboole_0(X35,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

fof(c_0_19,plain,(
    ! [X50,X51] : k4_xboole_0(X50,k4_xboole_0(X50,X51)) = k3_xboole_0(X50,X51) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_20,plain,(
    ! [X56,X57] : k2_xboole_0(k3_xboole_0(X56,X57),k4_xboole_0(X56,X57)) = X56 ),
    inference(variable_rename,[status(thm)],[t51_xboole_1])).

fof(c_0_21,plain,(
    ! [X20,X21,X22,X23,X24,X25,X26,X27] :
      ( ( r2_hidden(X23,X20)
        | ~ r2_hidden(X23,X22)
        | X22 != k4_xboole_0(X20,X21) )
      & ( ~ r2_hidden(X23,X21)
        | ~ r2_hidden(X23,X22)
        | X22 != k4_xboole_0(X20,X21) )
      & ( ~ r2_hidden(X24,X20)
        | r2_hidden(X24,X21)
        | r2_hidden(X24,X22)
        | X22 != k4_xboole_0(X20,X21) )
      & ( ~ r2_hidden(esk2_3(X25,X26,X27),X27)
        | ~ r2_hidden(esk2_3(X25,X26,X27),X25)
        | r2_hidden(esk2_3(X25,X26,X27),X26)
        | X27 = k4_xboole_0(X25,X26) )
      & ( r2_hidden(esk2_3(X25,X26,X27),X25)
        | r2_hidden(esk2_3(X25,X26,X27),X27)
        | X27 = k4_xboole_0(X25,X26) )
      & ( ~ r2_hidden(esk2_3(X25,X26,X27),X26)
        | r2_hidden(esk2_3(X25,X26,X27),X27)
        | X27 = k4_xboole_0(X25,X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

fof(c_0_22,plain,(
    ! [X58,X59,X60] : k4_xboole_0(X58,k4_xboole_0(X59,X60)) = k2_xboole_0(k4_xboole_0(X58,X59),k3_xboole_0(X58,X60)) ),
    inference(variable_rename,[status(thm)],[t52_xboole_1])).

cnf(c_0_23,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_25,plain,(
    ! [X40] : k4_xboole_0(X40,k1_xboole_0) = X40 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

cnf(c_0_26,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_27,plain,(
    ! [X7,X8] : k2_xboole_0(X7,X8) = k2_xboole_0(X8,X7) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_28,plain,(
    ! [X38,X39] : k2_xboole_0(X38,k4_xboole_0(X39,X38)) = k2_xboole_0(X38,X39) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

cnf(c_0_29,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_30,plain,(
    ! [X43,X44,X45] : k4_xboole_0(k4_xboole_0(X43,X44),X45) = k4_xboole_0(X43,k2_xboole_0(X44,X45)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

cnf(c_0_31,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_32,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_33,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_34,plain,
    ( k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,X2)) = X1 ),
    inference(rw,[status(thm)],[c_0_26,c_0_24])).

cnf(c_0_35,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_36,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_37,plain,(
    ! [X11,X12,X13,X14,X15,X16,X17,X18] :
      ( ( ~ r2_hidden(X14,X13)
        | r2_hidden(X14,X11)
        | r2_hidden(X14,X12)
        | X13 != k2_xboole_0(X11,X12) )
      & ( ~ r2_hidden(X15,X11)
        | r2_hidden(X15,X13)
        | X13 != k2_xboole_0(X11,X12) )
      & ( ~ r2_hidden(X15,X12)
        | r2_hidden(X15,X13)
        | X13 != k2_xboole_0(X11,X12) )
      & ( ~ r2_hidden(esk1_3(X16,X17,X18),X16)
        | ~ r2_hidden(esk1_3(X16,X17,X18),X18)
        | X18 = k2_xboole_0(X16,X17) )
      & ( ~ r2_hidden(esk1_3(X16,X17,X18),X17)
        | ~ r2_hidden(esk1_3(X16,X17,X18),X18)
        | X18 = k2_xboole_0(X16,X17) )
      & ( r2_hidden(esk1_3(X16,X17,X18),X18)
        | r2_hidden(esk1_3(X16,X17,X18),X16)
        | r2_hidden(esk1_3(X16,X17,X18),X17)
        | X18 = k2_xboole_0(X16,X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).

fof(c_0_38,plain,(
    ! [X69,X70,X71,X72,X73,X74] :
      ( ( ~ r2_hidden(X71,X70)
        | X71 = X69
        | X70 != k1_tarski(X69) )
      & ( X72 != X69
        | r2_hidden(X72,X70)
        | X70 != k1_tarski(X69) )
      & ( ~ r2_hidden(esk4_2(X73,X74),X74)
        | esk4_2(X73,X74) != X73
        | X74 = k1_tarski(X73) )
      & ( r2_hidden(esk4_2(X73,X74),X74)
        | esk4_2(X73,X74) = X73
        | X74 = k1_tarski(X73) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

cnf(c_0_39,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_29])).

cnf(c_0_40,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_41,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X3))) ),
    inference(rw,[status(thm)],[c_0_31,c_0_24])).

cnf(c_0_42,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_43,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X1,X2)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_35]),c_0_36]),c_0_35])).

cnf(c_0_44,plain,
    ( r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X3 != k2_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_45,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_46,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(k4_xboole_0(X2,X3),X4))
    | ~ r2_hidden(X1,k2_xboole_0(X3,X4)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_47,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_33]),c_0_35]),c_0_43])).

cnf(c_0_48,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_44])).

cnf(c_0_49,plain,
    ( r2_hidden(X1,k1_tarski(X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_45])])).

fof(c_0_50,plain,(
    ! [X52,X53,X54] : k3_xboole_0(X52,k4_xboole_0(X53,X54)) = k4_xboole_0(k3_xboole_0(X52,X53),X54) ),
    inference(variable_rename,[status(thm)],[t49_xboole_1])).

fof(c_0_51,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( k4_xboole_0(k2_tarski(X1,X2),X3) = k2_tarski(X1,X2)
      <=> ( ~ r2_hidden(X1,X3)
          & ~ r2_hidden(X2,X3) ) ) ),
    inference(assume_negation,[status(cth)],[t72_zfmisc_1])).

fof(c_0_52,plain,(
    ! [X48,X49] : k4_xboole_0(X48,k3_xboole_0(X48,X49)) = k4_xboole_0(X48,X49) ),
    inference(variable_rename,[status(thm)],[t47_xboole_1])).

cnf(c_0_53,plain,
    ( ~ r2_hidden(X1,k2_xboole_0(k4_xboole_0(X2,X3),X4))
    | ~ r2_hidden(X1,k4_xboole_0(X3,X4)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_54,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,k1_tarski(X1))) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_55,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

fof(c_0_56,negated_conjecture,
    ( ( k4_xboole_0(k2_tarski(esk5_0,esk6_0),esk7_0) != k2_tarski(esk5_0,esk6_0)
      | r2_hidden(esk5_0,esk7_0)
      | r2_hidden(esk6_0,esk7_0) )
    & ( ~ r2_hidden(esk5_0,esk7_0)
      | k4_xboole_0(k2_tarski(esk5_0,esk6_0),esk7_0) = k2_tarski(esk5_0,esk6_0) )
    & ( ~ r2_hidden(esk6_0,esk7_0)
      | k4_xboole_0(k2_tarski(esk5_0,esk6_0),esk7_0) = k2_tarski(esk5_0,esk6_0) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_51])])])])])).

fof(c_0_57,plain,(
    ! [X76,X77] : k2_tarski(X76,X77) = k2_xboole_0(k1_tarski(X76),k1_tarski(X77)) ),
    inference(variable_rename,[status(thm)],[t41_enumset1])).

cnf(c_0_58,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

fof(c_0_59,plain,(
    ! [X30] :
      ( X30 = k1_xboole_0
      | r2_hidden(esk3_1(X30),X30) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

fof(c_0_60,plain,(
    ! [X9,X10] : k3_xboole_0(X9,X10) = k3_xboole_0(X10,X9) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_61,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X1))) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_62,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55,c_0_24]),c_0_24])).

cnf(c_0_63,negated_conjecture,
    ( r2_hidden(esk5_0,esk7_0)
    | r2_hidden(esk6_0,esk7_0)
    | k4_xboole_0(k2_tarski(esk5_0,esk6_0),esk7_0) != k2_tarski(esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_64,plain,
    ( k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_65,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_58,c_0_24])).

cnf(c_0_66,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk3_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_67,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_68,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X3,k1_tarski(X1))))) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_69,negated_conjecture,
    ( r2_hidden(esk5_0,esk7_0)
    | r2_hidden(esk6_0,esk7_0)
    | k4_xboole_0(k2_xboole_0(k1_tarski(esk5_0),k1_tarski(esk6_0)),esk7_0) != k2_xboole_0(k1_tarski(esk5_0),k1_tarski(esk6_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_63,c_0_64]),c_0_64])).

cnf(c_0_70,plain,
    ( k4_xboole_0(X1,X2) = X1
    | r2_hidden(esk3_1(k4_xboole_0(X1,k4_xboole_0(X1,X2))),k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_33])).

cnf(c_0_71,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X2,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_67,c_0_24]),c_0_24])).

cnf(c_0_72,plain,
    ( r2_hidden(esk3_1(k4_xboole_0(X1,k4_xboole_0(X2,k1_tarski(X3)))),k4_xboole_0(X1,k4_xboole_0(X2,k1_tarski(X3))))
    | ~ r2_hidden(X3,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_66]),c_0_33])).

cnf(c_0_73,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_74,negated_conjecture,
    ( r2_hidden(esk3_1(k4_xboole_0(esk7_0,k4_xboole_0(k4_xboole_0(esk7_0,k1_tarski(esk5_0)),k1_tarski(esk6_0)))),k4_xboole_0(esk7_0,k4_xboole_0(k4_xboole_0(esk7_0,k1_tarski(esk5_0)),k1_tarski(esk6_0))))
    | r2_hidden(esk5_0,esk7_0) ),
    inference(csr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_71]),c_0_40]),c_0_71]),c_0_40]),c_0_72])).

fof(c_0_75,plain,(
    ! [X82,X83] :
      ( ( k4_xboole_0(X82,k1_tarski(X83)) != X82
        | ~ r2_hidden(X83,X82) )
      & ( r2_hidden(X83,X82)
        | k4_xboole_0(X82,k1_tarski(X83)) = X82 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_zfmisc_1])])])).

cnf(c_0_76,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k4_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_73])).

cnf(c_0_77,negated_conjecture,
    ( r2_hidden(esk5_0,esk7_0)
    | ~ r2_hidden(esk3_1(k4_xboole_0(esk7_0,k4_xboole_0(k4_xboole_0(esk7_0,k1_tarski(esk5_0)),k1_tarski(esk6_0)))),k4_xboole_0(k4_xboole_0(esk7_0,k1_tarski(esk5_0)),k1_tarski(esk6_0))) ),
    inference(spm,[status(thm)],[c_0_39,c_0_74])).

cnf(c_0_78,plain,
    ( r2_hidden(X1,X2)
    | k4_xboole_0(X2,k1_tarski(X1)) = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_79,negated_conjecture,
    ( r2_hidden(esk3_1(k4_xboole_0(esk7_0,k4_xboole_0(k4_xboole_0(esk7_0,k1_tarski(esk5_0)),k1_tarski(esk6_0)))),esk7_0)
    | r2_hidden(esk5_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_76,c_0_74])).

cnf(c_0_80,negated_conjecture,
    ( r2_hidden(esk5_0,esk7_0)
    | ~ r2_hidden(esk3_1(k4_xboole_0(esk7_0,k4_xboole_0(esk7_0,k1_tarski(esk6_0)))),k4_xboole_0(esk7_0,k1_tarski(esk6_0))) ),
    inference(spm,[status(thm)],[c_0_77,c_0_78])).

cnf(c_0_81,plain,
    ( r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X3 != k2_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_82,negated_conjecture,
    ( r2_hidden(esk3_1(k4_xboole_0(esk7_0,k4_xboole_0(esk7_0,k1_tarski(esk6_0)))),esk7_0)
    | r2_hidden(esk5_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_79,c_0_78])).

cnf(c_0_83,negated_conjecture,
    ( r2_hidden(esk6_0,esk7_0)
    | r2_hidden(esk5_0,esk7_0)
    | ~ r2_hidden(esk3_1(k1_xboole_0),esk7_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_78]),c_0_42])).

cnf(c_0_84,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_81])).

cnf(c_0_85,negated_conjecture,
    ( r2_hidden(esk6_0,esk7_0)
    | r2_hidden(esk5_0,esk7_0) ),
    inference(csr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_78]),c_0_42]),c_0_83])).

cnf(c_0_86,negated_conjecture,
    ( k4_xboole_0(k2_tarski(esk5_0,esk6_0),esk7_0) = k2_tarski(esk5_0,esk6_0)
    | ~ r2_hidden(esk6_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_87,negated_conjecture,
    ( k4_xboole_0(k2_tarski(esk5_0,esk6_0),esk7_0) = k2_tarski(esk5_0,esk6_0)
    | ~ r2_hidden(esk5_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_88,plain,
    ( ~ r2_hidden(X1,k2_xboole_0(X2,k4_xboole_0(X3,X4)))
    | ~ r2_hidden(X1,k4_xboole_0(X4,X2)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_35])).

cnf(c_0_89,negated_conjecture,
    ( r2_hidden(esk6_0,k2_xboole_0(esk7_0,X1))
    | r2_hidden(esk5_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_84,c_0_85])).

cnf(c_0_90,negated_conjecture,
    ( k4_xboole_0(k2_xboole_0(k1_tarski(esk5_0),k1_tarski(esk6_0)),esk7_0) = k2_xboole_0(k1_tarski(esk5_0),k1_tarski(esk6_0))
    | ~ r2_hidden(esk6_0,esk7_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_86,c_0_64]),c_0_64])).

cnf(c_0_91,negated_conjecture,
    ( k4_xboole_0(k2_xboole_0(k1_tarski(esk5_0),k1_tarski(esk6_0)),esk7_0) = k2_xboole_0(k1_tarski(esk5_0),k1_tarski(esk6_0))
    | ~ r2_hidden(esk5_0,esk7_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_87,c_0_64]),c_0_64])).

cnf(c_0_92,negated_conjecture,
    ( r2_hidden(esk5_0,esk7_0)
    | ~ r2_hidden(esk6_0,k4_xboole_0(X1,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_88,c_0_89])).

cnf(c_0_93,negated_conjecture,
    ( k4_xboole_0(k2_xboole_0(k1_tarski(esk5_0),k1_tarski(esk6_0)),esk7_0) = k2_xboole_0(k1_tarski(esk5_0),k1_tarski(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_85]),c_0_91])).

cnf(c_0_94,negated_conjecture,
    ( r2_hidden(esk5_0,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_93]),c_0_54])])).

cnf(c_0_95,negated_conjecture,
    ( r2_hidden(esk5_0,k2_xboole_0(esk7_0,X1)) ),
    inference(spm,[status(thm)],[c_0_84,c_0_94])).

cnf(c_0_96,negated_conjecture,
    ( ~ r2_hidden(esk5_0,k4_xboole_0(X1,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_88,c_0_95])).

cnf(c_0_97,plain,
    ( r2_hidden(X1,k2_xboole_0(k1_tarski(X1),X2)) ),
    inference(spm,[status(thm)],[c_0_84,c_0_49])).

cnf(c_0_98,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_93]),c_0_97])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:31:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 14.32/14.50  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 14.32/14.50  # and selection function SelectNegativeLiterals.
% 14.32/14.50  #
% 14.32/14.50  # Preprocessing time       : 0.028 s
% 14.32/14.50  # Presaturation interreduction done
% 14.32/14.50  
% 14.32/14.50  # Proof found!
% 14.32/14.50  # SZS status Theorem
% 14.32/14.50  # SZS output start CNFRefutation
% 14.32/14.50  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 14.32/14.50  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 14.32/14.50  fof(t51_xboole_1, axiom, ![X1, X2]:k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_xboole_1)).
% 14.32/14.50  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 14.32/14.50  fof(t52_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(X1,k4_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_xboole_1)).
% 14.32/14.50  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 14.32/14.50  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 14.32/14.50  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 14.32/14.50  fof(t41_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 14.32/14.50  fof(d3_xboole_0, axiom, ![X1, X2, X3]:(X3=k2_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)|r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 14.32/14.50  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 14.32/14.50  fof(t49_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 14.32/14.50  fof(t72_zfmisc_1, conjecture, ![X1, X2, X3]:(k4_xboole_0(k2_tarski(X1,X2),X3)=k2_tarski(X1,X2)<=>(~(r2_hidden(X1,X3))&~(r2_hidden(X2,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_zfmisc_1)).
% 14.32/14.50  fof(t47_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 14.32/14.50  fof(t41_enumset1, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 14.32/14.50  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 14.32/14.50  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 14.32/14.50  fof(t65_zfmisc_1, axiom, ![X1, X2]:(k4_xboole_0(X1,k1_tarski(X2))=X1<=>~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 14.32/14.50  fof(c_0_18, plain, ![X35]:k3_xboole_0(X35,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 14.32/14.50  fof(c_0_19, plain, ![X50, X51]:k4_xboole_0(X50,k4_xboole_0(X50,X51))=k3_xboole_0(X50,X51), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 14.32/14.50  fof(c_0_20, plain, ![X56, X57]:k2_xboole_0(k3_xboole_0(X56,X57),k4_xboole_0(X56,X57))=X56, inference(variable_rename,[status(thm)],[t51_xboole_1])).
% 14.32/14.50  fof(c_0_21, plain, ![X20, X21, X22, X23, X24, X25, X26, X27]:((((r2_hidden(X23,X20)|~r2_hidden(X23,X22)|X22!=k4_xboole_0(X20,X21))&(~r2_hidden(X23,X21)|~r2_hidden(X23,X22)|X22!=k4_xboole_0(X20,X21)))&(~r2_hidden(X24,X20)|r2_hidden(X24,X21)|r2_hidden(X24,X22)|X22!=k4_xboole_0(X20,X21)))&((~r2_hidden(esk2_3(X25,X26,X27),X27)|(~r2_hidden(esk2_3(X25,X26,X27),X25)|r2_hidden(esk2_3(X25,X26,X27),X26))|X27=k4_xboole_0(X25,X26))&((r2_hidden(esk2_3(X25,X26,X27),X25)|r2_hidden(esk2_3(X25,X26,X27),X27)|X27=k4_xboole_0(X25,X26))&(~r2_hidden(esk2_3(X25,X26,X27),X26)|r2_hidden(esk2_3(X25,X26,X27),X27)|X27=k4_xboole_0(X25,X26))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 14.32/14.50  fof(c_0_22, plain, ![X58, X59, X60]:k4_xboole_0(X58,k4_xboole_0(X59,X60))=k2_xboole_0(k4_xboole_0(X58,X59),k3_xboole_0(X58,X60)), inference(variable_rename,[status(thm)],[t52_xboole_1])).
% 14.32/14.50  cnf(c_0_23, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_18])).
% 14.32/14.50  cnf(c_0_24, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 14.32/14.50  fof(c_0_25, plain, ![X40]:k4_xboole_0(X40,k1_xboole_0)=X40, inference(variable_rename,[status(thm)],[t3_boole])).
% 14.32/14.50  cnf(c_0_26, plain, (k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_20])).
% 14.32/14.50  fof(c_0_27, plain, ![X7, X8]:k2_xboole_0(X7,X8)=k2_xboole_0(X8,X7), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 14.32/14.50  fof(c_0_28, plain, ![X38, X39]:k2_xboole_0(X38,k4_xboole_0(X39,X38))=k2_xboole_0(X38,X39), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 14.32/14.50  cnf(c_0_29, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 14.32/14.50  fof(c_0_30, plain, ![X43, X44, X45]:k4_xboole_0(k4_xboole_0(X43,X44),X45)=k4_xboole_0(X43,k2_xboole_0(X44,X45)), inference(variable_rename,[status(thm)],[t41_xboole_1])).
% 14.32/14.50  cnf(c_0_31, plain, (k4_xboole_0(X1,k4_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 14.32/14.50  cnf(c_0_32, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))=k1_xboole_0), inference(rw,[status(thm)],[c_0_23, c_0_24])).
% 14.32/14.50  cnf(c_0_33, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_25])).
% 14.32/14.50  cnf(c_0_34, plain, (k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,X2))=X1), inference(rw,[status(thm)],[c_0_26, c_0_24])).
% 14.32/14.50  cnf(c_0_35, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 14.32/14.50  cnf(c_0_36, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 14.32/14.50  fof(c_0_37, plain, ![X11, X12, X13, X14, X15, X16, X17, X18]:(((~r2_hidden(X14,X13)|(r2_hidden(X14,X11)|r2_hidden(X14,X12))|X13!=k2_xboole_0(X11,X12))&((~r2_hidden(X15,X11)|r2_hidden(X15,X13)|X13!=k2_xboole_0(X11,X12))&(~r2_hidden(X15,X12)|r2_hidden(X15,X13)|X13!=k2_xboole_0(X11,X12))))&(((~r2_hidden(esk1_3(X16,X17,X18),X16)|~r2_hidden(esk1_3(X16,X17,X18),X18)|X18=k2_xboole_0(X16,X17))&(~r2_hidden(esk1_3(X16,X17,X18),X17)|~r2_hidden(esk1_3(X16,X17,X18),X18)|X18=k2_xboole_0(X16,X17)))&(r2_hidden(esk1_3(X16,X17,X18),X18)|(r2_hidden(esk1_3(X16,X17,X18),X16)|r2_hidden(esk1_3(X16,X17,X18),X17))|X18=k2_xboole_0(X16,X17)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).
% 14.32/14.50  fof(c_0_38, plain, ![X69, X70, X71, X72, X73, X74]:(((~r2_hidden(X71,X70)|X71=X69|X70!=k1_tarski(X69))&(X72!=X69|r2_hidden(X72,X70)|X70!=k1_tarski(X69)))&((~r2_hidden(esk4_2(X73,X74),X74)|esk4_2(X73,X74)!=X73|X74=k1_tarski(X73))&(r2_hidden(esk4_2(X73,X74),X74)|esk4_2(X73,X74)=X73|X74=k1_tarski(X73)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 14.32/14.50  cnf(c_0_39, plain, (~r2_hidden(X1,k4_xboole_0(X2,X3))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_29])).
% 14.32/14.50  cnf(c_0_40, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 14.32/14.50  cnf(c_0_41, plain, (k4_xboole_0(X1,k4_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X3)))), inference(rw,[status(thm)],[c_0_31, c_0_24])).
% 14.32/14.50  cnf(c_0_42, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[c_0_32, c_0_33])).
% 14.32/14.50  cnf(c_0_43, plain, (k2_xboole_0(X1,k4_xboole_0(X1,X2))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_35]), c_0_36]), c_0_35])).
% 14.32/14.50  cnf(c_0_44, plain, (r2_hidden(X1,X3)|~r2_hidden(X1,X2)|X3!=k2_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 14.32/14.50  cnf(c_0_45, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 14.32/14.50  cnf(c_0_46, plain, (~r2_hidden(X1,k4_xboole_0(k4_xboole_0(X2,X3),X4))|~r2_hidden(X1,k2_xboole_0(X3,X4))), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 14.32/14.50  cnf(c_0_47, plain, (k4_xboole_0(X1,k4_xboole_0(X2,X1))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_33]), c_0_35]), c_0_43])).
% 14.32/14.50  cnf(c_0_48, plain, (r2_hidden(X1,k2_xboole_0(X2,X3))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_44])).
% 14.32/14.50  cnf(c_0_49, plain, (r2_hidden(X1,k1_tarski(X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_45])])).
% 14.32/14.50  fof(c_0_50, plain, ![X52, X53, X54]:k3_xboole_0(X52,k4_xboole_0(X53,X54))=k4_xboole_0(k3_xboole_0(X52,X53),X54), inference(variable_rename,[status(thm)],[t49_xboole_1])).
% 14.32/14.50  fof(c_0_51, negated_conjecture, ~(![X1, X2, X3]:(k4_xboole_0(k2_tarski(X1,X2),X3)=k2_tarski(X1,X2)<=>(~(r2_hidden(X1,X3))&~(r2_hidden(X2,X3))))), inference(assume_negation,[status(cth)],[t72_zfmisc_1])).
% 14.32/14.50  fof(c_0_52, plain, ![X48, X49]:k4_xboole_0(X48,k3_xboole_0(X48,X49))=k4_xboole_0(X48,X49), inference(variable_rename,[status(thm)],[t47_xboole_1])).
% 14.32/14.50  cnf(c_0_53, plain, (~r2_hidden(X1,k2_xboole_0(k4_xboole_0(X2,X3),X4))|~r2_hidden(X1,k4_xboole_0(X3,X4))), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 14.32/14.50  cnf(c_0_54, plain, (r2_hidden(X1,k2_xboole_0(X2,k1_tarski(X1)))), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 14.32/14.50  cnf(c_0_55, plain, (k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 14.32/14.50  fof(c_0_56, negated_conjecture, ((k4_xboole_0(k2_tarski(esk5_0,esk6_0),esk7_0)!=k2_tarski(esk5_0,esk6_0)|(r2_hidden(esk5_0,esk7_0)|r2_hidden(esk6_0,esk7_0)))&((~r2_hidden(esk5_0,esk7_0)|k4_xboole_0(k2_tarski(esk5_0,esk6_0),esk7_0)=k2_tarski(esk5_0,esk6_0))&(~r2_hidden(esk6_0,esk7_0)|k4_xboole_0(k2_tarski(esk5_0,esk6_0),esk7_0)=k2_tarski(esk5_0,esk6_0)))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_51])])])])])).
% 14.32/14.50  fof(c_0_57, plain, ![X76, X77]:k2_tarski(X76,X77)=k2_xboole_0(k1_tarski(X76),k1_tarski(X77)), inference(variable_rename,[status(thm)],[t41_enumset1])).
% 14.32/14.50  cnf(c_0_58, plain, (k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 14.32/14.50  fof(c_0_59, plain, ![X30]:(X30=k1_xboole_0|r2_hidden(esk3_1(X30),X30)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 14.32/14.50  fof(c_0_60, plain, ![X9, X10]:k3_xboole_0(X9,X10)=k3_xboole_0(X10,X9), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 14.32/14.50  cnf(c_0_61, plain, (~r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X1)))), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 14.32/14.50  cnf(c_0_62, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3)))=k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55, c_0_24]), c_0_24])).
% 14.32/14.50  cnf(c_0_63, negated_conjecture, (r2_hidden(esk5_0,esk7_0)|r2_hidden(esk6_0,esk7_0)|k4_xboole_0(k2_tarski(esk5_0,esk6_0),esk7_0)!=k2_tarski(esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 14.32/14.50  cnf(c_0_64, plain, (k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_57])).
% 14.32/14.50  cnf(c_0_65, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2)))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_58, c_0_24])).
% 14.32/14.50  cnf(c_0_66, plain, (X1=k1_xboole_0|r2_hidden(esk3_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 14.32/14.50  cnf(c_0_67, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 14.32/14.50  cnf(c_0_68, plain, (~r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X3,k1_tarski(X1)))))), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 14.32/14.50  cnf(c_0_69, negated_conjecture, (r2_hidden(esk5_0,esk7_0)|r2_hidden(esk6_0,esk7_0)|k4_xboole_0(k2_xboole_0(k1_tarski(esk5_0),k1_tarski(esk6_0)),esk7_0)!=k2_xboole_0(k1_tarski(esk5_0),k1_tarski(esk6_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_63, c_0_64]), c_0_64])).
% 14.32/14.50  cnf(c_0_70, plain, (k4_xboole_0(X1,X2)=X1|r2_hidden(esk3_1(k4_xboole_0(X1,k4_xboole_0(X1,X2))),k4_xboole_0(X1,k4_xboole_0(X1,X2)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_33])).
% 14.32/14.50  cnf(c_0_71, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k4_xboole_0(X2,k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_67, c_0_24]), c_0_24])).
% 14.32/14.50  cnf(c_0_72, plain, (r2_hidden(esk3_1(k4_xboole_0(X1,k4_xboole_0(X2,k1_tarski(X3)))),k4_xboole_0(X1,k4_xboole_0(X2,k1_tarski(X3))))|~r2_hidden(X3,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_66]), c_0_33])).
% 14.32/14.50  cnf(c_0_73, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 14.32/14.50  cnf(c_0_74, negated_conjecture, (r2_hidden(esk3_1(k4_xboole_0(esk7_0,k4_xboole_0(k4_xboole_0(esk7_0,k1_tarski(esk5_0)),k1_tarski(esk6_0)))),k4_xboole_0(esk7_0,k4_xboole_0(k4_xboole_0(esk7_0,k1_tarski(esk5_0)),k1_tarski(esk6_0))))|r2_hidden(esk5_0,esk7_0)), inference(csr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_71]), c_0_40]), c_0_71]), c_0_40]), c_0_72])).
% 14.32/14.50  fof(c_0_75, plain, ![X82, X83]:((k4_xboole_0(X82,k1_tarski(X83))!=X82|~r2_hidden(X83,X82))&(r2_hidden(X83,X82)|k4_xboole_0(X82,k1_tarski(X83))=X82)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_zfmisc_1])])])).
% 14.32/14.50  cnf(c_0_76, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k4_xboole_0(X2,X3))), inference(er,[status(thm)],[c_0_73])).
% 14.32/14.50  cnf(c_0_77, negated_conjecture, (r2_hidden(esk5_0,esk7_0)|~r2_hidden(esk3_1(k4_xboole_0(esk7_0,k4_xboole_0(k4_xboole_0(esk7_0,k1_tarski(esk5_0)),k1_tarski(esk6_0)))),k4_xboole_0(k4_xboole_0(esk7_0,k1_tarski(esk5_0)),k1_tarski(esk6_0)))), inference(spm,[status(thm)],[c_0_39, c_0_74])).
% 14.32/14.50  cnf(c_0_78, plain, (r2_hidden(X1,X2)|k4_xboole_0(X2,k1_tarski(X1))=X2), inference(split_conjunct,[status(thm)],[c_0_75])).
% 14.32/14.50  cnf(c_0_79, negated_conjecture, (r2_hidden(esk3_1(k4_xboole_0(esk7_0,k4_xboole_0(k4_xboole_0(esk7_0,k1_tarski(esk5_0)),k1_tarski(esk6_0)))),esk7_0)|r2_hidden(esk5_0,esk7_0)), inference(spm,[status(thm)],[c_0_76, c_0_74])).
% 14.32/14.50  cnf(c_0_80, negated_conjecture, (r2_hidden(esk5_0,esk7_0)|~r2_hidden(esk3_1(k4_xboole_0(esk7_0,k4_xboole_0(esk7_0,k1_tarski(esk6_0)))),k4_xboole_0(esk7_0,k1_tarski(esk6_0)))), inference(spm,[status(thm)],[c_0_77, c_0_78])).
% 14.32/14.50  cnf(c_0_81, plain, (r2_hidden(X1,X3)|~r2_hidden(X1,X2)|X3!=k2_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 14.32/14.50  cnf(c_0_82, negated_conjecture, (r2_hidden(esk3_1(k4_xboole_0(esk7_0,k4_xboole_0(esk7_0,k1_tarski(esk6_0)))),esk7_0)|r2_hidden(esk5_0,esk7_0)), inference(spm,[status(thm)],[c_0_79, c_0_78])).
% 14.32/14.50  cnf(c_0_83, negated_conjecture, (r2_hidden(esk6_0,esk7_0)|r2_hidden(esk5_0,esk7_0)|~r2_hidden(esk3_1(k1_xboole_0),esk7_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_78]), c_0_42])).
% 14.32/14.50  cnf(c_0_84, plain, (r2_hidden(X1,k2_xboole_0(X2,X3))|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_81])).
% 14.32/14.50  cnf(c_0_85, negated_conjecture, (r2_hidden(esk6_0,esk7_0)|r2_hidden(esk5_0,esk7_0)), inference(csr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_78]), c_0_42]), c_0_83])).
% 14.32/14.50  cnf(c_0_86, negated_conjecture, (k4_xboole_0(k2_tarski(esk5_0,esk6_0),esk7_0)=k2_tarski(esk5_0,esk6_0)|~r2_hidden(esk6_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 14.32/14.50  cnf(c_0_87, negated_conjecture, (k4_xboole_0(k2_tarski(esk5_0,esk6_0),esk7_0)=k2_tarski(esk5_0,esk6_0)|~r2_hidden(esk5_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 14.32/14.50  cnf(c_0_88, plain, (~r2_hidden(X1,k2_xboole_0(X2,k4_xboole_0(X3,X4)))|~r2_hidden(X1,k4_xboole_0(X4,X2))), inference(spm,[status(thm)],[c_0_53, c_0_35])).
% 14.32/14.50  cnf(c_0_89, negated_conjecture, (r2_hidden(esk6_0,k2_xboole_0(esk7_0,X1))|r2_hidden(esk5_0,esk7_0)), inference(spm,[status(thm)],[c_0_84, c_0_85])).
% 14.32/14.50  cnf(c_0_90, negated_conjecture, (k4_xboole_0(k2_xboole_0(k1_tarski(esk5_0),k1_tarski(esk6_0)),esk7_0)=k2_xboole_0(k1_tarski(esk5_0),k1_tarski(esk6_0))|~r2_hidden(esk6_0,esk7_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_86, c_0_64]), c_0_64])).
% 14.32/14.50  cnf(c_0_91, negated_conjecture, (k4_xboole_0(k2_xboole_0(k1_tarski(esk5_0),k1_tarski(esk6_0)),esk7_0)=k2_xboole_0(k1_tarski(esk5_0),k1_tarski(esk6_0))|~r2_hidden(esk5_0,esk7_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_87, c_0_64]), c_0_64])).
% 14.32/14.50  cnf(c_0_92, negated_conjecture, (r2_hidden(esk5_0,esk7_0)|~r2_hidden(esk6_0,k4_xboole_0(X1,esk7_0))), inference(spm,[status(thm)],[c_0_88, c_0_89])).
% 14.32/14.50  cnf(c_0_93, negated_conjecture, (k4_xboole_0(k2_xboole_0(k1_tarski(esk5_0),k1_tarski(esk6_0)),esk7_0)=k2_xboole_0(k1_tarski(esk5_0),k1_tarski(esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_85]), c_0_91])).
% 14.32/14.50  cnf(c_0_94, negated_conjecture, (r2_hidden(esk5_0,esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_93]), c_0_54])])).
% 14.32/14.50  cnf(c_0_95, negated_conjecture, (r2_hidden(esk5_0,k2_xboole_0(esk7_0,X1))), inference(spm,[status(thm)],[c_0_84, c_0_94])).
% 14.32/14.50  cnf(c_0_96, negated_conjecture, (~r2_hidden(esk5_0,k4_xboole_0(X1,esk7_0))), inference(spm,[status(thm)],[c_0_88, c_0_95])).
% 14.32/14.50  cnf(c_0_97, plain, (r2_hidden(X1,k2_xboole_0(k1_tarski(X1),X2))), inference(spm,[status(thm)],[c_0_84, c_0_49])).
% 14.32/14.50  cnf(c_0_98, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_93]), c_0_97])]), ['proof']).
% 14.32/14.50  # SZS output end CNFRefutation
% 14.32/14.50  # Proof object total steps             : 99
% 14.32/14.50  # Proof object clause steps            : 62
% 14.32/14.50  # Proof object formula steps           : 37
% 14.32/14.50  # Proof object conjectures             : 23
% 14.32/14.50  # Proof object clause conjectures      : 20
% 14.32/14.50  # Proof object formula conjectures     : 3
% 14.32/14.50  # Proof object initial clauses used    : 22
% 14.32/14.50  # Proof object initial formulas used   : 18
% 14.32/14.50  # Proof object generating inferences   : 24
% 14.32/14.50  # Proof object simplifying inferences  : 42
% 14.32/14.50  # Training examples: 0 positive, 0 negative
% 14.32/14.50  # Parsed axioms                        : 31
% 14.32/14.50  # Removed by relevancy pruning/SinE    : 0
% 14.32/14.50  # Initial clauses                      : 47
% 14.32/14.50  # Removed in clause preprocessing      : 2
% 14.32/14.50  # Initial clauses in saturation        : 45
% 14.32/14.50  # Processed clauses                    : 23827
% 14.32/14.50  # ...of these trivial                  : 412
% 14.32/14.50  # ...subsumed                          : 21389
% 14.32/14.50  # ...remaining for further processing  : 2026
% 14.32/14.50  # Other redundant clauses eliminated   : 17463
% 14.32/14.50  # Clauses deleted for lack of memory   : 0
% 14.32/14.50  # Backward-subsumed                    : 229
% 14.32/14.50  # Backward-rewritten                   : 127
% 14.32/14.50  # Generated clauses                    : 1606192
% 14.32/14.50  # ...of the previous two non-trivial   : 1467347
% 14.32/14.50  # Contextual simplify-reflections      : 43
% 14.32/14.50  # Paramodulations                      : 1588432
% 14.32/14.50  # Factorizations                       : 284
% 14.32/14.50  # Equation resolutions                 : 17477
% 14.32/14.50  # Propositional unsat checks           : 0
% 14.32/14.50  #    Propositional check models        : 0
% 14.32/14.50  #    Propositional check unsatisfiable : 0
% 14.32/14.50  #    Propositional clauses             : 0
% 14.32/14.50  #    Propositional clauses after purity: 0
% 14.32/14.50  #    Propositional unsat core size     : 0
% 14.32/14.50  #    Propositional preprocessing time  : 0.000
% 14.32/14.50  #    Propositional encoding time       : 0.000
% 14.32/14.50  #    Propositional solver time         : 0.000
% 14.32/14.50  #    Success case prop preproc time    : 0.000
% 14.32/14.50  #    Success case prop encoding time   : 0.000
% 14.32/14.50  #    Success case prop solver time     : 0.000
% 14.32/14.50  # Current number of processed clauses  : 1620
% 14.32/14.50  #    Positive orientable unit clauses  : 190
% 14.32/14.50  #    Positive unorientable unit clauses: 8
% 14.32/14.50  #    Negative unit clauses             : 213
% 14.32/14.50  #    Non-unit-clauses                  : 1209
% 14.32/14.50  # Current number of unprocessed clauses: 1442168
% 14.32/14.50  # ...number of literals in the above   : 6650942
% 14.32/14.50  # Current number of archived formulas  : 0
% 14.32/14.50  # Current number of archived clauses   : 400
% 14.32/14.50  # Clause-clause subsumption calls (NU) : 470427
% 14.32/14.50  # Rec. Clause-clause subsumption calls : 282189
% 14.32/14.50  # Non-unit clause-clause subsumptions  : 9752
% 14.32/14.50  # Unit Clause-clause subsumption calls : 15395
% 14.32/14.50  # Rewrite failures with RHS unbound    : 0
% 14.32/14.50  # BW rewrite match attempts            : 2149
% 14.32/14.50  # BW rewrite match successes           : 230
% 14.32/14.50  # Condensation attempts                : 0
% 14.32/14.50  # Condensation successes               : 0
% 14.32/14.50  # Termbank termtop insertions          : 37565958
% 14.36/14.56  
% 14.36/14.56  # -------------------------------------------------
% 14.36/14.56  # User time                : 13.588 s
% 14.36/14.56  # System time              : 0.627 s
% 14.36/14.56  # Total time               : 14.215 s
% 14.36/14.56  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
