%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:35:35 EST 2020

% Result     : Theorem 0.37s
% Output     : CNFRefutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   80 (1152 expanded)
%              Number of clauses        :   47 ( 499 expanded)
%              Number of leaves         :   16 ( 326 expanded)
%              Depth                    :   12
%              Number of atoms          :  161 (1288 expanded)
%              Number of equality atoms :  117 (1216 expanded)
%              Maximal formula depth    :   22 (   3 average)
%              Maximal clause size      :   28 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t46_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(idempotence_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t91_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(d1_enumset1,axiom,(
    ! [X1,X2,X3,X4] :
      ( X4 = k1_enumset1(X1,X2,X3)
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ~ ( X5 != X1
              & X5 != X2
              & X5 != X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(t71_enumset1,conjecture,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t44_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).

fof(c_0_16,plain,(
    ! [X23,X24] : k4_xboole_0(X23,k2_xboole_0(X23,X24)) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t46_xboole_1])).

fof(c_0_17,plain,(
    ! [X30,X31] : k2_xboole_0(X30,X31) = k5_xboole_0(X30,k4_xboole_0(X31,X30)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_18,plain,(
    ! [X20,X21] : k4_xboole_0(X20,X21) = k5_xboole_0(X20,k3_xboole_0(X20,X21)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_19,plain,(
    ! [X22] : k2_xboole_0(X22,k1_xboole_0) = X22 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

fof(c_0_20,plain,(
    ! [X6,X7] : k2_xboole_0(X6,X7) = k2_xboole_0(X7,X6) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_21,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_25,plain,(
    ! [X19] : k2_xboole_0(X19,X19) = X19 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).

fof(c_0_26,plain,(
    ! [X25,X26] : k4_xboole_0(X25,k4_xboole_0(X25,X26)) = k3_xboole_0(X25,X26) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

cnf(c_0_27,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21,c_0_22]),c_0_23]),c_0_23])).

cnf(c_0_29,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_22]),c_0_23])).

cnf(c_0_30,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_31,plain,(
    ! [X43,X44,X45,X46,X47,X48] :
      ( ( ~ r2_hidden(X45,X44)
        | X45 = X43
        | X44 != k1_tarski(X43) )
      & ( X46 != X43
        | r2_hidden(X46,X44)
        | X44 != k1_tarski(X43) )
      & ( ~ r2_hidden(esk3_2(X47,X48),X48)
        | esk3_2(X47,X48) != X47
        | X48 = k1_tarski(X47) )
      & ( r2_hidden(esk3_2(X47,X48),X48)
        | esk3_2(X47,X48) = X47
        | X48 = k1_tarski(X47) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

fof(c_0_32,plain,(
    ! [X54] : k2_tarski(X54,X54) = k1_tarski(X54) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_33,plain,(
    ! [X55,X56] : k1_enumset1(X55,X55,X56) = k2_tarski(X55,X56) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

cnf(c_0_34,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_35,plain,(
    ! [X8,X9] : k3_xboole_0(X8,X9) = k3_xboole_0(X9,X8) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_36,plain,(
    ! [X27,X28,X29] : k5_xboole_0(k5_xboole_0(X27,X28),X29) = k5_xboole_0(X27,k5_xboole_0(X28,X29)) ),
    inference(variable_rename,[status(thm)],[t91_xboole_1])).

cnf(c_0_37,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) = k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_22]),c_0_22]),c_0_23]),c_0_23])).

cnf(c_0_38,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X1)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_39,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X1))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_22]),c_0_23])).

cnf(c_0_40,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_41,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_42,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

fof(c_0_43,plain,(
    ! [X10,X11,X12,X13,X14,X15,X16,X17] :
      ( ( r2_hidden(X13,X10)
        | ~ r2_hidden(X13,X12)
        | X12 != k3_xboole_0(X10,X11) )
      & ( r2_hidden(X13,X11)
        | ~ r2_hidden(X13,X12)
        | X12 != k3_xboole_0(X10,X11) )
      & ( ~ r2_hidden(X14,X10)
        | ~ r2_hidden(X14,X11)
        | r2_hidden(X14,X12)
        | X12 != k3_xboole_0(X10,X11) )
      & ( ~ r2_hidden(esk1_3(X15,X16,X17),X17)
        | ~ r2_hidden(esk1_3(X15,X16,X17),X15)
        | ~ r2_hidden(esk1_3(X15,X16,X17),X16)
        | X17 = k3_xboole_0(X15,X16) )
      & ( r2_hidden(esk1_3(X15,X16,X17),X15)
        | r2_hidden(esk1_3(X15,X16,X17),X17)
        | X17 = k3_xboole_0(X15,X16) )
      & ( r2_hidden(esk1_3(X15,X16,X17),X16)
        | r2_hidden(esk1_3(X15,X16,X17),X17)
        | X17 = k3_xboole_0(X15,X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

cnf(c_0_44,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_23]),c_0_23])).

cnf(c_0_45,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_46,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_47,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39])).

cnf(c_0_48,plain,
    ( X1 = X3
    | X2 != k1_enumset1(X3,X3,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_41]),c_0_42])).

cnf(c_0_49,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

fof(c_0_50,plain,(
    ! [X32,X33,X34,X35,X36,X37,X38,X39,X40,X41] :
      ( ( ~ r2_hidden(X36,X35)
        | X36 = X32
        | X36 = X33
        | X36 = X34
        | X35 != k1_enumset1(X32,X33,X34) )
      & ( X37 != X32
        | r2_hidden(X37,X35)
        | X35 != k1_enumset1(X32,X33,X34) )
      & ( X37 != X33
        | r2_hidden(X37,X35)
        | X35 != k1_enumset1(X32,X33,X34) )
      & ( X37 != X34
        | r2_hidden(X37,X35)
        | X35 != k1_enumset1(X32,X33,X34) )
      & ( esk2_4(X38,X39,X40,X41) != X38
        | ~ r2_hidden(esk2_4(X38,X39,X40,X41),X41)
        | X41 = k1_enumset1(X38,X39,X40) )
      & ( esk2_4(X38,X39,X40,X41) != X39
        | ~ r2_hidden(esk2_4(X38,X39,X40,X41),X41)
        | X41 = k1_enumset1(X38,X39,X40) )
      & ( esk2_4(X38,X39,X40,X41) != X40
        | ~ r2_hidden(esk2_4(X38,X39,X40,X41),X41)
        | X41 = k1_enumset1(X38,X39,X40) )
      & ( r2_hidden(esk2_4(X38,X39,X40,X41),X41)
        | esk2_4(X38,X39,X40,X41) = X38
        | esk2_4(X38,X39,X40,X41) = X39
        | esk2_4(X38,X39,X40,X41) = X40
        | X41 = k1_enumset1(X38,X39,X40) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).

cnf(c_0_51,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0)) = k3_xboole_0(X1,X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_38])).

cnf(c_0_52,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k1_xboole_0,k3_xboole_0(X1,k1_xboole_0))) = X1 ),
    inference(spm,[status(thm)],[c_0_29,c_0_45])).

cnf(c_0_53,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k1_xboole_0,X2)) = k5_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

fof(c_0_54,negated_conjecture,(
    ~ ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(assume_negation,[status(cth)],[t71_enumset1])).

fof(c_0_55,plain,(
    ! [X50,X51,X52,X53] : k2_enumset1(X50,X51,X52,X53) = k2_xboole_0(k1_tarski(X50),k1_enumset1(X51,X52,X53)) ),
    inference(variable_rename,[status(thm)],[t44_enumset1])).

cnf(c_0_56,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k1_enumset1(X2,X2,X2)) ),
    inference(er,[status(thm)],[c_0_48])).

cnf(c_0_57,plain,
    ( k3_xboole_0(X1,X2) = X2
    | r2_hidden(esk1_3(X1,X2,X2),X2) ),
    inference(ef,[status(thm)],[c_0_49])).

cnf(c_0_58,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X2,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_59,plain,
    ( k5_xboole_0(k1_xboole_0,k3_xboole_0(X1,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_51]),c_0_29])).

cnf(c_0_60,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_53]),c_0_51])).

fof(c_0_61,negated_conjecture,(
    k2_enumset1(esk4_0,esk4_0,esk5_0,esk6_0) != k1_enumset1(esk4_0,esk5_0,esk6_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_54])])])).

cnf(c_0_62,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_63,plain,
    ( X3 = k3_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X1)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_64,plain,
    ( esk1_3(X1,k1_enumset1(X2,X2,X2),k1_enumset1(X2,X2,X2)) = X2
    | k3_xboole_0(X1,k1_enumset1(X2,X2,X2)) = k1_enumset1(X2,X2,X2) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_65,plain,
    ( r2_hidden(X1,k1_enumset1(X1,X2,X3)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_58])])).

cnf(c_0_66,plain,
    ( k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(rw,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_67,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_38,c_0_60])).

cnf(c_0_68,negated_conjecture,
    ( k2_enumset1(esk4_0,esk4_0,esk5_0,esk6_0) != k1_enumset1(esk4_0,esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_69,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k5_xboole_0(k1_enumset1(X1,X1,X1),k5_xboole_0(k1_enumset1(X2,X3,X4),k3_xboole_0(k1_enumset1(X2,X3,X4),k1_enumset1(X1,X1,X1)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_62,c_0_41]),c_0_42]),c_0_22]),c_0_23])).

cnf(c_0_70,plain,
    ( k3_xboole_0(X1,k1_enumset1(X2,X2,X2)) = k1_enumset1(X2,X2,X2)
    | ~ r2_hidden(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_65])])).

cnf(c_0_71,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,X2)) = X2 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_46])).

cnf(c_0_72,plain,
    ( k1_xboole_0 = k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_46,c_0_67])).

cnf(c_0_73,negated_conjecture,
    ( k5_xboole_0(k1_enumset1(esk4_0,esk4_0,esk4_0),k5_xboole_0(k1_enumset1(esk4_0,esk5_0,esk6_0),k3_xboole_0(k1_enumset1(esk4_0,esk5_0,esk6_0),k1_enumset1(esk4_0,esk4_0,esk4_0)))) != k1_enumset1(esk4_0,esk5_0,esk6_0) ),
    inference(rw,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_74,plain,
    ( k3_xboole_0(k1_enumset1(X1,X2,X3),k1_enumset1(X1,X1,X1)) = k1_enumset1(X1,X1,X1) ),
    inference(spm,[status(thm)],[c_0_70,c_0_65])).

cnf(c_0_75,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_47])).

cnf(c_0_76,negated_conjecture,
    ( k5_xboole_0(k1_enumset1(esk4_0,esk4_0,esk4_0),k5_xboole_0(k1_enumset1(esk4_0,esk5_0,esk6_0),k3_xboole_0(k1_enumset1(esk4_0,esk4_0,esk4_0),k1_enumset1(esk4_0,esk5_0,esk6_0)))) != k1_enumset1(esk4_0,esk5_0,esk6_0) ),
    inference(rw,[status(thm)],[c_0_73,c_0_45])).

cnf(c_0_77,plain,
    ( k3_xboole_0(k1_enumset1(X1,X1,X1),k1_enumset1(X1,X2,X3)) = k1_enumset1(X1,X1,X1) ),
    inference(spm,[status(thm)],[c_0_45,c_0_74])).

cnf(c_0_78,plain,
    ( k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_71,c_0_75])).

cnf(c_0_79,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_76,c_0_77]),c_0_78]),c_0_71])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:36:55 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.37/0.54  # AutoSched0-Mode selected heuristic G_E___107_B42_F1_PI_SE_Q4_CS_SP_PS_S0YI
% 0.37/0.54  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.37/0.54  #
% 0.37/0.54  # Preprocessing time       : 0.028 s
% 0.37/0.54  # Presaturation interreduction done
% 0.37/0.54  
% 0.37/0.54  # Proof found!
% 0.37/0.54  # SZS status Theorem
% 0.37/0.54  # SZS output start CNFRefutation
% 0.37/0.54  fof(t46_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 0.37/0.54  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.37/0.54  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.37/0.54  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 0.37/0.54  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.37/0.54  fof(idempotence_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 0.37/0.54  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.37/0.54  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 0.37/0.54  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.37/0.54  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.37/0.54  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.37/0.54  fof(t91_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 0.37/0.54  fof(d4_xboole_0, axiom, ![X1, X2, X3]:(X3=k3_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 0.37/0.54  fof(d1_enumset1, axiom, ![X1, X2, X3, X4]:(X4=k1_enumset1(X1,X2,X3)<=>![X5]:(r2_hidden(X5,X4)<=>~(((X5!=X1&X5!=X2)&X5!=X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 0.37/0.54  fof(t71_enumset1, conjecture, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.37/0.54  fof(t44_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_enumset1)).
% 0.37/0.54  fof(c_0_16, plain, ![X23, X24]:k4_xboole_0(X23,k2_xboole_0(X23,X24))=k1_xboole_0, inference(variable_rename,[status(thm)],[t46_xboole_1])).
% 0.37/0.54  fof(c_0_17, plain, ![X30, X31]:k2_xboole_0(X30,X31)=k5_xboole_0(X30,k4_xboole_0(X31,X30)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.37/0.54  fof(c_0_18, plain, ![X20, X21]:k4_xboole_0(X20,X21)=k5_xboole_0(X20,k3_xboole_0(X20,X21)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.37/0.54  fof(c_0_19, plain, ![X22]:k2_xboole_0(X22,k1_xboole_0)=X22, inference(variable_rename,[status(thm)],[t1_boole])).
% 0.37/0.54  fof(c_0_20, plain, ![X6, X7]:k2_xboole_0(X6,X7)=k2_xboole_0(X7,X6), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.37/0.54  cnf(c_0_21, plain, (k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.37/0.54  cnf(c_0_22, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.37/0.54  cnf(c_0_23, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.37/0.54  cnf(c_0_24, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.37/0.54  fof(c_0_25, plain, ![X19]:k2_xboole_0(X19,X19)=X19, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).
% 0.37/0.54  fof(c_0_26, plain, ![X25, X26]:k4_xboole_0(X25,k4_xboole_0(X25,X26))=k3_xboole_0(X25,X26), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.37/0.54  cnf(c_0_27, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.37/0.54  cnf(c_0_28, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21, c_0_22]), c_0_23]), c_0_23])).
% 0.37/0.54  cnf(c_0_29, plain, (k5_xboole_0(X1,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1)))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_22]), c_0_23])).
% 0.37/0.54  cnf(c_0_30, plain, (k2_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.37/0.54  fof(c_0_31, plain, ![X43, X44, X45, X46, X47, X48]:(((~r2_hidden(X45,X44)|X45=X43|X44!=k1_tarski(X43))&(X46!=X43|r2_hidden(X46,X44)|X44!=k1_tarski(X43)))&((~r2_hidden(esk3_2(X47,X48),X48)|esk3_2(X47,X48)!=X47|X48=k1_tarski(X47))&(r2_hidden(esk3_2(X47,X48),X48)|esk3_2(X47,X48)=X47|X48=k1_tarski(X47)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.37/0.54  fof(c_0_32, plain, ![X54]:k2_tarski(X54,X54)=k1_tarski(X54), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.37/0.54  fof(c_0_33, plain, ![X55, X56]:k1_enumset1(X55,X55,X56)=k2_tarski(X55,X56), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.37/0.54  cnf(c_0_34, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.37/0.54  fof(c_0_35, plain, ![X8, X9]:k3_xboole_0(X8,X9)=k3_xboole_0(X9,X8), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.37/0.54  fof(c_0_36, plain, ![X27, X28, X29]:k5_xboole_0(k5_xboole_0(X27,X28),X29)=k5_xboole_0(X27,k5_xboole_0(X28,X29)), inference(variable_rename,[status(thm)],[t91_xboole_1])).
% 0.37/0.54  cnf(c_0_37, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))=k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27, c_0_22]), c_0_22]), c_0_23]), c_0_23])).
% 0.37/0.54  cnf(c_0_38, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X1))=k1_xboole_0), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.37/0.54  cnf(c_0_39, plain, (k5_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X1)))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_22]), c_0_23])).
% 0.37/0.54  cnf(c_0_40, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.37/0.54  cnf(c_0_41, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.37/0.54  cnf(c_0_42, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.37/0.54  fof(c_0_43, plain, ![X10, X11, X12, X13, X14, X15, X16, X17]:((((r2_hidden(X13,X10)|~r2_hidden(X13,X12)|X12!=k3_xboole_0(X10,X11))&(r2_hidden(X13,X11)|~r2_hidden(X13,X12)|X12!=k3_xboole_0(X10,X11)))&(~r2_hidden(X14,X10)|~r2_hidden(X14,X11)|r2_hidden(X14,X12)|X12!=k3_xboole_0(X10,X11)))&((~r2_hidden(esk1_3(X15,X16,X17),X17)|(~r2_hidden(esk1_3(X15,X16,X17),X15)|~r2_hidden(esk1_3(X15,X16,X17),X16))|X17=k3_xboole_0(X15,X16))&((r2_hidden(esk1_3(X15,X16,X17),X15)|r2_hidden(esk1_3(X15,X16,X17),X17)|X17=k3_xboole_0(X15,X16))&(r2_hidden(esk1_3(X15,X16,X17),X16)|r2_hidden(esk1_3(X15,X16,X17),X17)|X17=k3_xboole_0(X15,X16))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).
% 0.37/0.54  cnf(c_0_44, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_23]), c_0_23])).
% 0.37/0.54  cnf(c_0_45, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.37/0.54  cnf(c_0_46, plain, (k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.37/0.54  cnf(c_0_47, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_39])).
% 0.37/0.54  cnf(c_0_48, plain, (X1=X3|X2!=k1_enumset1(X3,X3,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_41]), c_0_42])).
% 0.37/0.54  cnf(c_0_49, plain, (r2_hidden(esk1_3(X1,X2,X3),X2)|r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.37/0.54  fof(c_0_50, plain, ![X32, X33, X34, X35, X36, X37, X38, X39, X40, X41]:(((~r2_hidden(X36,X35)|(X36=X32|X36=X33|X36=X34)|X35!=k1_enumset1(X32,X33,X34))&(((X37!=X32|r2_hidden(X37,X35)|X35!=k1_enumset1(X32,X33,X34))&(X37!=X33|r2_hidden(X37,X35)|X35!=k1_enumset1(X32,X33,X34)))&(X37!=X34|r2_hidden(X37,X35)|X35!=k1_enumset1(X32,X33,X34))))&((((esk2_4(X38,X39,X40,X41)!=X38|~r2_hidden(esk2_4(X38,X39,X40,X41),X41)|X41=k1_enumset1(X38,X39,X40))&(esk2_4(X38,X39,X40,X41)!=X39|~r2_hidden(esk2_4(X38,X39,X40,X41),X41)|X41=k1_enumset1(X38,X39,X40)))&(esk2_4(X38,X39,X40,X41)!=X40|~r2_hidden(esk2_4(X38,X39,X40,X41),X41)|X41=k1_enumset1(X38,X39,X40)))&(r2_hidden(esk2_4(X38,X39,X40,X41),X41)|(esk2_4(X38,X39,X40,X41)=X38|esk2_4(X38,X39,X40,X41)=X39|esk2_4(X38,X39,X40,X41)=X40)|X41=k1_enumset1(X38,X39,X40)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).
% 0.37/0.54  cnf(c_0_51, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0))=k3_xboole_0(X1,X1)), inference(spm,[status(thm)],[c_0_44, c_0_38])).
% 0.37/0.54  cnf(c_0_52, plain, (k5_xboole_0(X1,k5_xboole_0(k1_xboole_0,k3_xboole_0(X1,k1_xboole_0)))=X1), inference(spm,[status(thm)],[c_0_29, c_0_45])).
% 0.37/0.54  cnf(c_0_53, plain, (k5_xboole_0(X1,k5_xboole_0(k1_xboole_0,X2))=k5_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.37/0.54  fof(c_0_54, negated_conjecture, ~(![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(assume_negation,[status(cth)],[t71_enumset1])).
% 0.37/0.54  fof(c_0_55, plain, ![X50, X51, X52, X53]:k2_enumset1(X50,X51,X52,X53)=k2_xboole_0(k1_tarski(X50),k1_enumset1(X51,X52,X53)), inference(variable_rename,[status(thm)],[t44_enumset1])).
% 0.37/0.54  cnf(c_0_56, plain, (X1=X2|~r2_hidden(X1,k1_enumset1(X2,X2,X2))), inference(er,[status(thm)],[c_0_48])).
% 0.37/0.54  cnf(c_0_57, plain, (k3_xboole_0(X1,X2)=X2|r2_hidden(esk1_3(X1,X2,X2),X2)), inference(ef,[status(thm)],[c_0_49])).
% 0.37/0.54  cnf(c_0_58, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X2,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.37/0.54  cnf(c_0_59, plain, (k5_xboole_0(k1_xboole_0,k3_xboole_0(X1,X1))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_51]), c_0_29])).
% 0.37/0.54  cnf(c_0_60, plain, (k3_xboole_0(X1,X1)=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52, c_0_53]), c_0_51])).
% 0.37/0.54  fof(c_0_61, negated_conjecture, k2_enumset1(esk4_0,esk4_0,esk5_0,esk6_0)!=k1_enumset1(esk4_0,esk5_0,esk6_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_54])])])).
% 0.37/0.54  cnf(c_0_62, plain, (k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.37/0.54  cnf(c_0_63, plain, (X3=k3_xboole_0(X1,X2)|~r2_hidden(esk1_3(X1,X2,X3),X3)|~r2_hidden(esk1_3(X1,X2,X3),X1)|~r2_hidden(esk1_3(X1,X2,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.37/0.54  cnf(c_0_64, plain, (esk1_3(X1,k1_enumset1(X2,X2,X2),k1_enumset1(X2,X2,X2))=X2|k3_xboole_0(X1,k1_enumset1(X2,X2,X2))=k1_enumset1(X2,X2,X2)), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.37/0.54  cnf(c_0_65, plain, (r2_hidden(X1,k1_enumset1(X1,X2,X3))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_58])])).
% 0.37/0.54  cnf(c_0_66, plain, (k5_xboole_0(k1_xboole_0,X1)=X1), inference(rw,[status(thm)],[c_0_59, c_0_60])).
% 0.37/0.54  cnf(c_0_67, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[c_0_38, c_0_60])).
% 0.37/0.54  cnf(c_0_68, negated_conjecture, (k2_enumset1(esk4_0,esk4_0,esk5_0,esk6_0)!=k1_enumset1(esk4_0,esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.37/0.54  cnf(c_0_69, plain, (k2_enumset1(X1,X2,X3,X4)=k5_xboole_0(k1_enumset1(X1,X1,X1),k5_xboole_0(k1_enumset1(X2,X3,X4),k3_xboole_0(k1_enumset1(X2,X3,X4),k1_enumset1(X1,X1,X1))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_62, c_0_41]), c_0_42]), c_0_22]), c_0_23])).
% 0.37/0.54  cnf(c_0_70, plain, (k3_xboole_0(X1,k1_enumset1(X2,X2,X2))=k1_enumset1(X2,X2,X2)|~r2_hidden(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_65])])).
% 0.37/0.54  cnf(c_0_71, plain, (k5_xboole_0(X1,k5_xboole_0(X1,X2))=X2), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_46])).
% 0.37/0.54  cnf(c_0_72, plain, (k1_xboole_0=k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,X2)))), inference(spm,[status(thm)],[c_0_46, c_0_67])).
% 0.37/0.54  cnf(c_0_73, negated_conjecture, (k5_xboole_0(k1_enumset1(esk4_0,esk4_0,esk4_0),k5_xboole_0(k1_enumset1(esk4_0,esk5_0,esk6_0),k3_xboole_0(k1_enumset1(esk4_0,esk5_0,esk6_0),k1_enumset1(esk4_0,esk4_0,esk4_0))))!=k1_enumset1(esk4_0,esk5_0,esk6_0)), inference(rw,[status(thm)],[c_0_68, c_0_69])).
% 0.37/0.54  cnf(c_0_74, plain, (k3_xboole_0(k1_enumset1(X1,X2,X3),k1_enumset1(X1,X1,X1))=k1_enumset1(X1,X1,X1)), inference(spm,[status(thm)],[c_0_70, c_0_65])).
% 0.37/0.54  cnf(c_0_75, plain, (k5_xboole_0(X1,k5_xboole_0(X2,X1))=X2), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_47])).
% 0.37/0.54  cnf(c_0_76, negated_conjecture, (k5_xboole_0(k1_enumset1(esk4_0,esk4_0,esk4_0),k5_xboole_0(k1_enumset1(esk4_0,esk5_0,esk6_0),k3_xboole_0(k1_enumset1(esk4_0,esk4_0,esk4_0),k1_enumset1(esk4_0,esk5_0,esk6_0))))!=k1_enumset1(esk4_0,esk5_0,esk6_0)), inference(rw,[status(thm)],[c_0_73, c_0_45])).
% 0.37/0.54  cnf(c_0_77, plain, (k3_xboole_0(k1_enumset1(X1,X1,X1),k1_enumset1(X1,X2,X3))=k1_enumset1(X1,X1,X1)), inference(spm,[status(thm)],[c_0_45, c_0_74])).
% 0.37/0.54  cnf(c_0_78, plain, (k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_71, c_0_75])).
% 0.37/0.54  cnf(c_0_79, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_76, c_0_77]), c_0_78]), c_0_71])]), ['proof']).
% 0.37/0.54  # SZS output end CNFRefutation
% 0.37/0.54  # Proof object total steps             : 80
% 0.37/0.54  # Proof object clause steps            : 47
% 0.37/0.54  # Proof object formula steps           : 33
% 0.37/0.54  # Proof object conjectures             : 7
% 0.37/0.54  # Proof object clause conjectures      : 4
% 0.37/0.54  # Proof object formula conjectures     : 3
% 0.37/0.54  # Proof object initial clauses used    : 17
% 0.37/0.54  # Proof object initial formulas used   : 16
% 0.37/0.54  # Proof object generating inferences   : 15
% 0.37/0.54  # Proof object simplifying inferences  : 38
% 0.37/0.54  # Training examples: 0 positive, 0 negative
% 0.37/0.54  # Parsed axioms                        : 16
% 0.37/0.54  # Removed by relevancy pruning/SinE    : 0
% 0.37/0.54  # Initial clauses                      : 31
% 0.37/0.54  # Removed in clause preprocessing      : 5
% 0.37/0.54  # Initial clauses in saturation        : 26
% 0.37/0.54  # Processed clauses                    : 2296
% 0.37/0.54  # ...of these trivial                  : 674
% 0.37/0.54  # ...subsumed                          : 1346
% 0.37/0.54  # ...remaining for further processing  : 276
% 0.37/0.54  # Other redundant clauses eliminated   : 199
% 0.37/0.54  # Clauses deleted for lack of memory   : 0
% 0.37/0.54  # Backward-subsumed                    : 4
% 0.37/0.54  # Backward-rewritten                   : 41
% 0.37/0.54  # Generated clauses                    : 17634
% 0.37/0.54  # ...of the previous two non-trivial   : 12662
% 0.37/0.54  # Contextual simplify-reflections      : 1
% 0.37/0.54  # Paramodulations                      : 17277
% 0.37/0.54  # Factorizations                       : 162
% 0.37/0.54  # Equation resolutions                 : 199
% 0.37/0.54  # Propositional unsat checks           : 0
% 0.37/0.54  #    Propositional check models        : 0
% 0.37/0.54  #    Propositional check unsatisfiable : 0
% 0.37/0.54  #    Propositional clauses             : 0
% 0.37/0.54  #    Propositional clauses after purity: 0
% 0.37/0.54  #    Propositional unsat core size     : 0
% 0.37/0.54  #    Propositional preprocessing time  : 0.000
% 0.37/0.54  #    Propositional encoding time       : 0.000
% 0.37/0.54  #    Propositional solver time         : 0.000
% 0.37/0.54  #    Success case prop preproc time    : 0.000
% 0.37/0.54  #    Success case prop encoding time   : 0.000
% 0.37/0.54  #    Success case prop solver time     : 0.000
% 0.37/0.54  # Current number of processed clauses  : 197
% 0.37/0.54  #    Positive orientable unit clauses  : 82
% 0.37/0.54  #    Positive unorientable unit clauses: 11
% 0.37/0.54  #    Negative unit clauses             : 0
% 0.37/0.54  #    Non-unit-clauses                  : 104
% 0.37/0.54  # Current number of unprocessed clauses: 9623
% 0.37/0.54  # ...number of literals in the above   : 21258
% 0.37/0.54  # Current number of archived formulas  : 0
% 0.37/0.54  # Current number of archived clauses   : 75
% 0.37/0.54  # Clause-clause subsumption calls (NU) : 3065
% 0.37/0.54  # Rec. Clause-clause subsumption calls : 2121
% 0.37/0.54  # Non-unit clause-clause subsumptions  : 433
% 0.37/0.54  # Unit Clause-clause subsumption calls : 664
% 0.37/0.54  # Rewrite failures with RHS unbound    : 114
% 0.37/0.54  # BW rewrite match attempts            : 1361
% 0.37/0.54  # BW rewrite match successes           : 309
% 0.37/0.54  # Condensation attempts                : 0
% 0.37/0.54  # Condensation successes               : 0
% 0.37/0.54  # Termbank termtop insertions          : 247938
% 0.37/0.54  
% 0.37/0.54  # -------------------------------------------------
% 0.37/0.54  # User time                : 0.192 s
% 0.37/0.54  # System time              : 0.010 s
% 0.37/0.54  # Total time               : 0.202 s
% 0.37/0.54  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
