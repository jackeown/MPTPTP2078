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
% DateTime   : Thu Dec  3 10:35:32 EST 2020

% Result     : Theorem 13.23s
% Output     : CNFRefutation 13.23s
% Verified   : 
% Statistics : Number of formulae       :   92 (3133 expanded)
%              Number of clauses        :   59 (1501 expanded)
%              Number of leaves         :   16 ( 815 expanded)
%              Depth                    :   19
%              Number of atoms          :  166 (3583 expanded)
%              Number of equality atoms :   86 (3127 expanded)
%              Maximal formula depth    :   17 (   3 average)
%              Maximal clause size      :   20 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t46_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(idempotence_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(t91_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t41_enumset1,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,conjecture,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t42_enumset1,axiom,(
    ! [X1,X2,X3] : k1_enumset1(X1,X2,X3) = k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(c_0_16,plain,(
    ! [X43,X44] : k2_xboole_0(X43,X44) = k5_xboole_0(X43,k4_xboole_0(X44,X43)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_17,plain,(
    ! [X32,X33] : k4_xboole_0(X32,X33) = k5_xboole_0(X32,k3_xboole_0(X32,X33)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_18,plain,(
    ! [X38,X39] : k4_xboole_0(X38,k2_xboole_0(X38,X39)) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t46_xboole_1])).

cnf(c_0_19,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_21,plain,(
    ! [X36] : k2_xboole_0(X36,k1_xboole_0) = X36 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

fof(c_0_22,plain,(
    ! [X31] : k2_xboole_0(X31,X31) = X31 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).

cnf(c_0_23,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(rw,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_25,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_26,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_27,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_20]),c_0_24])).

cnf(c_0_28,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1))) = X1 ),
    inference(rw,[status(thm)],[c_0_25,c_0_24])).

fof(c_0_29,plain,(
    ! [X40,X41,X42] : k5_xboole_0(k5_xboole_0(X40,X41),X42) = k5_xboole_0(X40,k5_xboole_0(X41,X42)) ),
    inference(variable_rename,[status(thm)],[t91_xboole_1])).

cnf(c_0_30,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X1))) = X1 ),
    inference(rw,[status(thm)],[c_0_26,c_0_24])).

cnf(c_0_31,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X1)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

fof(c_0_32,plain,(
    ! [X37] : k4_xboole_0(X37,k1_xboole_0) = X37 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

cnf(c_0_33,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_34,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_35,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_36,plain,(
    ! [X22,X23,X24,X25,X26,X27,X28,X29] :
      ( ( r2_hidden(X25,X22)
        | ~ r2_hidden(X25,X24)
        | X24 != k4_xboole_0(X22,X23) )
      & ( ~ r2_hidden(X25,X23)
        | ~ r2_hidden(X25,X24)
        | X24 != k4_xboole_0(X22,X23) )
      & ( ~ r2_hidden(X26,X22)
        | r2_hidden(X26,X23)
        | r2_hidden(X26,X24)
        | X24 != k4_xboole_0(X22,X23) )
      & ( ~ r2_hidden(esk3_3(X27,X28,X29),X29)
        | ~ r2_hidden(esk3_3(X27,X28,X29),X27)
        | r2_hidden(esk3_3(X27,X28,X29),X28)
        | X29 = k4_xboole_0(X27,X28) )
      & ( r2_hidden(esk3_3(X27,X28,X29),X27)
        | r2_hidden(esk3_3(X27,X28,X29),X29)
        | X29 = k4_xboole_0(X27,X28) )
      & ( ~ r2_hidden(esk3_3(X27,X28,X29),X28)
        | r2_hidden(esk3_3(X27,X28,X29),X29)
        | X29 = k4_xboole_0(X27,X28) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

fof(c_0_37,plain,(
    ! [X34,X35] :
      ( ~ r1_tarski(X34,X35)
      | k2_xboole_0(X34,X35) = X35 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_38,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k1_xboole_0,X2)) = k5_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_39,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0)) = X1 ),
    inference(rw,[status(thm)],[c_0_35,c_0_20])).

cnf(c_0_40,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k3_xboole_0(X1,X1),X2)) = k5_xboole_0(k1_xboole_0,X2) ),
    inference(spm,[status(thm)],[c_0_33,c_0_31])).

cnf(c_0_41,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

fof(c_0_42,plain,(
    ! [X5,X6] : k3_xboole_0(X5,X6) = k3_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_43,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

fof(c_0_44,plain,(
    ! [X7,X8,X9,X10,X11] :
      ( ( ~ r1_tarski(X7,X8)
        | ~ r2_hidden(X9,X7)
        | r2_hidden(X9,X8) )
      & ( r2_hidden(esk1_2(X10,X11),X10)
        | r1_tarski(X10,X11) )
      & ( ~ r2_hidden(esk1_2(X10,X11),X11)
        | r1_tarski(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_45,plain,
    ( k5_xboole_0(X1,k3_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X2))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_27]),c_0_34]),c_0_39])).

cnf(c_0_46,plain,
    ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(X1,X1),k3_xboole_0(X1,X1))) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_31]),c_0_34])).

cnf(c_0_47,plain,
    ( X3 != k5_xboole_0(X4,k3_xboole_0(X4,X2))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_41,c_0_20])).

cnf(c_0_48,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_49,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_43,c_0_24])).

cnf(c_0_50,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_51,plain,
    ( k5_xboole_0(X1,k3_xboole_0(k1_xboole_0,X2)) = X1 ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_52,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_47])).

cnf(c_0_53,plain,
    ( k5_xboole_0(X1,k3_xboole_0(k1_xboole_0,X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_39,c_0_48])).

cnf(c_0_54,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) = X2
    | r2_hidden(esk1_2(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_55,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X2,k1_xboole_0)) = X1 ),
    inference(spm,[status(thm)],[c_0_51,c_0_48])).

cnf(c_0_56,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

fof(c_0_57,plain,(
    ! [X45,X46] : k2_tarski(X45,X46) = k2_xboole_0(k1_tarski(X45),k1_tarski(X46)) ),
    inference(variable_rename,[status(thm)],[t41_enumset1])).

fof(c_0_58,plain,(
    ! [X50] : k2_tarski(X50,X50) = k1_tarski(X50) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_59,negated_conjecture,(
    ~ ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(assume_negation,[status(cth)],[t70_enumset1])).

fof(c_0_60,plain,(
    ! [X47,X48,X49] : k1_enumset1(X47,X48,X49) = k2_xboole_0(k1_tarski(X47),k2_tarski(X48,X49)) ),
    inference(variable_rename,[status(thm)],[t42_enumset1])).

cnf(c_0_61,plain,
    ( k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_56])).

cnf(c_0_62,plain,
    ( k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_63,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

fof(c_0_64,negated_conjecture,(
    k1_enumset1(esk4_0,esk4_0,esk5_0) != k2_tarski(esk4_0,esk5_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_59])])])).

cnf(c_0_65,plain,
    ( k1_enumset1(X1,X2,X3) = k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

fof(c_0_66,plain,(
    ! [X13,X14,X15,X16,X17,X18,X19,X20] :
      ( ( r2_hidden(X16,X13)
        | ~ r2_hidden(X16,X15)
        | X15 != k3_xboole_0(X13,X14) )
      & ( r2_hidden(X16,X14)
        | ~ r2_hidden(X16,X15)
        | X15 != k3_xboole_0(X13,X14) )
      & ( ~ r2_hidden(X17,X13)
        | ~ r2_hidden(X17,X14)
        | r2_hidden(X17,X15)
        | X15 != k3_xboole_0(X13,X14) )
      & ( ~ r2_hidden(esk2_3(X18,X19,X20),X20)
        | ~ r2_hidden(esk2_3(X18,X19,X20),X18)
        | ~ r2_hidden(esk2_3(X18,X19,X20),X19)
        | X20 = k3_xboole_0(X18,X19) )
      & ( r2_hidden(esk2_3(X18,X19,X20),X18)
        | r2_hidden(esk2_3(X18,X19,X20),X20)
        | X20 = k3_xboole_0(X18,X19) )
      & ( r2_hidden(esk2_3(X18,X19,X20),X19)
        | r2_hidden(esk2_3(X18,X19,X20),X20)
        | X20 = k3_xboole_0(X18,X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

cnf(c_0_67,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k3_xboole_0(X1,X1),X2)) = X2 ),
    inference(rw,[status(thm)],[c_0_40,c_0_61])).

cnf(c_0_68,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X1),k3_xboole_0(X1,X1)) = X1 ),
    inference(rw,[status(thm)],[c_0_46,c_0_61])).

cnf(c_0_69,plain,
    ( k2_tarski(X1,X2) = k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X2,X2),k3_xboole_0(k2_tarski(X2,X2),k2_tarski(X1,X1)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_62,c_0_63]),c_0_63]),c_0_24])).

cnf(c_0_70,negated_conjecture,
    ( k1_enumset1(esk4_0,esk4_0,esk5_0) != k2_tarski(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_71,plain,
    ( k1_enumset1(X1,X2,X3) = k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X2,X3),k3_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_65,c_0_63]),c_0_24])).

cnf(c_0_72,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_73,plain,
    ( k5_xboole_0(k3_xboole_0(X1,X1),k5_xboole_0(X1,X2)) = X2 ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_74,plain,
    ( k5_xboole_0(k2_tarski(X1,X1),k3_xboole_0(k2_tarski(X1,X1),k2_tarski(X1,X2))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_27,c_0_69])).

cnf(c_0_75,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_76,negated_conjecture,
    ( k5_xboole_0(k2_tarski(esk4_0,esk4_0),k5_xboole_0(k2_tarski(esk4_0,esk5_0),k3_xboole_0(k2_tarski(esk4_0,esk5_0),k2_tarski(esk4_0,esk4_0)))) != k2_tarski(esk4_0,esk5_0) ),
    inference(rw,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_77,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X3,X2)) ),
    inference(er,[status(thm)],[c_0_72])).

cnf(c_0_78,plain,
    ( k3_xboole_0(k2_tarski(X1,X1),k2_tarski(X1,X1)) = k3_xboole_0(k2_tarski(X1,X1),k2_tarski(X1,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_34])).

cnf(c_0_79,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_75])).

cnf(c_0_80,negated_conjecture,
    ( k5_xboole_0(k2_tarski(esk4_0,esk4_0),k5_xboole_0(k2_tarski(esk4_0,esk5_0),k3_xboole_0(k2_tarski(esk4_0,esk4_0),k2_tarski(esk4_0,esk5_0)))) != k2_tarski(esk4_0,esk5_0) ),
    inference(rw,[status(thm)],[c_0_76,c_0_48])).

cnf(c_0_81,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2))) = X2
    | r2_hidden(esk1_2(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_54,c_0_48])).

cnf(c_0_82,plain,
    ( r2_hidden(X1,k2_tarski(X2,X3))
    | ~ r2_hidden(X1,k3_xboole_0(k2_tarski(X2,X2),k2_tarski(X2,X2))) ),
    inference(spm,[status(thm)],[c_0_77,c_0_78])).

cnf(c_0_83,plain,
    ( r2_hidden(X1,k3_xboole_0(X2,X2))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_79,c_0_68])).

cnf(c_0_84,negated_conjecture,
    ( r2_hidden(esk1_2(k2_tarski(esk4_0,esk4_0),k2_tarski(esk4_0,esk5_0)),k2_tarski(esk4_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_80,c_0_81])).

cnf(c_0_85,plain,
    ( r2_hidden(X1,k2_tarski(X2,X3))
    | ~ r2_hidden(X1,k3_xboole_0(k2_tarski(X2,X2),k2_tarski(X2,X4))) ),
    inference(spm,[status(thm)],[c_0_82,c_0_78])).

cnf(c_0_86,negated_conjecture,
    ( r2_hidden(esk1_2(k2_tarski(esk4_0,esk4_0),k2_tarski(esk4_0,esk5_0)),k3_xboole_0(k2_tarski(esk4_0,esk4_0),k2_tarski(esk4_0,esk4_0))) ),
    inference(spm,[status(thm)],[c_0_83,c_0_84])).

cnf(c_0_87,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_88,negated_conjecture,
    ( r2_hidden(esk1_2(k2_tarski(esk4_0,esk4_0),k2_tarski(esk4_0,esk5_0)),k2_tarski(esk4_0,X1)) ),
    inference(spm,[status(thm)],[c_0_85,c_0_86])).

cnf(c_0_89,negated_conjecture,
    ( r1_tarski(k2_tarski(esk4_0,esk4_0),k2_tarski(esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_87,c_0_88])).

cnf(c_0_90,negated_conjecture,
    ( k5_xboole_0(k2_tarski(esk4_0,esk4_0),k5_xboole_0(k2_tarski(esk4_0,esk5_0),k3_xboole_0(k2_tarski(esk4_0,esk4_0),k2_tarski(esk4_0,esk4_0)))) != k2_tarski(esk4_0,esk5_0) ),
    inference(rw,[status(thm)],[c_0_80,c_0_78])).

cnf(c_0_91,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_89]),c_0_48]),c_0_78]),c_0_90]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n008.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 19:52:15 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 13.23/13.44  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 13.23/13.44  # and selection function SelectNegativeLiterals.
% 13.23/13.44  #
% 13.23/13.44  # Preprocessing time       : 0.027 s
% 13.23/13.44  # Presaturation interreduction done
% 13.23/13.44  
% 13.23/13.44  # Proof found!
% 13.23/13.44  # SZS status Theorem
% 13.23/13.44  # SZS output start CNFRefutation
% 13.23/13.44  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 13.23/13.44  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 13.23/13.44  fof(t46_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 13.23/13.44  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 13.23/13.44  fof(idempotence_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 13.23/13.44  fof(t91_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 13.23/13.44  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 13.23/13.44  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 13.23/13.44  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 13.23/13.44  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 13.23/13.44  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 13.23/13.44  fof(t41_enumset1, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 13.23/13.44  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 13.23/13.44  fof(t70_enumset1, conjecture, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 13.23/13.44  fof(t42_enumset1, axiom, ![X1, X2, X3]:k1_enumset1(X1,X2,X3)=k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_enumset1)).
% 13.23/13.44  fof(d4_xboole_0, axiom, ![X1, X2, X3]:(X3=k3_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 13.23/13.44  fof(c_0_16, plain, ![X43, X44]:k2_xboole_0(X43,X44)=k5_xboole_0(X43,k4_xboole_0(X44,X43)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 13.23/13.44  fof(c_0_17, plain, ![X32, X33]:k4_xboole_0(X32,X33)=k5_xboole_0(X32,k3_xboole_0(X32,X33)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 13.23/13.44  fof(c_0_18, plain, ![X38, X39]:k4_xboole_0(X38,k2_xboole_0(X38,X39))=k1_xboole_0, inference(variable_rename,[status(thm)],[t46_xboole_1])).
% 13.23/13.44  cnf(c_0_19, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 13.23/13.44  cnf(c_0_20, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 13.23/13.44  fof(c_0_21, plain, ![X36]:k2_xboole_0(X36,k1_xboole_0)=X36, inference(variable_rename,[status(thm)],[t1_boole])).
% 13.23/13.44  fof(c_0_22, plain, ![X31]:k2_xboole_0(X31,X31)=X31, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).
% 13.23/13.44  cnf(c_0_23, plain, (k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_18])).
% 13.23/13.44  cnf(c_0_24, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))), inference(rw,[status(thm)],[c_0_19, c_0_20])).
% 13.23/13.44  cnf(c_0_25, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_21])).
% 13.23/13.44  cnf(c_0_26, plain, (k2_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_22])).
% 13.23/13.44  cnf(c_0_27, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23, c_0_20]), c_0_24])).
% 13.23/13.44  cnf(c_0_28, plain, (k5_xboole_0(X1,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1)))=X1), inference(rw,[status(thm)],[c_0_25, c_0_24])).
% 13.23/13.44  fof(c_0_29, plain, ![X40, X41, X42]:k5_xboole_0(k5_xboole_0(X40,X41),X42)=k5_xboole_0(X40,k5_xboole_0(X41,X42)), inference(variable_rename,[status(thm)],[t91_xboole_1])).
% 13.23/13.44  cnf(c_0_30, plain, (k5_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X1)))=X1), inference(rw,[status(thm)],[c_0_26, c_0_24])).
% 13.23/13.44  cnf(c_0_31, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X1))=k1_xboole_0), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 13.23/13.44  fof(c_0_32, plain, ![X37]:k4_xboole_0(X37,k1_xboole_0)=X37, inference(variable_rename,[status(thm)],[t3_boole])).
% 13.23/13.44  cnf(c_0_33, plain, (k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 13.23/13.44  cnf(c_0_34, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[c_0_30, c_0_31])).
% 13.23/13.44  cnf(c_0_35, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_32])).
% 13.23/13.44  fof(c_0_36, plain, ![X22, X23, X24, X25, X26, X27, X28, X29]:((((r2_hidden(X25,X22)|~r2_hidden(X25,X24)|X24!=k4_xboole_0(X22,X23))&(~r2_hidden(X25,X23)|~r2_hidden(X25,X24)|X24!=k4_xboole_0(X22,X23)))&(~r2_hidden(X26,X22)|r2_hidden(X26,X23)|r2_hidden(X26,X24)|X24!=k4_xboole_0(X22,X23)))&((~r2_hidden(esk3_3(X27,X28,X29),X29)|(~r2_hidden(esk3_3(X27,X28,X29),X27)|r2_hidden(esk3_3(X27,X28,X29),X28))|X29=k4_xboole_0(X27,X28))&((r2_hidden(esk3_3(X27,X28,X29),X27)|r2_hidden(esk3_3(X27,X28,X29),X29)|X29=k4_xboole_0(X27,X28))&(~r2_hidden(esk3_3(X27,X28,X29),X28)|r2_hidden(esk3_3(X27,X28,X29),X29)|X29=k4_xboole_0(X27,X28))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 13.23/13.44  fof(c_0_37, plain, ![X34, X35]:(~r1_tarski(X34,X35)|k2_xboole_0(X34,X35)=X35), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 13.23/13.44  cnf(c_0_38, plain, (k5_xboole_0(X1,k5_xboole_0(k1_xboole_0,X2))=k5_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 13.23/13.44  cnf(c_0_39, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0))=X1), inference(rw,[status(thm)],[c_0_35, c_0_20])).
% 13.23/13.44  cnf(c_0_40, plain, (k5_xboole_0(X1,k5_xboole_0(k3_xboole_0(X1,X1),X2))=k5_xboole_0(k1_xboole_0,X2)), inference(spm,[status(thm)],[c_0_33, c_0_31])).
% 13.23/13.44  cnf(c_0_41, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 13.23/13.44  fof(c_0_42, plain, ![X5, X6]:k3_xboole_0(X5,X6)=k3_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 13.23/13.44  cnf(c_0_43, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 13.23/13.44  fof(c_0_44, plain, ![X7, X8, X9, X10, X11]:((~r1_tarski(X7,X8)|(~r2_hidden(X9,X7)|r2_hidden(X9,X8)))&((r2_hidden(esk1_2(X10,X11),X10)|r1_tarski(X10,X11))&(~r2_hidden(esk1_2(X10,X11),X11)|r1_tarski(X10,X11)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 13.23/13.44  cnf(c_0_45, plain, (k5_xboole_0(X1,k3_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X2)))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_27]), c_0_34]), c_0_39])).
% 13.23/13.44  cnf(c_0_46, plain, (k5_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(X1,X1),k3_xboole_0(X1,X1)))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_31]), c_0_34])).
% 13.23/13.44  cnf(c_0_47, plain, (X3!=k5_xboole_0(X4,k3_xboole_0(X4,X2))|~r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_41, c_0_20])).
% 13.23/13.44  cnf(c_0_48, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 13.23/13.44  cnf(c_0_49, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))=X2|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_43, c_0_24])).
% 13.23/13.44  cnf(c_0_50, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 13.23/13.44  cnf(c_0_51, plain, (k5_xboole_0(X1,k3_xboole_0(k1_xboole_0,X2))=X1), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 13.23/13.44  cnf(c_0_52, plain, (~r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_47])).
% 13.23/13.44  cnf(c_0_53, plain, (k5_xboole_0(X1,k3_xboole_0(k1_xboole_0,X1))=X1), inference(spm,[status(thm)],[c_0_39, c_0_48])).
% 13.23/13.44  cnf(c_0_54, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))=X2|r2_hidden(esk1_2(X1,X2),X1)), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 13.23/13.44  cnf(c_0_55, plain, (k5_xboole_0(X1,k3_xboole_0(X2,k1_xboole_0))=X1), inference(spm,[status(thm)],[c_0_51, c_0_48])).
% 13.23/13.44  cnf(c_0_56, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 13.23/13.44  fof(c_0_57, plain, ![X45, X46]:k2_tarski(X45,X46)=k2_xboole_0(k1_tarski(X45),k1_tarski(X46)), inference(variable_rename,[status(thm)],[t41_enumset1])).
% 13.23/13.44  fof(c_0_58, plain, ![X50]:k2_tarski(X50,X50)=k1_tarski(X50), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 13.23/13.44  fof(c_0_59, negated_conjecture, ~(![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(assume_negation,[status(cth)],[t70_enumset1])).
% 13.23/13.44  fof(c_0_60, plain, ![X47, X48, X49]:k1_enumset1(X47,X48,X49)=k2_xboole_0(k1_tarski(X47),k2_tarski(X48,X49)), inference(variable_rename,[status(thm)],[t42_enumset1])).
% 13.23/13.44  cnf(c_0_61, plain, (k5_xboole_0(k1_xboole_0,X1)=X1), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_56])).
% 13.23/13.44  cnf(c_0_62, plain, (k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_57])).
% 13.23/13.44  cnf(c_0_63, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 13.23/13.44  fof(c_0_64, negated_conjecture, k1_enumset1(esk4_0,esk4_0,esk5_0)!=k2_tarski(esk4_0,esk5_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_59])])])).
% 13.23/13.44  cnf(c_0_65, plain, (k1_enumset1(X1,X2,X3)=k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_60])).
% 13.23/13.44  fof(c_0_66, plain, ![X13, X14, X15, X16, X17, X18, X19, X20]:((((r2_hidden(X16,X13)|~r2_hidden(X16,X15)|X15!=k3_xboole_0(X13,X14))&(r2_hidden(X16,X14)|~r2_hidden(X16,X15)|X15!=k3_xboole_0(X13,X14)))&(~r2_hidden(X17,X13)|~r2_hidden(X17,X14)|r2_hidden(X17,X15)|X15!=k3_xboole_0(X13,X14)))&((~r2_hidden(esk2_3(X18,X19,X20),X20)|(~r2_hidden(esk2_3(X18,X19,X20),X18)|~r2_hidden(esk2_3(X18,X19,X20),X19))|X20=k3_xboole_0(X18,X19))&((r2_hidden(esk2_3(X18,X19,X20),X18)|r2_hidden(esk2_3(X18,X19,X20),X20)|X20=k3_xboole_0(X18,X19))&(r2_hidden(esk2_3(X18,X19,X20),X19)|r2_hidden(esk2_3(X18,X19,X20),X20)|X20=k3_xboole_0(X18,X19))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).
% 13.23/13.44  cnf(c_0_67, plain, (k5_xboole_0(X1,k5_xboole_0(k3_xboole_0(X1,X1),X2))=X2), inference(rw,[status(thm)],[c_0_40, c_0_61])).
% 13.23/13.44  cnf(c_0_68, plain, (k3_xboole_0(k3_xboole_0(X1,X1),k3_xboole_0(X1,X1))=X1), inference(rw,[status(thm)],[c_0_46, c_0_61])).
% 13.23/13.44  cnf(c_0_69, plain, (k2_tarski(X1,X2)=k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X2,X2),k3_xboole_0(k2_tarski(X2,X2),k2_tarski(X1,X1))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_62, c_0_63]), c_0_63]), c_0_24])).
% 13.23/13.44  cnf(c_0_70, negated_conjecture, (k1_enumset1(esk4_0,esk4_0,esk5_0)!=k2_tarski(esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_64])).
% 13.23/13.44  cnf(c_0_71, plain, (k1_enumset1(X1,X2,X3)=k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X2,X3),k3_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_65, c_0_63]), c_0_24])).
% 13.23/13.44  cnf(c_0_72, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_66])).
% 13.23/13.44  cnf(c_0_73, plain, (k5_xboole_0(k3_xboole_0(X1,X1),k5_xboole_0(X1,X2))=X2), inference(spm,[status(thm)],[c_0_67, c_0_68])).
% 13.23/13.44  cnf(c_0_74, plain, (k5_xboole_0(k2_tarski(X1,X1),k3_xboole_0(k2_tarski(X1,X1),k2_tarski(X1,X2)))=k1_xboole_0), inference(spm,[status(thm)],[c_0_27, c_0_69])).
% 13.23/13.44  cnf(c_0_75, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_66])).
% 13.23/13.44  cnf(c_0_76, negated_conjecture, (k5_xboole_0(k2_tarski(esk4_0,esk4_0),k5_xboole_0(k2_tarski(esk4_0,esk5_0),k3_xboole_0(k2_tarski(esk4_0,esk5_0),k2_tarski(esk4_0,esk4_0))))!=k2_tarski(esk4_0,esk5_0)), inference(rw,[status(thm)],[c_0_70, c_0_71])).
% 13.23/13.44  cnf(c_0_77, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k3_xboole_0(X3,X2))), inference(er,[status(thm)],[c_0_72])).
% 13.23/13.44  cnf(c_0_78, plain, (k3_xboole_0(k2_tarski(X1,X1),k2_tarski(X1,X1))=k3_xboole_0(k2_tarski(X1,X1),k2_tarski(X1,X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_34])).
% 13.23/13.44  cnf(c_0_79, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k3_xboole_0(X2,X3))), inference(er,[status(thm)],[c_0_75])).
% 13.23/13.44  cnf(c_0_80, negated_conjecture, (k5_xboole_0(k2_tarski(esk4_0,esk4_0),k5_xboole_0(k2_tarski(esk4_0,esk5_0),k3_xboole_0(k2_tarski(esk4_0,esk4_0),k2_tarski(esk4_0,esk5_0))))!=k2_tarski(esk4_0,esk5_0)), inference(rw,[status(thm)],[c_0_76, c_0_48])).
% 13.23/13.44  cnf(c_0_81, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2)))=X2|r2_hidden(esk1_2(X1,X2),X1)), inference(spm,[status(thm)],[c_0_54, c_0_48])).
% 13.23/13.44  cnf(c_0_82, plain, (r2_hidden(X1,k2_tarski(X2,X3))|~r2_hidden(X1,k3_xboole_0(k2_tarski(X2,X2),k2_tarski(X2,X2)))), inference(spm,[status(thm)],[c_0_77, c_0_78])).
% 13.23/13.44  cnf(c_0_83, plain, (r2_hidden(X1,k3_xboole_0(X2,X2))|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_79, c_0_68])).
% 13.23/13.44  cnf(c_0_84, negated_conjecture, (r2_hidden(esk1_2(k2_tarski(esk4_0,esk4_0),k2_tarski(esk4_0,esk5_0)),k2_tarski(esk4_0,esk4_0))), inference(spm,[status(thm)],[c_0_80, c_0_81])).
% 13.23/13.44  cnf(c_0_85, plain, (r2_hidden(X1,k2_tarski(X2,X3))|~r2_hidden(X1,k3_xboole_0(k2_tarski(X2,X2),k2_tarski(X2,X4)))), inference(spm,[status(thm)],[c_0_82, c_0_78])).
% 13.23/13.44  cnf(c_0_86, negated_conjecture, (r2_hidden(esk1_2(k2_tarski(esk4_0,esk4_0),k2_tarski(esk4_0,esk5_0)),k3_xboole_0(k2_tarski(esk4_0,esk4_0),k2_tarski(esk4_0,esk4_0)))), inference(spm,[status(thm)],[c_0_83, c_0_84])).
% 13.23/13.44  cnf(c_0_87, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 13.23/13.44  cnf(c_0_88, negated_conjecture, (r2_hidden(esk1_2(k2_tarski(esk4_0,esk4_0),k2_tarski(esk4_0,esk5_0)),k2_tarski(esk4_0,X1))), inference(spm,[status(thm)],[c_0_85, c_0_86])).
% 13.23/13.44  cnf(c_0_89, negated_conjecture, (r1_tarski(k2_tarski(esk4_0,esk4_0),k2_tarski(esk4_0,esk5_0))), inference(spm,[status(thm)],[c_0_87, c_0_88])).
% 13.23/13.44  cnf(c_0_90, negated_conjecture, (k5_xboole_0(k2_tarski(esk4_0,esk4_0),k5_xboole_0(k2_tarski(esk4_0,esk5_0),k3_xboole_0(k2_tarski(esk4_0,esk4_0),k2_tarski(esk4_0,esk4_0))))!=k2_tarski(esk4_0,esk5_0)), inference(rw,[status(thm)],[c_0_80, c_0_78])).
% 13.23/13.44  cnf(c_0_91, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_89]), c_0_48]), c_0_78]), c_0_90]), ['proof']).
% 13.23/13.44  # SZS output end CNFRefutation
% 13.23/13.44  # Proof object total steps             : 92
% 13.23/13.44  # Proof object clause steps            : 59
% 13.23/13.44  # Proof object formula steps           : 33
% 13.23/13.44  # Proof object conjectures             : 12
% 13.23/13.44  # Proof object clause conjectures      : 9
% 13.23/13.44  # Proof object formula conjectures     : 3
% 13.23/13.44  # Proof object initial clauses used    : 18
% 13.23/13.44  # Proof object initial formulas used   : 16
% 13.23/13.44  # Proof object generating inferences   : 23
% 13.23/13.44  # Proof object simplifying inferences  : 30
% 13.23/13.44  # Training examples: 0 positive, 0 negative
% 13.23/13.44  # Parsed axioms                        : 16
% 13.23/13.44  # Removed by relevancy pruning/SinE    : 0
% 13.23/13.44  # Initial clauses                      : 28
% 13.23/13.44  # Removed in clause preprocessing      : 4
% 13.23/13.44  # Initial clauses in saturation        : 24
% 13.23/13.44  # Processed clauses                    : 11359
% 13.23/13.44  # ...of these trivial                  : 1960
% 13.23/13.44  # ...subsumed                          : 7988
% 13.23/13.44  # ...remaining for further processing  : 1411
% 13.23/13.44  # Other redundant clauses eliminated   : 7696
% 13.23/13.44  # Clauses deleted for lack of memory   : 0
% 13.23/13.44  # Backward-subsumed                    : 50
% 13.23/13.44  # Backward-rewritten                   : 159
% 13.23/13.44  # Generated clauses                    : 1071498
% 13.23/13.44  # ...of the previous two non-trivial   : 978164
% 13.23/13.44  # Contextual simplify-reflections      : 28
% 13.23/13.44  # Paramodulations                      : 1063796
% 13.23/13.44  # Factorizations                       : 6
% 13.23/13.44  # Equation resolutions                 : 7696
% 13.23/13.44  # Propositional unsat checks           : 0
% 13.23/13.44  #    Propositional check models        : 0
% 13.23/13.44  #    Propositional check unsatisfiable : 0
% 13.23/13.44  #    Propositional clauses             : 0
% 13.23/13.44  #    Propositional clauses after purity: 0
% 13.23/13.44  #    Propositional unsat core size     : 0
% 13.23/13.44  #    Propositional preprocessing time  : 0.000
% 13.23/13.44  #    Propositional encoding time       : 0.000
% 13.23/13.44  #    Propositional solver time         : 0.000
% 13.23/13.44  #    Success case prop preproc time    : 0.000
% 13.23/13.44  #    Success case prop encoding time   : 0.000
% 13.23/13.44  #    Success case prop solver time     : 0.000
% 13.23/13.44  # Current number of processed clauses  : 1172
% 13.23/13.44  #    Positive orientable unit clauses  : 255
% 13.23/13.44  #    Positive unorientable unit clauses: 5
% 13.23/13.44  #    Negative unit clauses             : 5
% 13.23/13.44  #    Non-unit-clauses                  : 907
% 13.23/13.44  # Current number of unprocessed clauses: 964345
% 13.23/13.44  # ...number of literals in the above   : 3788941
% 13.23/13.44  # Current number of archived formulas  : 0
% 13.23/13.44  # Current number of archived clauses   : 237
% 13.23/13.44  # Clause-clause subsumption calls (NU) : 139214
% 13.23/13.44  # Rec. Clause-clause subsumption calls : 97839
% 13.23/13.44  # Non-unit clause-clause subsumptions  : 6907
% 13.23/13.44  # Unit Clause-clause subsumption calls : 8363
% 13.23/13.44  # Rewrite failures with RHS unbound    : 19
% 13.23/13.44  # BW rewrite match attempts            : 2133
% 13.23/13.44  # BW rewrite match successes           : 111
% 13.23/13.44  # Condensation attempts                : 0
% 13.23/13.44  # Condensation successes               : 0
% 13.23/13.44  # Termbank termtop insertions          : 31362962
% 13.31/13.50  
% 13.31/13.50  # -------------------------------------------------
% 13.31/13.50  # User time                : 12.595 s
% 13.31/13.50  # System time              : 0.537 s
% 13.31/13.50  # Total time               : 13.132 s
% 13.31/13.50  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
