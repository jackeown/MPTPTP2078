%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:35:36 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   82 (4895 expanded)
%              Number of clauses        :   51 (2282 expanded)
%              Number of leaves         :   15 (1306 expanded)
%              Depth                    :   13
%              Number of atoms          :  163 (5031 expanded)
%              Number of equality atoms :  119 (4959 expanded)
%              Maximal formula depth    :   22 (   3 average)
%              Maximal clause size      :   28 (   1 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t4_boole,axiom,(
    ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(t91_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(d1_enumset1,axiom,(
    ! [X1,X2,X3,X4] :
      ( X4 = k1_enumset1(X1,X2,X3)
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ~ ( X5 != X1
              & X5 != X2
              & X5 != X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(t71_enumset1,conjecture,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t44_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).

fof(c_0_15,plain,(
    ! [X24] : k4_xboole_0(k1_xboole_0,X24) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t4_boole])).

fof(c_0_16,plain,(
    ! [X17,X18] : k4_xboole_0(X17,X18) = k5_xboole_0(X17,k3_xboole_0(X17,X18)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_17,plain,(
    ! [X22,X23] : k4_xboole_0(X22,k4_xboole_0(X22,X23)) = k3_xboole_0(X22,X23) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_18,plain,(
    ! [X28,X29] : k2_xboole_0(X28,X29) = k5_xboole_0(X28,k4_xboole_0(X29,X28)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

cnf(c_0_19,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_22,plain,(
    ! [X19] : k2_xboole_0(X19,k1_xboole_0) = X19 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

cnf(c_0_23,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_24,plain,(
    ! [X6,X7] : k3_xboole_0(X6,X7) = k3_xboole_0(X7,X6) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_25,plain,
    ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_26,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21,c_0_20]),c_0_20])).

cnf(c_0_27,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(rw,[status(thm)],[c_0_23,c_0_20])).

cnf(c_0_29,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_30,plain,
    ( k3_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_31,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1))) = X1 ),
    inference(rw,[status(thm)],[c_0_27,c_0_28])).

fof(c_0_32,plain,(
    ! [X41,X42,X43,X44,X45,X46] :
      ( ( ~ r2_hidden(X43,X42)
        | X43 = X41
        | X42 != k1_tarski(X41) )
      & ( X44 != X41
        | r2_hidden(X44,X42)
        | X42 != k1_tarski(X41) )
      & ( ~ r2_hidden(esk3_2(X45,X46),X46)
        | esk3_2(X45,X46) != X45
        | X46 = k1_tarski(X45) )
      & ( r2_hidden(esk3_2(X45,X46),X46)
        | esk3_2(X45,X46) = X45
        | X46 = k1_tarski(X45) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

fof(c_0_33,plain,(
    ! [X52] : k2_tarski(X52,X52) = k1_tarski(X52) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_34,plain,(
    ! [X53,X54] : k1_enumset1(X53,X53,X54) = k2_tarski(X53,X54) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

cnf(c_0_35,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_36,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[c_0_31,c_0_25])).

cnf(c_0_37,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_38,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_39,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

fof(c_0_40,plain,(
    ! [X8,X9,X10,X11,X12,X13,X14,X15] :
      ( ( r2_hidden(X11,X8)
        | ~ r2_hidden(X11,X10)
        | X10 != k3_xboole_0(X8,X9) )
      & ( r2_hidden(X11,X9)
        | ~ r2_hidden(X11,X10)
        | X10 != k3_xboole_0(X8,X9) )
      & ( ~ r2_hidden(X12,X8)
        | ~ r2_hidden(X12,X9)
        | r2_hidden(X12,X10)
        | X10 != k3_xboole_0(X8,X9) )
      & ( ~ r2_hidden(esk1_3(X13,X14,X15),X15)
        | ~ r2_hidden(esk1_3(X13,X14,X15),X13)
        | ~ r2_hidden(esk1_3(X13,X14,X15),X14)
        | X15 = k3_xboole_0(X13,X14) )
      & ( r2_hidden(esk1_3(X13,X14,X15),X13)
        | r2_hidden(esk1_3(X13,X14,X15),X15)
        | X15 = k3_xboole_0(X13,X14) )
      & ( r2_hidden(esk1_3(X13,X14,X15),X14)
        | r2_hidden(esk1_3(X13,X14,X15),X15)
        | X15 = k3_xboole_0(X13,X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

fof(c_0_41,plain,(
    ! [X20,X21] : k2_xboole_0(X20,k4_xboole_0(X21,X20)) = k2_xboole_0(X20,X21) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

cnf(c_0_42,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X1)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_35]),c_0_36])).

fof(c_0_43,plain,(
    ! [X25,X26,X27] : k5_xboole_0(k5_xboole_0(X25,X26),X27) = k5_xboole_0(X25,k5_xboole_0(X26,X27)) ),
    inference(variable_rename,[status(thm)],[t91_xboole_1])).

cnf(c_0_44,plain,
    ( X1 = X3
    | X2 != k1_enumset1(X3,X3,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_38]),c_0_39])).

cnf(c_0_45,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

fof(c_0_46,plain,(
    ! [X30,X31,X32,X33,X34,X35,X36,X37,X38,X39] :
      ( ( ~ r2_hidden(X34,X33)
        | X34 = X30
        | X34 = X31
        | X34 = X32
        | X33 != k1_enumset1(X30,X31,X32) )
      & ( X35 != X30
        | r2_hidden(X35,X33)
        | X33 != k1_enumset1(X30,X31,X32) )
      & ( X35 != X31
        | r2_hidden(X35,X33)
        | X33 != k1_enumset1(X30,X31,X32) )
      & ( X35 != X32
        | r2_hidden(X35,X33)
        | X33 != k1_enumset1(X30,X31,X32) )
      & ( esk2_4(X36,X37,X38,X39) != X36
        | ~ r2_hidden(esk2_4(X36,X37,X38,X39),X39)
        | X39 = k1_enumset1(X36,X37,X38) )
      & ( esk2_4(X36,X37,X38,X39) != X37
        | ~ r2_hidden(esk2_4(X36,X37,X38,X39),X39)
        | X39 = k1_enumset1(X36,X37,X38) )
      & ( esk2_4(X36,X37,X38,X39) != X38
        | ~ r2_hidden(esk2_4(X36,X37,X38,X39),X39)
        | X39 = k1_enumset1(X36,X37,X38) )
      & ( r2_hidden(esk2_4(X36,X37,X38,X39),X39)
        | esk2_4(X36,X37,X38,X39) = X36
        | esk2_4(X36,X37,X38,X39) = X37
        | esk2_4(X36,X37,X38,X39) = X38
        | X39 = k1_enumset1(X36,X37,X38) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).

cnf(c_0_47,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_48,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_42]),c_0_35]),c_0_36])).

cnf(c_0_49,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

fof(c_0_50,negated_conjecture,(
    ~ ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(assume_negation,[status(cth)],[t71_enumset1])).

fof(c_0_51,plain,(
    ! [X48,X49,X50,X51] : k2_enumset1(X48,X49,X50,X51) = k2_xboole_0(k1_tarski(X48),k1_enumset1(X49,X50,X51)) ),
    inference(variable_rename,[status(thm)],[t44_enumset1])).

cnf(c_0_52,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k1_enumset1(X2,X2,X2)) ),
    inference(er,[status(thm)],[c_0_44])).

cnf(c_0_53,plain,
    ( k3_xboole_0(X1,X2) = X2
    | r2_hidden(esk1_3(X1,X2,X2),X2) ),
    inference(ef,[status(thm)],[c_0_45])).

cnf(c_0_54,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X2,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_55,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X2,k3_xboole_0(X2,X1)),k3_xboole_0(k5_xboole_0(X2,k3_xboole_0(X2,X1)),X1))) = k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_20]),c_0_28]),c_0_28])).

cnf(c_0_56,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_42,c_0_48])).

cnf(c_0_57,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k1_xboole_0,X2)) = k5_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_49,c_0_36])).

fof(c_0_58,negated_conjecture,(
    k2_enumset1(esk4_0,esk4_0,esk5_0,esk6_0) != k1_enumset1(esk4_0,esk5_0,esk6_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_50])])])).

cnf(c_0_59,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_60,plain,
    ( X3 = k3_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X1)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_61,plain,
    ( esk1_3(X1,k1_enumset1(X2,X2,X2),k1_enumset1(X2,X2,X2)) = X2
    | k3_xboole_0(X1,k1_enumset1(X2,X2,X2)) = k1_enumset1(X2,X2,X2) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_62,plain,
    ( r2_hidden(X1,k1_enumset1(X1,X2,X3)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_54])])).

cnf(c_0_63,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k3_xboole_0(X2,X1),k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))))) = k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55,c_0_29]),c_0_49])).

cnf(c_0_64,plain,
    ( k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X2,k5_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_56])).

cnf(c_0_65,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X2,X2)) = k5_xboole_0(X2,X2) ),
    inference(spm,[status(thm)],[c_0_35,c_0_56])).

cnf(c_0_66,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,X2)) = X1 ),
    inference(spm,[status(thm)],[c_0_36,c_0_56])).

cnf(c_0_67,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X2,X3))) = k5_xboole_0(X1,X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_56]),c_0_49])).

cnf(c_0_68,plain,
    ( k1_xboole_0 = k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_49,c_0_56])).

cnf(c_0_69,negated_conjecture,
    ( k2_enumset1(esk4_0,esk4_0,esk5_0,esk6_0) != k1_enumset1(esk4_0,esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_70,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k5_xboole_0(k1_enumset1(X1,X1,X1),k5_xboole_0(k1_enumset1(X2,X3,X4),k3_xboole_0(k1_enumset1(X2,X3,X4),k1_enumset1(X1,X1,X1)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59,c_0_38]),c_0_39]),c_0_28])).

cnf(c_0_71,plain,
    ( k3_xboole_0(X1,k1_enumset1(X2,X2,X2)) = k1_enumset1(X2,X2,X2)
    | ~ r2_hidden(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_62])])).

cnf(c_0_72,plain,
    ( k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_48]),c_0_48]),c_0_65]),c_0_66]),c_0_48]),c_0_66])).

cnf(c_0_73,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,X2))) = k5_xboole_0(X1,X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_36])).

cnf(c_0_74,negated_conjecture,
    ( k5_xboole_0(k1_enumset1(esk4_0,esk4_0,esk4_0),k5_xboole_0(k1_enumset1(esk4_0,esk5_0,esk6_0),k3_xboole_0(k1_enumset1(esk4_0,esk5_0,esk6_0),k1_enumset1(esk4_0,esk4_0,esk4_0)))) != k1_enumset1(esk4_0,esk5_0,esk6_0) ),
    inference(rw,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_75,plain,
    ( k3_xboole_0(k1_enumset1(X1,X2,X3),k1_enumset1(X1,X1,X1)) = k1_enumset1(X1,X1,X1) ),
    inference(spm,[status(thm)],[c_0_71,c_0_62])).

cnf(c_0_76,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,X2)) = X2 ),
    inference(rw,[status(thm)],[c_0_64,c_0_72])).

cnf(c_0_77,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_72]),c_0_72])).

cnf(c_0_78,negated_conjecture,
    ( k5_xboole_0(k1_enumset1(esk4_0,esk4_0,esk4_0),k5_xboole_0(k1_enumset1(esk4_0,esk5_0,esk6_0),k3_xboole_0(k1_enumset1(esk4_0,esk4_0,esk4_0),k1_enumset1(esk4_0,esk5_0,esk6_0)))) != k1_enumset1(esk4_0,esk5_0,esk6_0) ),
    inference(rw,[status(thm)],[c_0_74,c_0_29])).

cnf(c_0_79,plain,
    ( k3_xboole_0(k1_enumset1(X1,X1,X1),k1_enumset1(X1,X2,X3)) = k1_enumset1(X1,X1,X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_75])).

cnf(c_0_80,plain,
    ( k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_76,c_0_77])).

cnf(c_0_81,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_78,c_0_79]),c_0_80]),c_0_76])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:57:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.49  # AutoSched0-Mode selected heuristic G_E___107_B42_F1_PI_SE_Q4_CS_SP_PS_S0YI
% 0.20/0.49  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.20/0.49  #
% 0.20/0.49  # Preprocessing time       : 0.028 s
% 0.20/0.49  # Presaturation interreduction done
% 0.20/0.49  
% 0.20/0.49  # Proof found!
% 0.20/0.49  # SZS status Theorem
% 0.20/0.49  # SZS output start CNFRefutation
% 0.20/0.49  fof(t4_boole, axiom, ![X1]:k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 0.20/0.49  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.20/0.49  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.20/0.49  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.20/0.49  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 0.20/0.49  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.20/0.49  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 0.20/0.49  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.20/0.49  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.20/0.49  fof(d4_xboole_0, axiom, ![X1, X2, X3]:(X3=k3_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 0.20/0.49  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 0.20/0.49  fof(t91_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 0.20/0.49  fof(d1_enumset1, axiom, ![X1, X2, X3, X4]:(X4=k1_enumset1(X1,X2,X3)<=>![X5]:(r2_hidden(X5,X4)<=>~(((X5!=X1&X5!=X2)&X5!=X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 0.20/0.49  fof(t71_enumset1, conjecture, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.20/0.49  fof(t44_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_enumset1)).
% 0.20/0.49  fof(c_0_15, plain, ![X24]:k4_xboole_0(k1_xboole_0,X24)=k1_xboole_0, inference(variable_rename,[status(thm)],[t4_boole])).
% 0.20/0.49  fof(c_0_16, plain, ![X17, X18]:k4_xboole_0(X17,X18)=k5_xboole_0(X17,k3_xboole_0(X17,X18)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.20/0.49  fof(c_0_17, plain, ![X22, X23]:k4_xboole_0(X22,k4_xboole_0(X22,X23))=k3_xboole_0(X22,X23), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.20/0.49  fof(c_0_18, plain, ![X28, X29]:k2_xboole_0(X28,X29)=k5_xboole_0(X28,k4_xboole_0(X29,X28)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.20/0.49  cnf(c_0_19, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.49  cnf(c_0_20, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.49  cnf(c_0_21, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.49  fof(c_0_22, plain, ![X19]:k2_xboole_0(X19,k1_xboole_0)=X19, inference(variable_rename,[status(thm)],[t1_boole])).
% 0.20/0.49  cnf(c_0_23, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.49  fof(c_0_24, plain, ![X6, X7]:k3_xboole_0(X6,X7)=k3_xboole_0(X7,X6), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.20/0.49  cnf(c_0_25, plain, (k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1))=k1_xboole_0), inference(rw,[status(thm)],[c_0_19, c_0_20])).
% 0.20/0.49  cnf(c_0_26, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21, c_0_20]), c_0_20])).
% 0.20/0.49  cnf(c_0_27, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.49  cnf(c_0_28, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))), inference(rw,[status(thm)],[c_0_23, c_0_20])).
% 0.20/0.49  cnf(c_0_29, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.49  cnf(c_0_30, plain, (k3_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.20/0.49  cnf(c_0_31, plain, (k5_xboole_0(X1,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1)))=X1), inference(rw,[status(thm)],[c_0_27, c_0_28])).
% 0.20/0.49  fof(c_0_32, plain, ![X41, X42, X43, X44, X45, X46]:(((~r2_hidden(X43,X42)|X43=X41|X42!=k1_tarski(X41))&(X44!=X41|r2_hidden(X44,X42)|X42!=k1_tarski(X41)))&((~r2_hidden(esk3_2(X45,X46),X46)|esk3_2(X45,X46)!=X45|X46=k1_tarski(X45))&(r2_hidden(esk3_2(X45,X46),X46)|esk3_2(X45,X46)=X45|X46=k1_tarski(X45)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.20/0.49  fof(c_0_33, plain, ![X52]:k2_tarski(X52,X52)=k1_tarski(X52), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.20/0.49  fof(c_0_34, plain, ![X53, X54]:k1_enumset1(X53,X53,X54)=k2_tarski(X53,X54), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.20/0.49  cnf(c_0_35, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.20/0.49  cnf(c_0_36, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[c_0_31, c_0_25])).
% 0.20/0.49  cnf(c_0_37, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.49  cnf(c_0_38, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.20/0.49  cnf(c_0_39, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.20/0.49  fof(c_0_40, plain, ![X8, X9, X10, X11, X12, X13, X14, X15]:((((r2_hidden(X11,X8)|~r2_hidden(X11,X10)|X10!=k3_xboole_0(X8,X9))&(r2_hidden(X11,X9)|~r2_hidden(X11,X10)|X10!=k3_xboole_0(X8,X9)))&(~r2_hidden(X12,X8)|~r2_hidden(X12,X9)|r2_hidden(X12,X10)|X10!=k3_xboole_0(X8,X9)))&((~r2_hidden(esk1_3(X13,X14,X15),X15)|(~r2_hidden(esk1_3(X13,X14,X15),X13)|~r2_hidden(esk1_3(X13,X14,X15),X14))|X15=k3_xboole_0(X13,X14))&((r2_hidden(esk1_3(X13,X14,X15),X13)|r2_hidden(esk1_3(X13,X14,X15),X15)|X15=k3_xboole_0(X13,X14))&(r2_hidden(esk1_3(X13,X14,X15),X14)|r2_hidden(esk1_3(X13,X14,X15),X15)|X15=k3_xboole_0(X13,X14))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).
% 0.20/0.49  fof(c_0_41, plain, ![X20, X21]:k2_xboole_0(X20,k4_xboole_0(X21,X20))=k2_xboole_0(X20,X21), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 0.20/0.49  cnf(c_0_42, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X1))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_35]), c_0_36])).
% 0.20/0.49  fof(c_0_43, plain, ![X25, X26, X27]:k5_xboole_0(k5_xboole_0(X25,X26),X27)=k5_xboole_0(X25,k5_xboole_0(X26,X27)), inference(variable_rename,[status(thm)],[t91_xboole_1])).
% 0.20/0.49  cnf(c_0_44, plain, (X1=X3|X2!=k1_enumset1(X3,X3,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37, c_0_38]), c_0_39])).
% 0.20/0.49  cnf(c_0_45, plain, (r2_hidden(esk1_3(X1,X2,X3),X2)|r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.20/0.49  fof(c_0_46, plain, ![X30, X31, X32, X33, X34, X35, X36, X37, X38, X39]:(((~r2_hidden(X34,X33)|(X34=X30|X34=X31|X34=X32)|X33!=k1_enumset1(X30,X31,X32))&(((X35!=X30|r2_hidden(X35,X33)|X33!=k1_enumset1(X30,X31,X32))&(X35!=X31|r2_hidden(X35,X33)|X33!=k1_enumset1(X30,X31,X32)))&(X35!=X32|r2_hidden(X35,X33)|X33!=k1_enumset1(X30,X31,X32))))&((((esk2_4(X36,X37,X38,X39)!=X36|~r2_hidden(esk2_4(X36,X37,X38,X39),X39)|X39=k1_enumset1(X36,X37,X38))&(esk2_4(X36,X37,X38,X39)!=X37|~r2_hidden(esk2_4(X36,X37,X38,X39),X39)|X39=k1_enumset1(X36,X37,X38)))&(esk2_4(X36,X37,X38,X39)!=X38|~r2_hidden(esk2_4(X36,X37,X38,X39),X39)|X39=k1_enumset1(X36,X37,X38)))&(r2_hidden(esk2_4(X36,X37,X38,X39),X39)|(esk2_4(X36,X37,X38,X39)=X36|esk2_4(X36,X37,X38,X39)=X37|esk2_4(X36,X37,X38,X39)=X38)|X39=k1_enumset1(X36,X37,X38)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).
% 0.20/0.49  cnf(c_0_47, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.20/0.49  cnf(c_0_48, plain, (k3_xboole_0(X1,X1)=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_42]), c_0_35]), c_0_36])).
% 0.20/0.49  cnf(c_0_49, plain, (k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.20/0.49  fof(c_0_50, negated_conjecture, ~(![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(assume_negation,[status(cth)],[t71_enumset1])).
% 0.20/0.49  fof(c_0_51, plain, ![X48, X49, X50, X51]:k2_enumset1(X48,X49,X50,X51)=k2_xboole_0(k1_tarski(X48),k1_enumset1(X49,X50,X51)), inference(variable_rename,[status(thm)],[t44_enumset1])).
% 0.20/0.49  cnf(c_0_52, plain, (X1=X2|~r2_hidden(X1,k1_enumset1(X2,X2,X2))), inference(er,[status(thm)],[c_0_44])).
% 0.20/0.49  cnf(c_0_53, plain, (k3_xboole_0(X1,X2)=X2|r2_hidden(esk1_3(X1,X2,X2),X2)), inference(ef,[status(thm)],[c_0_45])).
% 0.20/0.49  cnf(c_0_54, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X2,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.20/0.49  cnf(c_0_55, plain, (k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X2,k3_xboole_0(X2,X1)),k3_xboole_0(k5_xboole_0(X2,k3_xboole_0(X2,X1)),X1)))=k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47, c_0_20]), c_0_28]), c_0_28])).
% 0.20/0.49  cnf(c_0_56, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[c_0_42, c_0_48])).
% 0.20/0.49  cnf(c_0_57, plain, (k5_xboole_0(X1,k5_xboole_0(k1_xboole_0,X2))=k5_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_49, c_0_36])).
% 0.20/0.49  fof(c_0_58, negated_conjecture, k2_enumset1(esk4_0,esk4_0,esk5_0,esk6_0)!=k1_enumset1(esk4_0,esk5_0,esk6_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_50])])])).
% 0.20/0.49  cnf(c_0_59, plain, (k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.20/0.49  cnf(c_0_60, plain, (X3=k3_xboole_0(X1,X2)|~r2_hidden(esk1_3(X1,X2,X3),X3)|~r2_hidden(esk1_3(X1,X2,X3),X1)|~r2_hidden(esk1_3(X1,X2,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.20/0.49  cnf(c_0_61, plain, (esk1_3(X1,k1_enumset1(X2,X2,X2),k1_enumset1(X2,X2,X2))=X2|k3_xboole_0(X1,k1_enumset1(X2,X2,X2))=k1_enumset1(X2,X2,X2)), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.20/0.49  cnf(c_0_62, plain, (r2_hidden(X1,k1_enumset1(X1,X2,X3))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_54])])).
% 0.20/0.49  cnf(c_0_63, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k3_xboole_0(X2,X1),k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))))=k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55, c_0_29]), c_0_49])).
% 0.20/0.49  cnf(c_0_64, plain, (k5_xboole_0(k1_xboole_0,X1)=k5_xboole_0(X2,k5_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_49, c_0_56])).
% 0.20/0.49  cnf(c_0_65, plain, (k3_xboole_0(X1,k5_xboole_0(X2,X2))=k5_xboole_0(X2,X2)), inference(spm,[status(thm)],[c_0_35, c_0_56])).
% 0.20/0.49  cnf(c_0_66, plain, (k5_xboole_0(X1,k5_xboole_0(X2,X2))=X1), inference(spm,[status(thm)],[c_0_36, c_0_56])).
% 0.20/0.49  cnf(c_0_67, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X2,X3)))=k5_xboole_0(X1,X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_56]), c_0_49])).
% 0.20/0.49  cnf(c_0_68, plain, (k1_xboole_0=k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,X2)))), inference(spm,[status(thm)],[c_0_49, c_0_56])).
% 0.20/0.49  cnf(c_0_69, negated_conjecture, (k2_enumset1(esk4_0,esk4_0,esk5_0,esk6_0)!=k1_enumset1(esk4_0,esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.20/0.49  cnf(c_0_70, plain, (k2_enumset1(X1,X2,X3,X4)=k5_xboole_0(k1_enumset1(X1,X1,X1),k5_xboole_0(k1_enumset1(X2,X3,X4),k3_xboole_0(k1_enumset1(X2,X3,X4),k1_enumset1(X1,X1,X1))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59, c_0_38]), c_0_39]), c_0_28])).
% 0.20/0.49  cnf(c_0_71, plain, (k3_xboole_0(X1,k1_enumset1(X2,X2,X2))=k1_enumset1(X2,X2,X2)|~r2_hidden(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_62])])).
% 0.20/0.49  cnf(c_0_72, plain, (k5_xboole_0(k1_xboole_0,X1)=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_48]), c_0_48]), c_0_65]), c_0_66]), c_0_48]), c_0_66])).
% 0.20/0.49  cnf(c_0_73, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,X2)))=k5_xboole_0(X1,X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_36])).
% 0.20/0.49  cnf(c_0_74, negated_conjecture, (k5_xboole_0(k1_enumset1(esk4_0,esk4_0,esk4_0),k5_xboole_0(k1_enumset1(esk4_0,esk5_0,esk6_0),k3_xboole_0(k1_enumset1(esk4_0,esk5_0,esk6_0),k1_enumset1(esk4_0,esk4_0,esk4_0))))!=k1_enumset1(esk4_0,esk5_0,esk6_0)), inference(rw,[status(thm)],[c_0_69, c_0_70])).
% 0.20/0.49  cnf(c_0_75, plain, (k3_xboole_0(k1_enumset1(X1,X2,X3),k1_enumset1(X1,X1,X1))=k1_enumset1(X1,X1,X1)), inference(spm,[status(thm)],[c_0_71, c_0_62])).
% 0.20/0.49  cnf(c_0_76, plain, (k5_xboole_0(X1,k5_xboole_0(X1,X2))=X2), inference(rw,[status(thm)],[c_0_64, c_0_72])).
% 0.20/0.49  cnf(c_0_77, plain, (k5_xboole_0(X1,k5_xboole_0(X2,X1))=X2), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_72]), c_0_72])).
% 0.20/0.49  cnf(c_0_78, negated_conjecture, (k5_xboole_0(k1_enumset1(esk4_0,esk4_0,esk4_0),k5_xboole_0(k1_enumset1(esk4_0,esk5_0,esk6_0),k3_xboole_0(k1_enumset1(esk4_0,esk4_0,esk4_0),k1_enumset1(esk4_0,esk5_0,esk6_0))))!=k1_enumset1(esk4_0,esk5_0,esk6_0)), inference(rw,[status(thm)],[c_0_74, c_0_29])).
% 0.20/0.49  cnf(c_0_79, plain, (k3_xboole_0(k1_enumset1(X1,X1,X1),k1_enumset1(X1,X2,X3))=k1_enumset1(X1,X1,X1)), inference(spm,[status(thm)],[c_0_29, c_0_75])).
% 0.20/0.49  cnf(c_0_80, plain, (k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_76, c_0_77])).
% 0.20/0.49  cnf(c_0_81, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_78, c_0_79]), c_0_80]), c_0_76])]), ['proof']).
% 0.20/0.49  # SZS output end CNFRefutation
% 0.20/0.49  # Proof object total steps             : 82
% 0.20/0.49  # Proof object clause steps            : 51
% 0.20/0.49  # Proof object formula steps           : 31
% 0.20/0.49  # Proof object conjectures             : 7
% 0.20/0.49  # Proof object clause conjectures      : 4
% 0.20/0.49  # Proof object formula conjectures     : 3
% 0.20/0.49  # Proof object initial clauses used    : 16
% 0.20/0.49  # Proof object initial formulas used   : 15
% 0.20/0.49  # Proof object generating inferences   : 19
% 0.20/0.49  # Proof object simplifying inferences  : 41
% 0.20/0.49  # Training examples: 0 positive, 0 negative
% 0.20/0.49  # Parsed axioms                        : 15
% 0.20/0.49  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.49  # Initial clauses                      : 30
% 0.20/0.49  # Removed in clause preprocessing      : 5
% 0.20/0.49  # Initial clauses in saturation        : 25
% 0.20/0.49  # Processed clauses                    : 1495
% 0.20/0.49  # ...of these trivial                  : 211
% 0.20/0.49  # ...subsumed                          : 1019
% 0.20/0.49  # ...remaining for further processing  : 265
% 0.20/0.49  # Other redundant clauses eliminated   : 199
% 0.20/0.49  # Clauses deleted for lack of memory   : 0
% 0.20/0.49  # Backward-subsumed                    : 4
% 0.20/0.49  # Backward-rewritten                   : 26
% 0.20/0.49  # Generated clauses                    : 9680
% 0.20/0.49  # ...of the previous two non-trivial   : 7164
% 0.20/0.49  # Contextual simplify-reflections      : 2
% 0.20/0.49  # Paramodulations                      : 9327
% 0.20/0.49  # Factorizations                       : 158
% 0.20/0.49  # Equation resolutions                 : 199
% 0.20/0.49  # Propositional unsat checks           : 0
% 0.20/0.49  #    Propositional check models        : 0
% 0.20/0.49  #    Propositional check unsatisfiable : 0
% 0.20/0.49  #    Propositional clauses             : 0
% 0.20/0.49  #    Propositional clauses after purity: 0
% 0.20/0.49  #    Propositional unsat core size     : 0
% 0.20/0.49  #    Propositional preprocessing time  : 0.000
% 0.20/0.49  #    Propositional encoding time       : 0.000
% 0.20/0.49  #    Propositional solver time         : 0.000
% 0.20/0.49  #    Success case prop preproc time    : 0.000
% 0.20/0.49  #    Success case prop encoding time   : 0.000
% 0.20/0.49  #    Success case prop solver time     : 0.000
% 0.20/0.49  # Current number of processed clauses  : 202
% 0.20/0.49  #    Positive orientable unit clauses  : 48
% 0.20/0.49  #    Positive unorientable unit clauses: 7
% 0.20/0.49  #    Negative unit clauses             : 0
% 0.20/0.49  #    Non-unit-clauses                  : 147
% 0.20/0.49  # Current number of unprocessed clauses: 5116
% 0.20/0.49  # ...number of literals in the above   : 15534
% 0.20/0.49  # Current number of archived formulas  : 0
% 0.20/0.49  # Current number of archived clauses   : 59
% 0.20/0.49  # Clause-clause subsumption calls (NU) : 3568
% 0.20/0.49  # Rec. Clause-clause subsumption calls : 2549
% 0.20/0.49  # Non-unit clause-clause subsumptions  : 329
% 0.20/0.49  # Unit Clause-clause subsumption calls : 692
% 0.20/0.49  # Rewrite failures with RHS unbound    : 58
% 0.20/0.49  # BW rewrite match attempts            : 708
% 0.20/0.49  # BW rewrite match successes           : 317
% 0.20/0.49  # Condensation attempts                : 0
% 0.20/0.49  # Condensation successes               : 0
% 0.20/0.49  # Termbank termtop insertions          : 132511
% 0.20/0.49  
% 0.20/0.49  # -------------------------------------------------
% 0.20/0.49  # User time                : 0.137 s
% 0.20/0.49  # System time              : 0.010 s
% 0.20/0.49  # Total time               : 0.147 s
% 0.20/0.49  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
