%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:33:22 EST 2020

% Result     : Theorem 47.13s
% Output     : CNFRefutation 47.23s
% Verified   : 
% Statistics : Number of formulae       :  140 (4438 expanded)
%              Number of clauses        :  111 (2075 expanded)
%              Number of leaves         :   14 (1177 expanded)
%              Depth                    :   21
%              Number of atoms          :  222 (4785 expanded)
%              Number of equality atoms :   88 (4234 expanded)
%              Maximal formula depth    :    9 (   2 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t22_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k3_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(t51_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t77_xboole_1,conjecture,(
    ! [X1,X2,X3] :
      ~ ( ~ r1_xboole_0(X1,X2)
        & r1_tarski(X1,X3)
        & r1_xboole_0(X1,k3_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_xboole_1)).

fof(t19_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X1,X3) )
     => r1_tarski(X1,k3_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t23_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_xboole_1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(t65_xboole_1,axiom,(
    ! [X1] : r1_xboole_0(X1,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(c_0_14,plain,(
    ! [X21,X22] : k2_xboole_0(X21,k3_xboole_0(X21,X22)) = X21 ),
    inference(variable_rename,[status(thm)],[t22_xboole_1])).

fof(c_0_15,plain,(
    ! [X27,X28] : k4_xboole_0(X27,k4_xboole_0(X27,X28)) = k3_xboole_0(X27,X28) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_16,plain,(
    ! [X26] : k3_xboole_0(X26,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

fof(c_0_17,plain,(
    ! [X29,X30] : k2_xboole_0(k3_xboole_0(X29,X30),k4_xboole_0(X29,X30)) = X29 ),
    inference(variable_rename,[status(thm)],[t51_xboole_1])).

cnf(c_0_18,plain,
    ( k2_xboole_0(X1,k3_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_22,plain,(
    ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_23,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = X1 ),
    inference(rw,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_24,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_20,c_0_19])).

fof(c_0_25,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ~ ( ~ r1_xboole_0(X1,X2)
          & r1_tarski(X1,X3)
          & r1_xboole_0(X1,k3_xboole_0(X2,X3)) ) ),
    inference(assume_negation,[status(cth)],[t77_xboole_1])).

cnf(c_0_26,plain,
    ( k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,X2)) = X1 ),
    inference(rw,[status(thm)],[c_0_21,c_0_19])).

cnf(c_0_27,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

fof(c_0_29,plain,(
    ! [X18,X19,X20] :
      ( ~ r1_tarski(X18,X19)
      | ~ r1_tarski(X18,X20)
      | r1_tarski(X18,k3_xboole_0(X19,X20)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).

fof(c_0_30,plain,(
    ! [X8,X9] :
      ( ( ~ r1_xboole_0(X8,X9)
        | k3_xboole_0(X8,X9) = k1_xboole_0 )
      & ( k3_xboole_0(X8,X9) != k1_xboole_0
        | r1_xboole_0(X8,X9) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

fof(c_0_31,negated_conjecture,
    ( ~ r1_xboole_0(esk2_0,esk3_0)
    & r1_tarski(esk2_0,esk4_0)
    & r1_xboole_0(esk2_0,k3_xboole_0(esk3_0,esk4_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_25])])])])).

fof(c_0_32,plain,(
    ! [X6,X7] : k3_xboole_0(X6,X7) = k3_xboole_0(X7,X6) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_33,plain,(
    ! [X23,X24,X25] : k3_xboole_0(X23,k2_xboole_0(X24,X25)) = k2_xboole_0(k3_xboole_0(X23,X24),k3_xboole_0(X23,X25)) ),
    inference(variable_rename,[status(thm)],[t23_xboole_1])).

cnf(c_0_34,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))) = X1 ),
    inference(rw,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_35,plain,
    ( k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_36,plain,
    ( r1_tarski(X1,k3_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_37,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_38,negated_conjecture,
    ( r1_xboole_0(esk2_0,k3_xboole_0(esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_39,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_40,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_41,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_24]),c_0_35])).

cnf(c_0_42,plain,
    ( r1_tarski(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))
    | ~ r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_36,c_0_19])).

cnf(c_0_43,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_37,c_0_19])).

cnf(c_0_44,negated_conjecture,
    ( r1_xboole_0(esk2_0,k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0))) ),
    inference(rw,[status(thm)],[c_0_38,c_0_19])).

cnf(c_0_45,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X2,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_19]),c_0_19])).

fof(c_0_46,plain,(
    ! [X32,X33] : r1_tarski(X32,k2_xboole_0(X32,X33)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

cnf(c_0_47,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(X2,X3))) = k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,k4_xboole_0(X1,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_19]),c_0_19]),c_0_19])).

cnf(c_0_48,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_24,c_0_41])).

fof(c_0_49,plain,(
    ! [X16,X17] :
      ( ~ r1_tarski(X16,X17)
      | k2_xboole_0(X16,X17) = X17 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_50,plain,
    ( r1_tarski(X1,k1_xboole_0)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3)
    | ~ r1_xboole_0(X3,X2) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_51,negated_conjecture,
    ( r1_xboole_0(esk2_0,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk3_0))) ),
    inference(rw,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_52,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_53,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,X2)))) = X1 ),
    inference(spm,[status(thm)],[c_0_34,c_0_47])).

cnf(c_0_54,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(X1,X2))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_41]),c_0_23])).

cnf(c_0_55,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_56,negated_conjecture,
    ( r1_tarski(X1,k1_xboole_0)
    | ~ r1_tarski(X1,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk3_0)))
    | ~ r1_tarski(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_57,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_52,c_0_34])).

fof(c_0_58,plain,(
    ! [X10,X11,X13,X14,X15] :
      ( ( r1_xboole_0(X10,X11)
        | r2_hidden(esk1_2(X10,X11),k3_xboole_0(X10,X11)) )
      & ( ~ r2_hidden(X15,k3_xboole_0(X13,X14))
        | ~ r1_xboole_0(X13,X14) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

cnf(c_0_59,plain,
    ( k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1))),k4_xboole_0(X1,k4_xboole_0(X1,X3))) = k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X2),X3))) ),
    inference(spm,[status(thm)],[c_0_47,c_0_45])).

cnf(c_0_60,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,k2_xboole_0(X3,k4_xboole_0(X1,X3)))))) = k4_xboole_0(X1,k4_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_53]),c_0_48]),c_0_28])).

cnf(c_0_61,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_34]),c_0_45])).

cnf(c_0_62,plain,
    ( k2_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_55,c_0_27])).

cnf(c_0_63,negated_conjecture,
    ( r1_tarski(k4_xboole_0(k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk3_0)),X1),k1_xboole_0)
    | ~ r1_tarski(k4_xboole_0(k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk3_0)),X1),esk2_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_64,plain,
    ( r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X2) ),
    inference(spm,[status(thm)],[c_0_57,c_0_45])).

cnf(c_0_65,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_66,plain,
    ( k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,k4_xboole_0(X3,k4_xboole_0(X3,X1)))) = k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,X3)))) ),
    inference(spm,[status(thm)],[c_0_47,c_0_45])).

cnf(c_0_67,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1))) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_53]),c_0_48]),c_0_28]),c_0_60]),c_0_61])).

cnf(c_0_68,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_55,c_0_62])).

cnf(c_0_69,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk3_0)))),k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_45])).

cnf(c_0_70,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_52,c_0_35])).

cnf(c_0_71,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(X2,X3))) = k4_xboole_0(X1,k4_xboole_0(X1,X3))
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_43]),c_0_35])).

cnf(c_0_72,plain,
    ( k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = X2 ),
    inference(spm,[status(thm)],[c_0_34,c_0_45])).

cnf(c_0_73,plain,
    ( ~ r1_xboole_0(X2,X3)
    | ~ r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))) ),
    inference(rw,[status(thm)],[c_0_65,c_0_19])).

cnf(c_0_74,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,k2_xboole_0(X1,X3))))) = k4_xboole_0(X1,k4_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_54]),c_0_48]),c_0_28])).

cnf(c_0_75,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,X3)))) = k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,X3)) ),
    inference(rw,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_76,negated_conjecture,
    ( k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk3_0)))) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_70])])).

cnf(c_0_77,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X3,k4_xboole_0(X3,X2))))) = k4_xboole_0(X1,k4_xboole_0(X1,X2))
    | ~ r1_xboole_0(X1,k4_xboole_0(X3,k4_xboole_0(X3,X2))) ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_78,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))
    | ~ r1_xboole_0(X3,X2) ),
    inference(spm,[status(thm)],[c_0_73,c_0_45])).

cnf(c_0_79,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(X2,X1))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_41]),c_0_27]),c_0_23])).

cnf(c_0_80,plain,
    ( k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,k2_xboole_0(X1,X3))) = k4_xboole_0(X1,k4_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_81,negated_conjecture,
    ( k4_xboole_0(esk2_0,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk3_0))) = esk2_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_76]),c_0_28])).

fof(c_0_82,plain,(
    ! [X31] : r1_xboole_0(X31,k1_xboole_0) ),
    inference(variable_rename,[status(thm)],[t65_xboole_1])).

cnf(c_0_83,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3))) = k4_xboole_0(X1,k4_xboole_0(X1,X2))
    | ~ r1_xboole_0(X1,k4_xboole_0(X3,k4_xboole_0(X3,X2))) ),
    inference(rw,[status(thm)],[c_0_77,c_0_67])).

cnf(c_0_84,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,k1_xboole_0))
    | ~ r1_xboole_0(X2,k4_xboole_0(X2,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_73,c_0_24])).

cnf(c_0_85,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk1_2(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_86,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(X2,X3))) = k4_xboole_0(X1,k4_xboole_0(X1,X2))
    | ~ r1_xboole_0(X1,X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_43]),c_0_28])).

cnf(c_0_87,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_xboole_0(k2_xboole_0(X3,X2),X2) ),
    inference(spm,[status(thm)],[c_0_78,c_0_79])).

cnf(c_0_88,negated_conjecture,
    ( k4_xboole_0(esk2_0,k2_xboole_0(esk2_0,X1)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_81]),c_0_48]),c_0_35]),c_0_48])).

cnf(c_0_89,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_82])).

cnf(c_0_90,negated_conjecture,
    ( k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,k4_xboole_0(esk3_0,esk4_0))) = k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_83,c_0_51])).

cnf(c_0_91,plain,
    ( r1_xboole_0(X1,X2)
    | k3_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_92,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_xboole_0(X2,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_84,c_0_41]),c_0_41])).

cnf(c_0_93,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk1_2(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_85,c_0_19])).

cnf(c_0_94,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,X3)))) = X1
    | ~ r1_xboole_0(X1,X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_43]),c_0_41]),c_0_27]),c_0_23])).

cnf(c_0_95,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3))) = k4_xboole_0(X1,k4_xboole_0(X1,X2))
    | ~ r1_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_86,c_0_34])).

cnf(c_0_96,plain,
    ( ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1)
    | ~ r1_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_87,c_0_62])).

cnf(c_0_97,negated_conjecture,
    ( k4_xboole_0(esk2_0,X1) = k1_xboole_0
    | ~ r1_tarski(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_88,c_0_55])).

cnf(c_0_98,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_24]),c_0_89])])).

cnf(c_0_99,plain,
    ( r1_tarski(X1,k4_xboole_0(X1,X2))
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_43]),c_0_41])).

cnf(c_0_100,negated_conjecture,
    ( k4_xboole_0(esk2_0,k4_xboole_0(esk3_0,esk4_0)) = k4_xboole_0(esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_90]),c_0_61])).

cnf(c_0_101,plain,
    ( r1_xboole_0(X1,X2)
    | k4_xboole_0(X1,k4_xboole_0(X1,X2)) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_91,c_0_19])).

cnf(c_0_102,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_92,c_0_93])).

cnf(c_0_103,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = X1
    | ~ r1_xboole_0(X1,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_48]),c_0_28])).

cnf(c_0_104,plain,
    ( k4_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,k4_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_68,c_0_57])).

cnf(c_0_105,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_52,c_0_23])).

cnf(c_0_106,negated_conjecture,
    ( k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,k4_xboole_0(esk4_0,esk3_0))) = k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_95,c_0_51])).

cnf(c_0_107,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,k4_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_96,c_0_57])).

cnf(c_0_108,negated_conjecture,
    ( r1_xboole_0(esk2_0,X1)
    | ~ r1_tarski(esk2_0,k4_xboole_0(esk2_0,X1)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_97]),c_0_98])).

cnf(c_0_109,negated_conjecture,
    ( r1_tarski(esk2_0,k4_xboole_0(esk2_0,esk3_0))
    | ~ r1_xboole_0(esk2_0,k4_xboole_0(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_99,c_0_100])).

cnf(c_0_110,negated_conjecture,
    ( ~ r1_xboole_0(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_111,plain,
    ( r1_xboole_0(X1,X2)
    | k4_xboole_0(X2,k4_xboole_0(X2,X1)) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_101,c_0_45])).

cnf(c_0_112,plain,
    ( k4_xboole_0(X1,X2) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_43]),c_0_28])).

cnf(c_0_113,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X1,X1) ),
    inference(spm,[status(thm)],[c_0_102,c_0_103])).

cnf(c_0_114,plain,
    ( r1_xboole_0(X1,X1)
    | X1 != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_48]),c_0_41])).

cnf(c_0_115,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_42]),c_0_105])])).

cnf(c_0_116,negated_conjecture,
    ( k4_xboole_0(esk2_0,k4_xboole_0(esk4_0,esk3_0)) = k4_xboole_0(esk2_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_106]),c_0_61])).

cnf(c_0_117,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(X2,X3))) = k4_xboole_0(X1,k4_xboole_0(X1,X3))
    | ~ r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,k4_xboole_0(X1,X3))) ),
    inference(spm,[status(thm)],[c_0_55,c_0_47])).

cnf(c_0_118,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_107,c_0_93])).

cnf(c_0_119,negated_conjecture,
    ( ~ r1_xboole_0(esk2_0,k4_xboole_0(esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_109]),c_0_110])).

cnf(c_0_120,plain,
    ( r1_xboole_0(X1,X2)
    | X2 != k1_xboole_0
    | ~ r1_xboole_0(X2,k4_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_111,c_0_112])).

cnf(c_0_121,plain,
    ( r1_xboole_0(X1,X2)
    | X1 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_113,c_0_114])).

cnf(c_0_122,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1))) = X1 ),
    inference(spm,[status(thm)],[c_0_23,c_0_45])).

cnf(c_0_123,negated_conjecture,
    ( k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk4_0)) = esk2_0
    | ~ r1_tarski(esk2_0,k4_xboole_0(esk4_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_115,c_0_106])).

cnf(c_0_124,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk4_0)),k4_xboole_0(esk4_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_64,c_0_116])).

cnf(c_0_125,negated_conjecture,
    ( r1_tarski(esk2_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_126,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(X2,X3))) = k4_xboole_0(X1,k4_xboole_0(X1,X3))
    | ~ r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117,c_0_42]),c_0_57])])).

cnf(c_0_127,negated_conjecture,
    ( ~ r1_xboole_0(esk2_0,k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_118,c_0_100]),c_0_119])).

cnf(c_0_128,plain,
    ( r1_xboole_0(X1,X2)
    | X2 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_120,c_0_121])).

cnf(c_0_129,negated_conjecture,
    ( k2_xboole_0(esk2_0,esk4_0) = esk4_0
    | ~ r1_tarski(esk2_0,k4_xboole_0(esk4_0,esk3_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_122,c_0_123]),c_0_27])).

cnf(c_0_130,negated_conjecture,
    ( r1_tarski(esk2_0,k4_xboole_0(esk4_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_124,c_0_115]),c_0_125])])).

cnf(c_0_131,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))) = k4_xboole_0(X1,k4_xboole_0(X1,X2))
    | ~ r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3))),k4_xboole_0(X2,k4_xboole_0(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_126,c_0_34])).

cnf(c_0_132,negated_conjecture,
    ( k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0)) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_127,c_0_128])).

cnf(c_0_133,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(X2,X3))) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_115]),c_0_23])).

cnf(c_0_134,negated_conjecture,
    ( k2_xboole_0(esk2_0,esk4_0) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_129,c_0_130])])).

cnf(c_0_135,negated_conjecture,
    ( ~ r1_tarski(k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0)),k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk3_0))) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_131,c_0_100]),c_0_45]),c_0_81]),c_0_48]),c_0_45]),c_0_132])).

cnf(c_0_136,negated_conjecture,
    ( k4_xboole_0(X1,k4_xboole_0(X1,esk4_0)) = X1
    | ~ r1_tarski(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_133,c_0_134])).

cnf(c_0_137,negated_conjecture,
    ( ~ r1_tarski(k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0)),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_135,c_0_42]),c_0_64])])).

cnf(c_0_138,negated_conjecture,
    ( r1_tarski(X1,esk4_0)
    | ~ r1_tarski(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_64,c_0_136])).

cnf(c_0_139,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_137,c_0_138]),c_0_57])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:21:52 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 47.13/47.40  # AutoSched0-Mode selected heuristic G_E___208_C48_F1_AE_CS_SP_PS_S0Y
% 47.13/47.40  # and selection function SelectMaxLComplexAvoidPosPred.
% 47.13/47.40  #
% 47.13/47.40  # Preprocessing time       : 0.026 s
% 47.13/47.40  # Presaturation interreduction done
% 47.13/47.40  
% 47.13/47.40  # Proof found!
% 47.13/47.40  # SZS status Theorem
% 47.13/47.40  # SZS output start CNFRefutation
% 47.13/47.40  fof(t22_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k3_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_xboole_1)).
% 47.13/47.40  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 47.13/47.40  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 47.13/47.40  fof(t51_xboole_1, axiom, ![X1, X2]:k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 47.13/47.40  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 47.13/47.40  fof(t77_xboole_1, conjecture, ![X1, X2, X3]:~(((~(r1_xboole_0(X1,X2))&r1_tarski(X1,X3))&r1_xboole_0(X1,k3_xboole_0(X2,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_xboole_1)).
% 47.13/47.40  fof(t19_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X1,X3))=>r1_tarski(X1,k3_xboole_0(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 47.13/47.40  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 47.13/47.40  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 47.13/47.40  fof(t23_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(X1,k2_xboole_0(X2,X3))=k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_xboole_1)).
% 47.13/47.40  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 47.13/47.40  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 47.13/47.40  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 47.13/47.40  fof(t65_xboole_1, axiom, ![X1]:r1_xboole_0(X1,k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 47.13/47.40  fof(c_0_14, plain, ![X21, X22]:k2_xboole_0(X21,k3_xboole_0(X21,X22))=X21, inference(variable_rename,[status(thm)],[t22_xboole_1])).
% 47.13/47.40  fof(c_0_15, plain, ![X27, X28]:k4_xboole_0(X27,k4_xboole_0(X27,X28))=k3_xboole_0(X27,X28), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 47.13/47.40  fof(c_0_16, plain, ![X26]:k3_xboole_0(X26,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 47.13/47.40  fof(c_0_17, plain, ![X29, X30]:k2_xboole_0(k3_xboole_0(X29,X30),k4_xboole_0(X29,X30))=X29, inference(variable_rename,[status(thm)],[t51_xboole_1])).
% 47.13/47.40  cnf(c_0_18, plain, (k2_xboole_0(X1,k3_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_14])).
% 47.13/47.40  cnf(c_0_19, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 47.13/47.40  cnf(c_0_20, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_16])).
% 47.13/47.40  cnf(c_0_21, plain, (k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_17])).
% 47.13/47.40  fof(c_0_22, plain, ![X4, X5]:k2_xboole_0(X4,X5)=k2_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 47.13/47.40  cnf(c_0_23, plain, (k2_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2)))=X1), inference(rw,[status(thm)],[c_0_18, c_0_19])).
% 47.13/47.40  cnf(c_0_24, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))=k1_xboole_0), inference(rw,[status(thm)],[c_0_20, c_0_19])).
% 47.13/47.40  fof(c_0_25, negated_conjecture, ~(![X1, X2, X3]:~(((~(r1_xboole_0(X1,X2))&r1_tarski(X1,X3))&r1_xboole_0(X1,k3_xboole_0(X2,X3))))), inference(assume_negation,[status(cth)],[t77_xboole_1])).
% 47.13/47.40  cnf(c_0_26, plain, (k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,X2))=X1), inference(rw,[status(thm)],[c_0_21, c_0_19])).
% 47.13/47.40  cnf(c_0_27, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 47.13/47.40  cnf(c_0_28, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 47.13/47.40  fof(c_0_29, plain, ![X18, X19, X20]:(~r1_tarski(X18,X19)|~r1_tarski(X18,X20)|r1_tarski(X18,k3_xboole_0(X19,X20))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).
% 47.13/47.40  fof(c_0_30, plain, ![X8, X9]:((~r1_xboole_0(X8,X9)|k3_xboole_0(X8,X9)=k1_xboole_0)&(k3_xboole_0(X8,X9)!=k1_xboole_0|r1_xboole_0(X8,X9))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 47.13/47.40  fof(c_0_31, negated_conjecture, ((~r1_xboole_0(esk2_0,esk3_0)&r1_tarski(esk2_0,esk4_0))&r1_xboole_0(esk2_0,k3_xboole_0(esk3_0,esk4_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_25])])])])).
% 47.13/47.40  fof(c_0_32, plain, ![X6, X7]:k3_xboole_0(X6,X7)=k3_xboole_0(X7,X6), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 47.13/47.40  fof(c_0_33, plain, ![X23, X24, X25]:k3_xboole_0(X23,k2_xboole_0(X24,X25))=k2_xboole_0(k3_xboole_0(X23,X24),k3_xboole_0(X23,X25)), inference(variable_rename,[status(thm)],[t23_xboole_1])).
% 47.13/47.40  cnf(c_0_34, plain, (k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))=X1), inference(rw,[status(thm)],[c_0_26, c_0_27])).
% 47.13/47.40  cnf(c_0_35, plain, (k2_xboole_0(k1_xboole_0,X1)=X1), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 47.13/47.40  cnf(c_0_36, plain, (r1_tarski(X1,k3_xboole_0(X2,X3))|~r1_tarski(X1,X2)|~r1_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 47.13/47.40  cnf(c_0_37, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 47.13/47.40  cnf(c_0_38, negated_conjecture, (r1_xboole_0(esk2_0,k3_xboole_0(esk3_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 47.13/47.40  cnf(c_0_39, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 47.13/47.40  cnf(c_0_40, plain, (k3_xboole_0(X1,k2_xboole_0(X2,X3))=k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 47.13/47.40  cnf(c_0_41, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_24]), c_0_35])).
% 47.13/47.40  cnf(c_0_42, plain, (r1_tarski(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))|~r1_tarski(X1,X3)|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_36, c_0_19])).
% 47.13/47.40  cnf(c_0_43, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_37, c_0_19])).
% 47.13/47.40  cnf(c_0_44, negated_conjecture, (r1_xboole_0(esk2_0,k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0)))), inference(rw,[status(thm)],[c_0_38, c_0_19])).
% 47.13/47.40  cnf(c_0_45, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k4_xboole_0(X2,k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39, c_0_19]), c_0_19])).
% 47.13/47.40  fof(c_0_46, plain, ![X32, X33]:r1_tarski(X32,k2_xboole_0(X32,X33)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 47.13/47.40  cnf(c_0_47, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(X2,X3)))=k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,k4_xboole_0(X1,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_19]), c_0_19]), c_0_19])).
% 47.13/47.40  cnf(c_0_48, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[c_0_24, c_0_41])).
% 47.13/47.40  fof(c_0_49, plain, ![X16, X17]:(~r1_tarski(X16,X17)|k2_xboole_0(X16,X17)=X17), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 47.13/47.40  cnf(c_0_50, plain, (r1_tarski(X1,k1_xboole_0)|~r1_tarski(X1,X2)|~r1_tarski(X1,X3)|~r1_xboole_0(X3,X2)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 47.13/47.40  cnf(c_0_51, negated_conjecture, (r1_xboole_0(esk2_0,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk3_0)))), inference(rw,[status(thm)],[c_0_44, c_0_45])).
% 47.13/47.40  cnf(c_0_52, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 47.13/47.40  cnf(c_0_53, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,X2))))=X1), inference(spm,[status(thm)],[c_0_34, c_0_47])).
% 47.13/47.40  cnf(c_0_54, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(X1,X2)))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_41]), c_0_23])).
% 47.13/47.40  cnf(c_0_55, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 47.13/47.40  cnf(c_0_56, negated_conjecture, (r1_tarski(X1,k1_xboole_0)|~r1_tarski(X1,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk3_0)))|~r1_tarski(X1,esk2_0)), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 47.13/47.40  cnf(c_0_57, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(spm,[status(thm)],[c_0_52, c_0_34])).
% 47.13/47.40  fof(c_0_58, plain, ![X10, X11, X13, X14, X15]:((r1_xboole_0(X10,X11)|r2_hidden(esk1_2(X10,X11),k3_xboole_0(X10,X11)))&(~r2_hidden(X15,k3_xboole_0(X13,X14))|~r1_xboole_0(X13,X14))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 47.13/47.40  cnf(c_0_59, plain, (k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1))),k4_xboole_0(X1,k4_xboole_0(X1,X3)))=k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X2),X3)))), inference(spm,[status(thm)],[c_0_47, c_0_45])).
% 47.13/47.40  cnf(c_0_60, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,k2_xboole_0(X3,k4_xboole_0(X1,X3))))))=k4_xboole_0(X1,k4_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_53]), c_0_48]), c_0_28])).
% 47.13/47.40  cnf(c_0_61, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2)))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_34]), c_0_45])).
% 47.13/47.40  cnf(c_0_62, plain, (k2_xboole_0(X1,X2)=X1|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_55, c_0_27])).
% 47.13/47.40  cnf(c_0_63, negated_conjecture, (r1_tarski(k4_xboole_0(k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk3_0)),X1),k1_xboole_0)|~r1_tarski(k4_xboole_0(k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk3_0)),X1),esk2_0)), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 47.13/47.40  cnf(c_0_64, plain, (r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X2)), inference(spm,[status(thm)],[c_0_57, c_0_45])).
% 47.13/47.40  cnf(c_0_65, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 47.13/47.40  cnf(c_0_66, plain, (k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,k4_xboole_0(X3,k4_xboole_0(X3,X1))))=k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,X3))))), inference(spm,[status(thm)],[c_0_47, c_0_45])).
% 47.13/47.40  cnf(c_0_67, plain, (k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1)))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_53]), c_0_48]), c_0_28]), c_0_60]), c_0_61])).
% 47.13/47.40  cnf(c_0_68, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_55, c_0_62])).
% 47.13/47.40  cnf(c_0_69, negated_conjecture, (r1_tarski(k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk3_0)))),k1_xboole_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_45])).
% 47.13/47.40  cnf(c_0_70, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_52, c_0_35])).
% 47.13/47.40  cnf(c_0_71, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(X2,X3)))=k4_xboole_0(X1,k4_xboole_0(X1,X3))|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_43]), c_0_35])).
% 47.13/47.40  cnf(c_0_72, plain, (k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,X2))))=X2), inference(spm,[status(thm)],[c_0_34, c_0_45])).
% 47.13/47.40  cnf(c_0_73, plain, (~r1_xboole_0(X2,X3)|~r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))), inference(rw,[status(thm)],[c_0_65, c_0_19])).
% 47.13/47.40  cnf(c_0_74, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,k2_xboole_0(X1,X3)))))=k4_xboole_0(X1,k4_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_54]), c_0_48]), c_0_28])).
% 47.13/47.40  cnf(c_0_75, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,X3))))=k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,X3))), inference(rw,[status(thm)],[c_0_66, c_0_67])).
% 47.13/47.40  cnf(c_0_76, negated_conjecture, (k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk3_0))))=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_70])])).
% 47.13/47.40  cnf(c_0_77, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X3,k4_xboole_0(X3,X2)))))=k4_xboole_0(X1,k4_xboole_0(X1,X2))|~r1_xboole_0(X1,k4_xboole_0(X3,k4_xboole_0(X3,X2)))), inference(spm,[status(thm)],[c_0_71, c_0_72])).
% 47.13/47.40  cnf(c_0_78, plain, (~r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))|~r1_xboole_0(X3,X2)), inference(spm,[status(thm)],[c_0_73, c_0_45])).
% 47.13/47.40  cnf(c_0_79, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(X2,X1)))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_41]), c_0_27]), c_0_23])).
% 47.13/47.40  cnf(c_0_80, plain, (k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,k2_xboole_0(X1,X3)))=k4_xboole_0(X1,k4_xboole_0(X1,X2))), inference(rw,[status(thm)],[c_0_74, c_0_75])).
% 47.13/47.40  cnf(c_0_81, negated_conjecture, (k4_xboole_0(esk2_0,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk3_0)))=esk2_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_76]), c_0_28])).
% 47.13/47.40  fof(c_0_82, plain, ![X31]:r1_xboole_0(X31,k1_xboole_0), inference(variable_rename,[status(thm)],[t65_xboole_1])).
% 47.13/47.40  cnf(c_0_83, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3)))=k4_xboole_0(X1,k4_xboole_0(X1,X2))|~r1_xboole_0(X1,k4_xboole_0(X3,k4_xboole_0(X3,X2)))), inference(rw,[status(thm)],[c_0_77, c_0_67])).
% 47.13/47.40  cnf(c_0_84, plain, (~r2_hidden(X1,k4_xboole_0(X2,k1_xboole_0))|~r1_xboole_0(X2,k4_xboole_0(X2,k1_xboole_0))), inference(spm,[status(thm)],[c_0_73, c_0_24])).
% 47.13/47.40  cnf(c_0_85, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk1_2(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_58])).
% 47.13/47.40  cnf(c_0_86, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(X2,X3)))=k4_xboole_0(X1,k4_xboole_0(X1,X2))|~r1_xboole_0(X1,X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_43]), c_0_28])).
% 47.13/47.40  cnf(c_0_87, plain, (~r2_hidden(X1,X2)|~r1_xboole_0(k2_xboole_0(X3,X2),X2)), inference(spm,[status(thm)],[c_0_78, c_0_79])).
% 47.13/47.40  cnf(c_0_88, negated_conjecture, (k4_xboole_0(esk2_0,k2_xboole_0(esk2_0,X1))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_81]), c_0_48]), c_0_35]), c_0_48])).
% 47.13/47.40  cnf(c_0_89, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_82])).
% 47.13/47.40  cnf(c_0_90, negated_conjecture, (k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,k4_xboole_0(esk3_0,esk4_0)))=k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_83, c_0_51])).
% 47.13/47.40  cnf(c_0_91, plain, (r1_xboole_0(X1,X2)|k3_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_30])).
% 47.13/47.40  cnf(c_0_92, plain, (~r2_hidden(X1,X2)|~r1_xboole_0(X2,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_84, c_0_41]), c_0_41])).
% 47.13/47.40  cnf(c_0_93, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk1_2(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))), inference(rw,[status(thm)],[c_0_85, c_0_19])).
% 47.13/47.40  cnf(c_0_94, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,X3))))=X1|~r1_xboole_0(X1,X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_43]), c_0_41]), c_0_27]), c_0_23])).
% 47.13/47.40  cnf(c_0_95, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3)))=k4_xboole_0(X1,k4_xboole_0(X1,X2))|~r1_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))), inference(spm,[status(thm)],[c_0_86, c_0_34])).
% 47.13/47.40  cnf(c_0_96, plain, (~r1_tarski(X1,X2)|~r2_hidden(X3,X1)|~r1_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_87, c_0_62])).
% 47.13/47.40  cnf(c_0_97, negated_conjecture, (k4_xboole_0(esk2_0,X1)=k1_xboole_0|~r1_tarski(esk2_0,X1)), inference(spm,[status(thm)],[c_0_88, c_0_55])).
% 47.13/47.40  cnf(c_0_98, plain, (~r2_hidden(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_24]), c_0_89])])).
% 47.13/47.40  cnf(c_0_99, plain, (r1_tarski(X1,k4_xboole_0(X1,X2))|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_43]), c_0_41])).
% 47.13/47.40  cnf(c_0_100, negated_conjecture, (k4_xboole_0(esk2_0,k4_xboole_0(esk3_0,esk4_0))=k4_xboole_0(esk2_0,esk3_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_90]), c_0_61])).
% 47.13/47.40  cnf(c_0_101, plain, (r1_xboole_0(X1,X2)|k4_xboole_0(X1,k4_xboole_0(X1,X2))!=k1_xboole_0), inference(rw,[status(thm)],[c_0_91, c_0_19])).
% 47.13/47.40  cnf(c_0_102, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,k4_xboole_0(X1,X2)))), inference(spm,[status(thm)],[c_0_92, c_0_93])).
% 47.13/47.40  cnf(c_0_103, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=X1|~r1_xboole_0(X1,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_48]), c_0_28])).
% 47.13/47.40  cnf(c_0_104, plain, (k4_xboole_0(X1,X2)=X1|~r1_tarski(X1,k4_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_68, c_0_57])).
% 47.13/47.40  cnf(c_0_105, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_52, c_0_23])).
% 47.13/47.40  cnf(c_0_106, negated_conjecture, (k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,k4_xboole_0(esk4_0,esk3_0)))=k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk4_0))), inference(spm,[status(thm)],[c_0_95, c_0_51])).
% 47.13/47.40  cnf(c_0_107, plain, (~r2_hidden(X1,k4_xboole_0(X2,X3))|~r1_xboole_0(X2,k4_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_96, c_0_57])).
% 47.13/47.40  cnf(c_0_108, negated_conjecture, (r1_xboole_0(esk2_0,X1)|~r1_tarski(esk2_0,k4_xboole_0(esk2_0,X1))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_97]), c_0_98])).
% 47.13/47.40  cnf(c_0_109, negated_conjecture, (r1_tarski(esk2_0,k4_xboole_0(esk2_0,esk3_0))|~r1_xboole_0(esk2_0,k4_xboole_0(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_99, c_0_100])).
% 47.13/47.40  cnf(c_0_110, negated_conjecture, (~r1_xboole_0(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 47.13/47.40  cnf(c_0_111, plain, (r1_xboole_0(X1,X2)|k4_xboole_0(X2,k4_xboole_0(X2,X1))!=k1_xboole_0), inference(spm,[status(thm)],[c_0_101, c_0_45])).
% 47.13/47.40  cnf(c_0_112, plain, (k4_xboole_0(X1,X2)=X1|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_43]), c_0_28])).
% 47.13/47.40  cnf(c_0_113, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(X1,X1)), inference(spm,[status(thm)],[c_0_102, c_0_103])).
% 47.13/47.40  cnf(c_0_114, plain, (r1_xboole_0(X1,X1)|X1!=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101, c_0_48]), c_0_41])).
% 47.13/47.40  cnf(c_0_115, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=X1|~r1_tarski(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104, c_0_42]), c_0_105])])).
% 47.13/47.40  cnf(c_0_116, negated_conjecture, (k4_xboole_0(esk2_0,k4_xboole_0(esk4_0,esk3_0))=k4_xboole_0(esk2_0,esk4_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_106]), c_0_61])).
% 47.13/47.40  cnf(c_0_117, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(X2,X3)))=k4_xboole_0(X1,k4_xboole_0(X1,X3))|~r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,k4_xboole_0(X1,X3)))), inference(spm,[status(thm)],[c_0_55, c_0_47])).
% 47.13/47.40  cnf(c_0_118, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2)))), inference(spm,[status(thm)],[c_0_107, c_0_93])).
% 47.13/47.40  cnf(c_0_119, negated_conjecture, (~r1_xboole_0(esk2_0,k4_xboole_0(esk3_0,esk4_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_108, c_0_109]), c_0_110])).
% 47.13/47.40  cnf(c_0_120, plain, (r1_xboole_0(X1,X2)|X2!=k1_xboole_0|~r1_xboole_0(X2,k4_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_111, c_0_112])).
% 47.23/47.40  cnf(c_0_121, plain, (r1_xboole_0(X1,X2)|X1!=k1_xboole_0), inference(spm,[status(thm)],[c_0_113, c_0_114])).
% 47.23/47.40  cnf(c_0_122, plain, (k2_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1)))=X1), inference(spm,[status(thm)],[c_0_23, c_0_45])).
% 47.23/47.40  cnf(c_0_123, negated_conjecture, (k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk4_0))=esk2_0|~r1_tarski(esk2_0,k4_xboole_0(esk4_0,esk3_0))), inference(spm,[status(thm)],[c_0_115, c_0_106])).
% 47.23/47.40  cnf(c_0_124, negated_conjecture, (r1_tarski(k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk4_0)),k4_xboole_0(esk4_0,esk3_0))), inference(spm,[status(thm)],[c_0_64, c_0_116])).
% 47.23/47.40  cnf(c_0_125, negated_conjecture, (r1_tarski(esk2_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 47.23/47.40  cnf(c_0_126, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(X2,X3)))=k4_xboole_0(X1,k4_xboole_0(X1,X3))|~r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117, c_0_42]), c_0_57])])).
% 47.23/47.40  cnf(c_0_127, negated_conjecture, (~r1_xboole_0(esk2_0,k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_118, c_0_100]), c_0_119])).
% 47.23/47.40  cnf(c_0_128, plain, (r1_xboole_0(X1,X2)|X2!=k1_xboole_0), inference(spm,[status(thm)],[c_0_120, c_0_121])).
% 47.23/47.40  cnf(c_0_129, negated_conjecture, (k2_xboole_0(esk2_0,esk4_0)=esk4_0|~r1_tarski(esk2_0,k4_xboole_0(esk4_0,esk3_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_122, c_0_123]), c_0_27])).
% 47.23/47.40  cnf(c_0_130, negated_conjecture, (r1_tarski(esk2_0,k4_xboole_0(esk4_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_124, c_0_115]), c_0_125])])).
% 47.23/47.40  cnf(c_0_131, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))))=k4_xboole_0(X1,k4_xboole_0(X1,X2))|~r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3))),k4_xboole_0(X2,k4_xboole_0(X2,X3)))), inference(spm,[status(thm)],[c_0_126, c_0_34])).
% 47.23/47.40  cnf(c_0_132, negated_conjecture, (k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0))!=k1_xboole_0), inference(spm,[status(thm)],[c_0_127, c_0_128])).
% 47.23/47.40  cnf(c_0_133, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(X2,X3)))=X1|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_115]), c_0_23])).
% 47.23/47.40  cnf(c_0_134, negated_conjecture, (k2_xboole_0(esk2_0,esk4_0)=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_129, c_0_130])])).
% 47.23/47.40  cnf(c_0_135, negated_conjecture, (~r1_tarski(k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0)),k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk3_0)))), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_131, c_0_100]), c_0_45]), c_0_81]), c_0_48]), c_0_45]), c_0_132])).
% 47.23/47.40  cnf(c_0_136, negated_conjecture, (k4_xboole_0(X1,k4_xboole_0(X1,esk4_0))=X1|~r1_tarski(X1,esk2_0)), inference(spm,[status(thm)],[c_0_133, c_0_134])).
% 47.23/47.40  cnf(c_0_137, negated_conjecture, (~r1_tarski(k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0)),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_135, c_0_42]), c_0_64])])).
% 47.23/47.40  cnf(c_0_138, negated_conjecture, (r1_tarski(X1,esk4_0)|~r1_tarski(X1,esk2_0)), inference(spm,[status(thm)],[c_0_64, c_0_136])).
% 47.23/47.40  cnf(c_0_139, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_137, c_0_138]), c_0_57])]), ['proof']).
% 47.23/47.40  # SZS output end CNFRefutation
% 47.23/47.40  # Proof object total steps             : 140
% 47.23/47.40  # Proof object clause steps            : 111
% 47.23/47.40  # Proof object formula steps           : 29
% 47.23/47.40  # Proof object conjectures             : 34
% 47.23/47.40  # Proof object clause conjectures      : 31
% 47.23/47.40  # Proof object formula conjectures     : 3
% 47.23/47.40  # Proof object initial clauses used    : 18
% 47.23/47.40  # Proof object initial formulas used   : 14
% 47.23/47.40  # Proof object generating inferences   : 74
% 47.23/47.40  # Proof object simplifying inferences  : 79
% 47.23/47.40  # Training examples: 0 positive, 0 negative
% 47.23/47.40  # Parsed axioms                        : 14
% 47.23/47.40  # Removed by relevancy pruning/SinE    : 0
% 47.23/47.40  # Initial clauses                      : 18
% 47.23/47.40  # Removed in clause preprocessing      : 1
% 47.23/47.40  # Initial clauses in saturation        : 17
% 47.23/47.40  # Processed clauses                    : 87215
% 47.23/47.40  # ...of these trivial                  : 649
% 47.23/47.40  # ...subsumed                          : 81346
% 47.23/47.40  # ...remaining for further processing  : 5220
% 47.23/47.40  # Other redundant clauses eliminated   : 0
% 47.23/47.40  # Clauses deleted for lack of memory   : 124982
% 47.23/47.40  # Backward-subsumed                    : 312
% 47.23/47.40  # Backward-rewritten                   : 305
% 47.23/47.40  # Generated clauses                    : 4261096
% 47.23/47.40  # ...of the previous two non-trivial   : 3970563
% 47.23/47.40  # Contextual simplify-reflections      : 60
% 47.23/47.40  # Paramodulations                      : 4261094
% 47.23/47.40  # Factorizations                       : 0
% 47.23/47.40  # Equation resolutions                 : 2
% 47.23/47.40  # Propositional unsat checks           : 0
% 47.23/47.40  #    Propositional check models        : 0
% 47.23/47.40  #    Propositional check unsatisfiable : 0
% 47.23/47.40  #    Propositional clauses             : 0
% 47.23/47.40  #    Propositional clauses after purity: 0
% 47.23/47.40  #    Propositional unsat core size     : 0
% 47.23/47.40  #    Propositional preprocessing time  : 0.000
% 47.23/47.40  #    Propositional encoding time       : 0.000
% 47.23/47.40  #    Propositional solver time         : 0.000
% 47.23/47.40  #    Success case prop preproc time    : 0.000
% 47.23/47.40  #    Success case prop encoding time   : 0.000
% 47.23/47.40  #    Success case prop solver time     : 0.000
% 47.23/47.40  # Current number of processed clauses  : 4586
% 47.23/47.40  #    Positive orientable unit clauses  : 143
% 47.23/47.40  #    Positive unorientable unit clauses: 2
% 47.23/47.40  #    Negative unit clauses             : 297
% 47.23/47.40  #    Non-unit-clauses                  : 4144
% 47.23/47.40  # Current number of unprocessed clauses: 1623390
% 47.23/47.40  # ...number of literals in the above   : 6654984
% 47.23/47.40  # Current number of archived formulas  : 0
% 47.23/47.40  # Current number of archived clauses   : 635
% 47.23/47.40  # Clause-clause subsumption calls (NU) : 4573231
% 47.23/47.40  # Rec. Clause-clause subsumption calls : 2222582
% 47.23/47.40  # Non-unit clause-clause subsumptions  : 23818
% 47.23/47.40  # Unit Clause-clause subsumption calls : 241390
% 47.23/47.40  # Rewrite failures with RHS unbound    : 0
% 47.23/47.40  # BW rewrite match attempts            : 2112
% 47.23/47.40  # BW rewrite match successes           : 125
% 47.23/47.40  # Condensation attempts                : 0
% 47.23/47.40  # Condensation successes               : 0
% 47.23/47.40  # Termbank termtop insertions          : 97438432
% 47.23/47.49  
% 47.23/47.49  # -------------------------------------------------
% 47.23/47.49  # User time                : 46.012 s
% 47.23/47.49  # System time              : 1.132 s
% 47.23/47.49  # Total time               : 47.145 s
% 47.23/47.49  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
