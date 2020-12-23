%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:32:39 EST 2020

% Result     : Theorem 1.37s
% Output     : CNFRefutation 1.37s
% Verified   : 
% Statistics : Number of formulae       :   99 (16251 expanded)
%              Number of clauses        :   78 (7633 expanded)
%              Number of leaves         :   10 (4144 expanded)
%              Depth                    :   31
%              Number of atoms          :  164 (24721 expanded)
%              Number of equality atoms :   60 (13760 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t51_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(t63_xboole_1,conjecture,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_xboole_0(X2,X3) )
     => r1_xboole_0(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(c_0_10,plain,(
    ! [X24,X25] : k2_xboole_0(k3_xboole_0(X24,X25),k4_xboole_0(X24,X25)) = X24 ),
    inference(variable_rename,[status(thm)],[t51_xboole_1])).

fof(c_0_11,plain,(
    ! [X22,X23] : k4_xboole_0(X22,k4_xboole_0(X22,X23)) = k3_xboole_0(X22,X23) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

cnf(c_0_12,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_13,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_14,plain,(
    ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_15,plain,(
    ! [X6,X7] :
      ( ( ~ r1_xboole_0(X6,X7)
        | k3_xboole_0(X6,X7) = k1_xboole_0 )
      & ( k3_xboole_0(X6,X7) != k1_xboole_0
        | r1_xboole_0(X6,X7) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

fof(c_0_16,plain,(
    ! [X18] : k2_xboole_0(X18,k1_xboole_0) = X18 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

fof(c_0_17,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( r1_tarski(X1,X2)
          & r1_xboole_0(X2,X3) )
       => r1_xboole_0(X1,X3) ) ),
    inference(assume_negation,[status(cth)],[t63_xboole_1])).

cnf(c_0_18,plain,
    ( k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,X2)) = X1 ),
    inference(rw,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_19,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_22,plain,(
    ! [X8,X9] :
      ( ~ r1_xboole_0(X8,X9)
      | r1_xboole_0(X9,X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

fof(c_0_23,negated_conjecture,
    ( r1_tarski(esk2_0,esk3_0)
    & r1_xboole_0(esk3_0,esk4_0)
    & ~ r1_xboole_0(esk2_0,esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).

cnf(c_0_24,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))) = X1 ),
    inference(rw,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_25,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_20,c_0_13])).

cnf(c_0_26,plain,
    ( k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_21,c_0_19])).

cnf(c_0_27,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,negated_conjecture,
    ( r1_xboole_0(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_29,plain,(
    ! [X10,X11,X13,X14,X15] :
      ( ( r1_xboole_0(X10,X11)
        | r2_hidden(esk1_2(X10,X11),k3_xboole_0(X10,X11)) )
      & ( ~ r2_hidden(X15,k3_xboole_0(X13,X14))
        | ~ r1_xboole_0(X13,X14) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

cnf(c_0_30,plain,
    ( r1_xboole_0(X1,X2)
    | k3_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_31,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26])).

cnf(c_0_32,negated_conjecture,
    ( r1_xboole_0(esk4_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_33,plain,
    ( k4_xboole_0(X1,X2) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_21])).

cnf(c_0_34,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_35,plain,(
    ! [X19,X20,X21] : k4_xboole_0(k4_xboole_0(X19,X20),X21) = k4_xboole_0(X19,k2_xboole_0(X20,X21)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

cnf(c_0_36,plain,
    ( r1_xboole_0(X1,X2)
    | k4_xboole_0(X1,k4_xboole_0(X1,X2)) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_30,c_0_13])).

cnf(c_0_37,negated_conjecture,
    ( k4_xboole_0(esk4_0,k1_xboole_0) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_38,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_25,c_0_33])).

cnf(c_0_39,plain,
    ( ~ r1_xboole_0(X2,X3)
    | ~ r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))) ),
    inference(rw,[status(thm)],[c_0_34,c_0_13])).

cnf(c_0_40,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

fof(c_0_41,plain,(
    ! [X16,X17] :
      ( ~ r1_tarski(X16,X17)
      | k2_xboole_0(X16,X17) = X17 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_42,negated_conjecture,
    ( r1_xboole_0(esk4_0,k1_xboole_0)
    | k4_xboole_0(esk4_0,esk4_0) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_43,negated_conjecture,
    ( k4_xboole_0(esk4_0,esk4_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_38,c_0_32])).

cnf(c_0_44,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,k2_xboole_0(X3,k4_xboole_0(X2,k2_xboole_0(X3,X4)))))
    | ~ r1_xboole_0(k4_xboole_0(X2,X3),X4) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_40])).

cnf(c_0_45,negated_conjecture,
    ( k4_xboole_0(esk3_0,esk3_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_38,c_0_28])).

cnf(c_0_46,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_47,negated_conjecture,
    ( r1_xboole_0(esk4_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_43])])).

cnf(c_0_48,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,k2_xboole_0(X3,k4_xboole_0(X2,X3))))
    | ~ r1_xboole_0(k4_xboole_0(X2,X3),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_21])).

cnf(c_0_49,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk1_2(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_50,negated_conjecture,
    ( k4_xboole_0(esk3_0,k2_xboole_0(esk3_0,X1)) = k4_xboole_0(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_45])).

cnf(c_0_51,plain,
    ( k2_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_46,c_0_19])).

cnf(c_0_52,negated_conjecture,
    ( r1_xboole_0(k1_xboole_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_47])).

cnf(c_0_53,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X2))
    | ~ r1_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X3)),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_24])).

cnf(c_0_54,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk1_2(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_49,c_0_13])).

cnf(c_0_55,negated_conjecture,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0
    | ~ r1_tarski(X1,esk3_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_45])).

cnf(c_0_56,negated_conjecture,
    ( k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_31,c_0_52])).

cnf(c_0_57,negated_conjecture,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_43]),c_0_43]),c_0_37]),c_0_47])])).

cnf(c_0_58,negated_conjecture,
    ( r1_xboole_0(k1_xboole_0,X1)
    | ~ r1_tarski(X1,esk3_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_56]),c_0_57])).

cnf(c_0_59,negated_conjecture,
    ( r1_tarski(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_60,negated_conjecture,
    ( r1_xboole_0(k1_xboole_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_61,negated_conjecture,
    ( r1_xboole_0(esk2_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_60])).

cnf(c_0_62,negated_conjecture,
    ( k4_xboole_0(esk2_0,esk2_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_38,c_0_61])).

cnf(c_0_63,negated_conjecture,
    ( k4_xboole_0(esk2_0,k2_xboole_0(esk2_0,X1)) = k4_xboole_0(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_62])).

cnf(c_0_64,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,k2_xboole_0(X2,X3)))) = k1_xboole_0
    | ~ r1_xboole_0(k4_xboole_0(X1,X2),X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_40]),c_0_40])).

cnf(c_0_65,negated_conjecture,
    ( k4_xboole_0(esk2_0,k2_xboole_0(X1,esk2_0)) = k4_xboole_0(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_63,c_0_19])).

cnf(c_0_66,negated_conjecture,
    ( k4_xboole_0(esk2_0,k2_xboole_0(X1,k4_xboole_0(k1_xboole_0,X1))) = k1_xboole_0
    | ~ r1_xboole_0(k4_xboole_0(esk2_0,X1),esk2_0) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_67,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X3)
    | k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,k2_xboole_0(X2,X3)))) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_40]),c_0_40])).

cnf(c_0_68,negated_conjecture,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,esk2_0)) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_66]),c_0_62]),c_0_60])])).

cnf(c_0_69,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X3)
    | k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,k2_xboole_0(X3,X2)))) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_67,c_0_19])).

cnf(c_0_70,plain,
    ( k2_xboole_0(k4_xboole_0(X1,k2_xboole_0(X2,X3)),k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,k2_xboole_0(X2,X3))))) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_40]),c_0_40])).

cnf(c_0_71,negated_conjecture,
    ( k4_xboole_0(k1_xboole_0,esk2_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_68]),c_0_21])).

cnf(c_0_72,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,k2_xboole_0(X3,X2)))
    | ~ r1_xboole_0(X2,k1_xboole_0)
    | ~ r1_xboole_0(X2,X3) ),
    inference(spm,[status(thm)],[c_0_48,c_0_33])).

cnf(c_0_73,plain,
    ( r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(X2,X3))),X2)
    | k4_xboole_0(X1,k4_xboole_0(X1,X2)) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_74,negated_conjecture,
    ( k4_xboole_0(k1_xboole_0,k2_xboole_0(esk2_0,X1)) = k4_xboole_0(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_71])).

cnf(c_0_75,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_26]),c_0_26]),c_0_24])).

cnf(c_0_76,negated_conjecture,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_56]),c_0_56]),c_0_57])).

cnf(c_0_77,negated_conjecture,
    ( ~ r2_hidden(X1,k4_xboole_0(k1_xboole_0,X2))
    | ~ r1_xboole_0(esk2_0,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_65]),c_0_61])])).

cnf(c_0_78,negated_conjecture,
    ( r1_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1)),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_71]),c_0_75])])).

cnf(c_0_79,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(k1_xboole_0,X2))
    | ~ r1_xboole_0(k1_xboole_0,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_21]),c_0_76])])).

cnf(c_0_80,negated_conjecture,
    ( r1_xboole_0(k1_xboole_0,X1)
    | ~ r1_xboole_0(esk2_0,k4_xboole_0(k1_xboole_0,X1)) ),
    inference(spm,[status(thm)],[c_0_77,c_0_54])).

cnf(c_0_81,negated_conjecture,
    ( r1_xboole_0(esk2_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))) ),
    inference(spm,[status(thm)],[c_0_27,c_0_78])).

cnf(c_0_82,plain,
    ( k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X2),X3)) = k4_xboole_0(k1_xboole_0,X3)
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_40,c_0_25])).

cnf(c_0_83,plain,
    ( r1_xboole_0(k1_xboole_0,X1)
    | ~ r1_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1)) ),
    inference(spm,[status(thm)],[c_0_79,c_0_54])).

cnf(c_0_84,negated_conjecture,
    ( r1_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1)) ),
    inference(spm,[status(thm)],[c_0_80,c_0_81])).

cnf(c_0_85,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = X2
    | ~ r1_xboole_0(X2,k2_xboole_0(k4_xboole_0(X2,X3),X1))
    | ~ r1_xboole_0(X2,X3) ),
    inference(spm,[status(thm)],[c_0_33,c_0_82])).

cnf(c_0_86,plain,
    ( r1_xboole_0(k1_xboole_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_83,c_0_84])])).

cnf(c_0_87,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,X3))) = k4_xboole_0(k1_xboole_0,X2)
    | ~ r1_xboole_0(X1,X3) ),
    inference(spm,[status(thm)],[c_0_82,c_0_19])).

cnf(c_0_88,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_86]),c_0_86])])).

cnf(c_0_89,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X3)
    | k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,X2))) != k1_xboole_0
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_67,c_0_51])).

cnf(c_0_90,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,X3))) = k1_xboole_0
    | ~ r1_xboole_0(X1,X3) ),
    inference(rw,[status(thm)],[c_0_87,c_0_88])).

cnf(c_0_91,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_86])).

cnf(c_0_92,plain,
    ( r1_xboole_0(X1,X2)
    | k4_xboole_0(X1,k2_xboole_0(X3,X1)) != k1_xboole_0
    | ~ r1_tarski(X2,X3)
    | ~ r1_xboole_0(X1,X3) ),
    inference(spm,[status(thm)],[c_0_89,c_0_33])).

cnf(c_0_93,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,X1)) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_75]),c_0_91])])).

cnf(c_0_94,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_tarski(X2,X3)
    | ~ r1_xboole_0(X1,X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_92,c_0_93])])).

cnf(c_0_95,negated_conjecture,
    ( r1_xboole_0(X1,esk2_0)
    | ~ r1_xboole_0(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_94,c_0_59])).

cnf(c_0_96,negated_conjecture,
    ( r1_xboole_0(esk2_0,X1)
    | ~ r1_xboole_0(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_95])).

cnf(c_0_97,negated_conjecture,
    ( ~ r1_xboole_0(esk2_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_98,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_32]),c_0_97]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.32  % Computer   : n005.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 11:57:02 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.18/0.32  # Version: 2.5pre002
% 0.18/0.33  # No SInE strategy applied
% 0.18/0.33  # Trying AutoSched0 for 299 seconds
% 1.37/1.61  # AutoSched0-Mode selected heuristic G_E___208_C48_F1_AE_CS_SP_PS_S0Y
% 1.37/1.61  # and selection function SelectMaxLComplexAvoidPosPred.
% 1.37/1.61  #
% 1.37/1.61  # Preprocessing time       : 0.026 s
% 1.37/1.61  # Presaturation interreduction done
% 1.37/1.61  
% 1.37/1.61  # Proof found!
% 1.37/1.61  # SZS status Theorem
% 1.37/1.61  # SZS output start CNFRefutation
% 1.37/1.61  fof(t51_xboole_1, axiom, ![X1, X2]:k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 1.37/1.61  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 1.37/1.61  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 1.37/1.61  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 1.37/1.61  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 1.37/1.61  fof(t63_xboole_1, conjecture, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_xboole_0(X2,X3))=>r1_xboole_0(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 1.37/1.61  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 1.37/1.61  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 1.37/1.61  fof(t41_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 1.37/1.61  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 1.37/1.61  fof(c_0_10, plain, ![X24, X25]:k2_xboole_0(k3_xboole_0(X24,X25),k4_xboole_0(X24,X25))=X24, inference(variable_rename,[status(thm)],[t51_xboole_1])).
% 1.37/1.61  fof(c_0_11, plain, ![X22, X23]:k4_xboole_0(X22,k4_xboole_0(X22,X23))=k3_xboole_0(X22,X23), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 1.37/1.61  cnf(c_0_12, plain, (k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_10])).
% 1.37/1.61  cnf(c_0_13, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 1.37/1.61  fof(c_0_14, plain, ![X4, X5]:k2_xboole_0(X4,X5)=k2_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 1.37/1.61  fof(c_0_15, plain, ![X6, X7]:((~r1_xboole_0(X6,X7)|k3_xboole_0(X6,X7)=k1_xboole_0)&(k3_xboole_0(X6,X7)!=k1_xboole_0|r1_xboole_0(X6,X7))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 1.37/1.61  fof(c_0_16, plain, ![X18]:k2_xboole_0(X18,k1_xboole_0)=X18, inference(variable_rename,[status(thm)],[t1_boole])).
% 1.37/1.61  fof(c_0_17, negated_conjecture, ~(![X1, X2, X3]:((r1_tarski(X1,X2)&r1_xboole_0(X2,X3))=>r1_xboole_0(X1,X3))), inference(assume_negation,[status(cth)],[t63_xboole_1])).
% 1.37/1.61  cnf(c_0_18, plain, (k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,X2))=X1), inference(rw,[status(thm)],[c_0_12, c_0_13])).
% 1.37/1.61  cnf(c_0_19, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 1.37/1.61  cnf(c_0_20, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 1.37/1.61  cnf(c_0_21, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_16])).
% 1.37/1.61  fof(c_0_22, plain, ![X8, X9]:(~r1_xboole_0(X8,X9)|r1_xboole_0(X9,X8)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 1.37/1.61  fof(c_0_23, negated_conjecture, ((r1_tarski(esk2_0,esk3_0)&r1_xboole_0(esk3_0,esk4_0))&~r1_xboole_0(esk2_0,esk4_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).
% 1.37/1.61  cnf(c_0_24, plain, (k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))=X1), inference(rw,[status(thm)],[c_0_18, c_0_19])).
% 1.37/1.61  cnf(c_0_25, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_20, c_0_13])).
% 1.37/1.61  cnf(c_0_26, plain, (k2_xboole_0(k1_xboole_0,X1)=X1), inference(spm,[status(thm)],[c_0_21, c_0_19])).
% 1.37/1.61  cnf(c_0_27, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 1.37/1.61  cnf(c_0_28, negated_conjecture, (r1_xboole_0(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 1.37/1.61  fof(c_0_29, plain, ![X10, X11, X13, X14, X15]:((r1_xboole_0(X10,X11)|r2_hidden(esk1_2(X10,X11),k3_xboole_0(X10,X11)))&(~r2_hidden(X15,k3_xboole_0(X13,X14))|~r1_xboole_0(X13,X14))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 1.37/1.61  cnf(c_0_30, plain, (r1_xboole_0(X1,X2)|k3_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_15])).
% 1.37/1.61  cnf(c_0_31, plain, (k4_xboole_0(X1,k1_xboole_0)=X1|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_26])).
% 1.37/1.61  cnf(c_0_32, negated_conjecture, (r1_xboole_0(esk4_0,esk3_0)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 1.37/1.61  cnf(c_0_33, plain, (k4_xboole_0(X1,X2)=X1|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_21])).
% 1.37/1.61  cnf(c_0_34, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 1.37/1.61  fof(c_0_35, plain, ![X19, X20, X21]:k4_xboole_0(k4_xboole_0(X19,X20),X21)=k4_xboole_0(X19,k2_xboole_0(X20,X21)), inference(variable_rename,[status(thm)],[t41_xboole_1])).
% 1.37/1.61  cnf(c_0_36, plain, (r1_xboole_0(X1,X2)|k4_xboole_0(X1,k4_xboole_0(X1,X2))!=k1_xboole_0), inference(rw,[status(thm)],[c_0_30, c_0_13])).
% 1.37/1.61  cnf(c_0_37, negated_conjecture, (k4_xboole_0(esk4_0,k1_xboole_0)=esk4_0), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 1.37/1.61  cnf(c_0_38, plain, (k4_xboole_0(X1,X1)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_25, c_0_33])).
% 1.37/1.61  cnf(c_0_39, plain, (~r1_xboole_0(X2,X3)|~r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))), inference(rw,[status(thm)],[c_0_34, c_0_13])).
% 1.37/1.61  cnf(c_0_40, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 1.37/1.61  fof(c_0_41, plain, ![X16, X17]:(~r1_tarski(X16,X17)|k2_xboole_0(X16,X17)=X17), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 1.37/1.61  cnf(c_0_42, negated_conjecture, (r1_xboole_0(esk4_0,k1_xboole_0)|k4_xboole_0(esk4_0,esk4_0)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 1.37/1.61  cnf(c_0_43, negated_conjecture, (k4_xboole_0(esk4_0,esk4_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_38, c_0_32])).
% 1.37/1.61  cnf(c_0_44, plain, (~r2_hidden(X1,k4_xboole_0(X2,k2_xboole_0(X3,k4_xboole_0(X2,k2_xboole_0(X3,X4)))))|~r1_xboole_0(k4_xboole_0(X2,X3),X4)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_40])).
% 1.37/1.61  cnf(c_0_45, negated_conjecture, (k4_xboole_0(esk3_0,esk3_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_38, c_0_28])).
% 1.37/1.61  cnf(c_0_46, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 1.37/1.61  cnf(c_0_47, negated_conjecture, (r1_xboole_0(esk4_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_42, c_0_43])])).
% 1.37/1.61  cnf(c_0_48, plain, (~r2_hidden(X1,k4_xboole_0(X2,k2_xboole_0(X3,k4_xboole_0(X2,X3))))|~r1_xboole_0(k4_xboole_0(X2,X3),k1_xboole_0)), inference(spm,[status(thm)],[c_0_44, c_0_21])).
% 1.37/1.61  cnf(c_0_49, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk1_2(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 1.37/1.61  cnf(c_0_50, negated_conjecture, (k4_xboole_0(esk3_0,k2_xboole_0(esk3_0,X1))=k4_xboole_0(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_40, c_0_45])).
% 1.37/1.61  cnf(c_0_51, plain, (k2_xboole_0(X1,X2)=X1|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_46, c_0_19])).
% 1.37/1.61  cnf(c_0_52, negated_conjecture, (r1_xboole_0(k1_xboole_0,esk4_0)), inference(spm,[status(thm)],[c_0_27, c_0_47])).
% 1.37/1.61  cnf(c_0_53, plain, (~r2_hidden(X1,k4_xboole_0(X2,X2))|~r1_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X3)),k1_xboole_0)), inference(spm,[status(thm)],[c_0_48, c_0_24])).
% 1.37/1.61  cnf(c_0_54, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk1_2(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))), inference(rw,[status(thm)],[c_0_49, c_0_13])).
% 1.37/1.61  cnf(c_0_55, negated_conjecture, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0|~r1_tarski(X1,esk3_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_45])).
% 1.37/1.61  cnf(c_0_56, negated_conjecture, (k4_xboole_0(k1_xboole_0,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_31, c_0_52])).
% 1.37/1.61  cnf(c_0_57, negated_conjecture, (~r2_hidden(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_43]), c_0_43]), c_0_37]), c_0_47])])).
% 1.37/1.61  cnf(c_0_58, negated_conjecture, (r1_xboole_0(k1_xboole_0,X1)|~r1_tarski(X1,esk3_0)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_56]), c_0_57])).
% 1.37/1.61  cnf(c_0_59, negated_conjecture, (r1_tarski(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 1.37/1.61  cnf(c_0_60, negated_conjecture, (r1_xboole_0(k1_xboole_0,esk2_0)), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 1.37/1.61  cnf(c_0_61, negated_conjecture, (r1_xboole_0(esk2_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_27, c_0_60])).
% 1.37/1.61  cnf(c_0_62, negated_conjecture, (k4_xboole_0(esk2_0,esk2_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_38, c_0_61])).
% 1.37/1.61  cnf(c_0_63, negated_conjecture, (k4_xboole_0(esk2_0,k2_xboole_0(esk2_0,X1))=k4_xboole_0(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_40, c_0_62])).
% 1.37/1.61  cnf(c_0_64, plain, (k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,k2_xboole_0(X2,X3))))=k1_xboole_0|~r1_xboole_0(k4_xboole_0(X1,X2),X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_40]), c_0_40])).
% 1.37/1.61  cnf(c_0_65, negated_conjecture, (k4_xboole_0(esk2_0,k2_xboole_0(X1,esk2_0))=k4_xboole_0(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_63, c_0_19])).
% 1.37/1.61  cnf(c_0_66, negated_conjecture, (k4_xboole_0(esk2_0,k2_xboole_0(X1,k4_xboole_0(k1_xboole_0,X1)))=k1_xboole_0|~r1_xboole_0(k4_xboole_0(esk2_0,X1),esk2_0)), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 1.37/1.61  cnf(c_0_67, plain, (r1_xboole_0(k4_xboole_0(X1,X2),X3)|k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,k2_xboole_0(X2,X3))))!=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_40]), c_0_40])).
% 1.37/1.61  cnf(c_0_68, negated_conjecture, (k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,esk2_0))=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_66]), c_0_62]), c_0_60])])).
% 1.37/1.61  cnf(c_0_69, plain, (r1_xboole_0(k4_xboole_0(X1,X2),X3)|k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,k2_xboole_0(X3,X2))))!=k1_xboole_0), inference(spm,[status(thm)],[c_0_67, c_0_19])).
% 1.37/1.61  cnf(c_0_70, plain, (k2_xboole_0(k4_xboole_0(X1,k2_xboole_0(X2,X3)),k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,k2_xboole_0(X2,X3)))))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_40]), c_0_40])).
% 1.37/1.61  cnf(c_0_71, negated_conjecture, (k4_xboole_0(k1_xboole_0,esk2_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_68]), c_0_21])).
% 1.37/1.61  cnf(c_0_72, plain, (~r2_hidden(X1,k4_xboole_0(X2,k2_xboole_0(X3,X2)))|~r1_xboole_0(X2,k1_xboole_0)|~r1_xboole_0(X2,X3)), inference(spm,[status(thm)],[c_0_48, c_0_33])).
% 1.37/1.61  cnf(c_0_73, plain, (r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(X2,X3))),X2)|k4_xboole_0(X1,k4_xboole_0(X1,X2))!=k1_xboole_0), inference(spm,[status(thm)],[c_0_69, c_0_70])).
% 1.37/1.61  cnf(c_0_74, negated_conjecture, (k4_xboole_0(k1_xboole_0,k2_xboole_0(esk2_0,X1))=k4_xboole_0(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_40, c_0_71])).
% 1.37/1.61  cnf(c_0_75, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_26]), c_0_26]), c_0_24])).
% 1.37/1.61  cnf(c_0_76, negated_conjecture, (r1_xboole_0(k1_xboole_0,k1_xboole_0)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_56]), c_0_56]), c_0_57])).
% 1.37/1.61  cnf(c_0_77, negated_conjecture, (~r2_hidden(X1,k4_xboole_0(k1_xboole_0,X2))|~r1_xboole_0(esk2_0,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_65]), c_0_61])])).
% 1.37/1.61  cnf(c_0_78, negated_conjecture, (r1_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1)),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_71]), c_0_75])])).
% 1.37/1.61  cnf(c_0_79, plain, (~r2_hidden(X1,k4_xboole_0(k1_xboole_0,X2))|~r1_xboole_0(k1_xboole_0,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_21]), c_0_76])])).
% 1.37/1.61  cnf(c_0_80, negated_conjecture, (r1_xboole_0(k1_xboole_0,X1)|~r1_xboole_0(esk2_0,k4_xboole_0(k1_xboole_0,X1))), inference(spm,[status(thm)],[c_0_77, c_0_54])).
% 1.37/1.61  cnf(c_0_81, negated_conjecture, (r1_xboole_0(esk2_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1)))), inference(spm,[status(thm)],[c_0_27, c_0_78])).
% 1.37/1.61  cnf(c_0_82, plain, (k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X2),X3))=k4_xboole_0(k1_xboole_0,X3)|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_40, c_0_25])).
% 1.37/1.61  cnf(c_0_83, plain, (r1_xboole_0(k1_xboole_0,X1)|~r1_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))), inference(spm,[status(thm)],[c_0_79, c_0_54])).
% 1.37/1.61  cnf(c_0_84, negated_conjecture, (r1_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))), inference(spm,[status(thm)],[c_0_80, c_0_81])).
% 1.37/1.61  cnf(c_0_85, plain, (k4_xboole_0(k1_xboole_0,X1)=X2|~r1_xboole_0(X2,k2_xboole_0(k4_xboole_0(X2,X3),X1))|~r1_xboole_0(X2,X3)), inference(spm,[status(thm)],[c_0_33, c_0_82])).
% 1.37/1.61  cnf(c_0_86, plain, (r1_xboole_0(k1_xboole_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_83, c_0_84])])).
% 1.37/1.61  cnf(c_0_87, plain, (k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,X3)))=k4_xboole_0(k1_xboole_0,X2)|~r1_xboole_0(X1,X3)), inference(spm,[status(thm)],[c_0_82, c_0_19])).
% 1.37/1.61  cnf(c_0_88, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_86]), c_0_86])])).
% 1.37/1.61  cnf(c_0_89, plain, (r1_xboole_0(k4_xboole_0(X1,X2),X3)|k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,X2)))!=k1_xboole_0|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_67, c_0_51])).
% 1.37/1.61  cnf(c_0_90, plain, (k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,X3)))=k1_xboole_0|~r1_xboole_0(X1,X3)), inference(rw,[status(thm)],[c_0_87, c_0_88])).
% 1.37/1.61  cnf(c_0_91, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_27, c_0_86])).
% 1.37/1.61  cnf(c_0_92, plain, (r1_xboole_0(X1,X2)|k4_xboole_0(X1,k2_xboole_0(X3,X1))!=k1_xboole_0|~r1_tarski(X2,X3)|~r1_xboole_0(X1,X3)), inference(spm,[status(thm)],[c_0_89, c_0_33])).
% 1.37/1.61  cnf(c_0_93, plain, (k4_xboole_0(X1,k2_xboole_0(X2,X1))=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_75]), c_0_91])])).
% 1.37/1.61  cnf(c_0_94, plain, (r1_xboole_0(X1,X2)|~r1_tarski(X2,X3)|~r1_xboole_0(X1,X3)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_92, c_0_93])])).
% 1.37/1.61  cnf(c_0_95, negated_conjecture, (r1_xboole_0(X1,esk2_0)|~r1_xboole_0(X1,esk3_0)), inference(spm,[status(thm)],[c_0_94, c_0_59])).
% 1.37/1.61  cnf(c_0_96, negated_conjecture, (r1_xboole_0(esk2_0,X1)|~r1_xboole_0(X1,esk3_0)), inference(spm,[status(thm)],[c_0_27, c_0_95])).
% 1.37/1.61  cnf(c_0_97, negated_conjecture, (~r1_xboole_0(esk2_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 1.37/1.61  cnf(c_0_98, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_32]), c_0_97]), ['proof']).
% 1.37/1.61  # SZS output end CNFRefutation
% 1.37/1.61  # Proof object total steps             : 99
% 1.37/1.61  # Proof object clause steps            : 78
% 1.37/1.61  # Proof object formula steps           : 21
% 1.37/1.61  # Proof object conjectures             : 36
% 1.37/1.61  # Proof object clause conjectures      : 33
% 1.37/1.61  # Proof object formula conjectures     : 3
% 1.37/1.61  # Proof object initial clauses used    : 14
% 1.37/1.61  # Proof object initial formulas used   : 10
% 1.37/1.61  # Proof object generating inferences   : 54
% 1.37/1.61  # Proof object simplifying inferences  : 46
% 1.37/1.61  # Training examples: 0 positive, 0 negative
% 1.37/1.61  # Parsed axioms                        : 10
% 1.37/1.61  # Removed by relevancy pruning/SinE    : 0
% 1.37/1.61  # Initial clauses                      : 14
% 1.37/1.61  # Removed in clause preprocessing      : 1
% 1.37/1.61  # Initial clauses in saturation        : 13
% 1.37/1.61  # Processed clauses                    : 17904
% 1.37/1.61  # ...of these trivial                  : 155
% 1.37/1.61  # ...subsumed                          : 16000
% 1.37/1.61  # ...remaining for further processing  : 1749
% 1.37/1.61  # Other redundant clauses eliminated   : 0
% 1.37/1.61  # Clauses deleted for lack of memory   : 0
% 1.37/1.61  # Backward-subsumed                    : 457
% 1.37/1.61  # Backward-rewritten                   : 734
% 1.37/1.61  # Generated clauses                    : 163175
% 1.37/1.61  # ...of the previous two non-trivial   : 150424
% 1.37/1.61  # Contextual simplify-reflections      : 53
% 1.37/1.61  # Paramodulations                      : 163170
% 1.37/1.61  # Factorizations                       : 0
% 1.37/1.61  # Equation resolutions                 : 0
% 1.37/1.61  # Propositional unsat checks           : 0
% 1.37/1.61  #    Propositional check models        : 0
% 1.37/1.61  #    Propositional check unsatisfiable : 0
% 1.37/1.61  #    Propositional clauses             : 0
% 1.37/1.61  #    Propositional clauses after purity: 0
% 1.37/1.61  #    Propositional unsat core size     : 0
% 1.37/1.61  #    Propositional preprocessing time  : 0.000
% 1.37/1.61  #    Propositional encoding time       : 0.000
% 1.37/1.61  #    Propositional solver time         : 0.000
% 1.37/1.61  #    Success case prop preproc time    : 0.000
% 1.37/1.61  #    Success case prop encoding time   : 0.000
% 1.37/1.61  #    Success case prop solver time     : 0.000
% 1.37/1.61  # Current number of processed clauses  : 540
% 1.37/1.61  #    Positive orientable unit clauses  : 34
% 1.37/1.61  #    Positive unorientable unit clauses: 3
% 1.37/1.61  #    Negative unit clauses             : 36
% 1.37/1.61  #    Non-unit-clauses                  : 467
% 1.37/1.61  # Current number of unprocessed clauses: 131396
% 1.37/1.61  # ...number of literals in the above   : 464416
% 1.37/1.61  # Current number of archived formulas  : 0
% 1.37/1.61  # Current number of archived clauses   : 1210
% 1.37/1.61  # Clause-clause subsumption calls (NU) : 221043
% 1.37/1.61  # Rec. Clause-clause subsumption calls : 87200
% 1.37/1.61  # Non-unit clause-clause subsumptions  : 4645
% 1.37/1.61  # Unit Clause-clause subsumption calls : 10778
% 1.37/1.61  # Rewrite failures with RHS unbound    : 0
% 1.37/1.61  # BW rewrite match attempts            : 889
% 1.37/1.61  # BW rewrite match successes           : 228
% 1.37/1.61  # Condensation attempts                : 0
% 1.37/1.61  # Condensation successes               : 0
% 1.37/1.61  # Termbank termtop insertions          : 2724787
% 1.45/1.61  
% 1.45/1.61  # -------------------------------------------------
% 1.45/1.61  # User time                : 1.225 s
% 1.45/1.61  # System time              : 0.067 s
% 1.45/1.61  # Total time               : 1.292 s
% 1.45/1.61  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
