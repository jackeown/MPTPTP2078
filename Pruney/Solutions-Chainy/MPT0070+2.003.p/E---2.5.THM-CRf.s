%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:32:36 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   89 (1633 expanded)
%              Number of clauses        :   66 ( 750 expanded)
%              Number of leaves         :   11 ( 425 expanded)
%              Depth                    :   21
%              Number of atoms          :  118 (2058 expanded)
%              Number of equality atoms :   77 (1525 expanded)
%              Maximal formula depth    :    7 (   2 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t51_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(t63_xboole_1,conjecture,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_xboole_0(X2,X3) )
     => r1_xboole_0(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(c_0_11,plain,(
    ! [X22,X23] : k2_xboole_0(k3_xboole_0(X22,X23),k4_xboole_0(X22,X23)) = X22 ),
    inference(variable_rename,[status(thm)],[t51_xboole_1])).

fof(c_0_12,plain,(
    ! [X20,X21] : k4_xboole_0(X20,k4_xboole_0(X20,X21)) = k3_xboole_0(X20,X21) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_13,plain,(
    ! [X8,X9] :
      ( ( ~ r1_xboole_0(X8,X9)
        | k3_xboole_0(X8,X9) = k1_xboole_0 )
      & ( k3_xboole_0(X8,X9) != k1_xboole_0
        | r1_xboole_0(X8,X9) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( r1_tarski(X1,X2)
          & r1_xboole_0(X2,X3) )
       => r1_xboole_0(X1,X3) ) ),
    inference(assume_negation,[status(cth)],[t63_xboole_1])).

cnf(c_0_15,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_17,plain,(
    ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_18,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_19,negated_conjecture,
    ( r1_tarski(esk1_0,esk2_0)
    & r1_xboole_0(esk2_0,esk3_0)
    & ~ r1_xboole_0(esk1_0,esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).

fof(c_0_20,plain,(
    ! [X10,X11] :
      ( ~ r1_xboole_0(X10,X11)
      | r1_xboole_0(X11,X10) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

cnf(c_0_21,plain,
    ( k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,X2)) = X1 ),
    inference(rw,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_22,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_18,c_0_16])).

cnf(c_0_24,negated_conjecture,
    ( r1_xboole_0(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_25,plain,(
    ! [X16] : k2_xboole_0(X16,k1_xboole_0) = X16 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

cnf(c_0_26,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))) = X1 ),
    inference(rw,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_28,negated_conjecture,
    ( k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_29,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_30,plain,(
    ! [X17,X18,X19] : k4_xboole_0(k4_xboole_0(X17,X18),X19) = k4_xboole_0(X17,k2_xboole_0(X18,X19)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

fof(c_0_31,plain,(
    ! [X12,X13] :
      ( ( k4_xboole_0(X12,X13) != k1_xboole_0
        | r1_tarski(X12,X13) )
      & ( ~ r1_tarski(X12,X13)
        | k4_xboole_0(X12,X13) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

fof(c_0_32,plain,(
    ! [X6,X7] : k3_xboole_0(X6,X7) = k3_xboole_0(X7,X6) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_33,negated_conjecture,
    ( r1_xboole_0(esk3_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_24])).

cnf(c_0_34,negated_conjecture,
    ( k4_xboole_0(esk2_0,esk3_0) = esk2_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29])).

cnf(c_0_35,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_36,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_37,negated_conjecture,
    ( r1_tarski(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_38,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_39,negated_conjecture,
    ( k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk2_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_23,c_0_33])).

cnf(c_0_40,plain,
    ( k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_29,c_0_22])).

cnf(c_0_41,negated_conjecture,
    ( k4_xboole_0(esk2_0,esk2_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_28,c_0_34])).

cnf(c_0_42,negated_conjecture,
    ( k4_xboole_0(esk2_0,k2_xboole_0(esk3_0,X1)) = k4_xboole_0(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_34])).

cnf(c_0_43,negated_conjecture,
    ( k4_xboole_0(esk1_0,esk2_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_44,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X2,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_16]),c_0_16])).

cnf(c_0_45,negated_conjecture,
    ( k4_xboole_0(esk3_0,k1_xboole_0) = esk3_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_39]),c_0_40])).

cnf(c_0_46,negated_conjecture,
    ( k4_xboole_0(esk2_0,k2_xboole_0(esk2_0,X1)) = k4_xboole_0(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_41])).

cnf(c_0_47,negated_conjecture,
    ( k4_xboole_0(esk2_0,k2_xboole_0(X1,esk3_0)) = k4_xboole_0(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_42,c_0_22])).

cnf(c_0_48,negated_conjecture,
    ( k4_xboole_0(esk1_0,k2_xboole_0(esk2_0,X1)) = k4_xboole_0(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_43])).

cnf(c_0_49,negated_conjecture,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,esk3_0)) = k4_xboole_0(esk3_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_50,negated_conjecture,
    ( k4_xboole_0(k1_xboole_0,esk3_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_41])).

cnf(c_0_51,negated_conjecture,
    ( k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_29]),c_0_43])).

cnf(c_0_52,negated_conjecture,
    ( k4_xboole_0(esk3_0,esk3_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_50]),c_0_51])).

fof(c_0_53,plain,(
    ! [X14,X15] :
      ( ~ r1_tarski(X14,X15)
      | k2_xboole_0(X14,X15) = X15 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_54,plain,
    ( r1_tarski(X1,X2)
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_55,negated_conjecture,
    ( k4_xboole_0(esk3_0,k2_xboole_0(esk3_0,X1)) = k4_xboole_0(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_52])).

cnf(c_0_56,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_57,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | k4_xboole_0(X1,k2_xboole_0(X2,X3)) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_54,c_0_35])).

cnf(c_0_58,negated_conjecture,
    ( k4_xboole_0(esk3_0,k2_xboole_0(X1,esk3_0)) = k4_xboole_0(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_55,c_0_22])).

cnf(c_0_59,negated_conjecture,
    ( k4_xboole_0(esk1_0,k2_xboole_0(X1,esk2_0)) = k4_xboole_0(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_48,c_0_22])).

cnf(c_0_60,negated_conjecture,
    ( k2_xboole_0(esk1_0,esk2_0) = esk2_0 ),
    inference(spm,[status(thm)],[c_0_56,c_0_37])).

cnf(c_0_61,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk3_0,X1),esk3_0)
    | k4_xboole_0(k1_xboole_0,X1) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_62,negated_conjecture,
    ( k4_xboole_0(k1_xboole_0,esk1_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_43])).

cnf(c_0_63,plain,
    ( k2_xboole_0(k4_xboole_0(X1,k2_xboole_0(X2,X3)),k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,k2_xboole_0(X2,X3))))) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_35]),c_0_35])).

cnf(c_0_64,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk3_0,esk1_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_65,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_40]),c_0_40]),c_0_27])).

cnf(c_0_66,negated_conjecture,
    ( k4_xboole_0(k1_xboole_0,k2_xboole_0(esk3_0,X1)) = k4_xboole_0(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_50])).

cnf(c_0_67,negated_conjecture,
    ( k2_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk1_0)) = esk3_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_64]),c_0_22])).

cnf(c_0_68,plain,
    ( k4_xboole_0(X1,X1) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_65])).

cnf(c_0_69,negated_conjecture,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(esk3_0,esk1_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_50])).

cnf(c_0_70,plain,
    ( k4_xboole_0(k1_xboole_0,k2_xboole_0(X1,k4_xboole_0(k1_xboole_0,X1))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_68]),c_0_35])).

cnf(c_0_71,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X1),k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,X1))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_27,c_0_68])).

cnf(c_0_72,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X1,X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_27,c_0_65])).

cnf(c_0_73,plain,
    ( r1_xboole_0(X1,X2)
    | k3_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_74,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk3_0)),esk3_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_69]),c_0_44])).

cnf(c_0_75,plain,
    ( k2_xboole_0(k4_xboole_0(k1_xboole_0,X1),k4_xboole_0(X1,X1)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_27,c_0_68])).

cnf(c_0_76,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,X1)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_65]),c_0_35]),c_0_72])).

cnf(c_0_77,plain,
    ( r1_xboole_0(X1,X2)
    | k4_xboole_0(X1,k4_xboole_0(X1,X2)) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_73,c_0_16])).

cnf(c_0_78,negated_conjecture,
    ( k2_xboole_0(esk3_0,k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk3_0))) = esk3_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_74]),c_0_22])).

cnf(c_0_79,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X1),k4_xboole_0(k1_xboole_0,X1)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_22,c_0_75])).

cnf(c_0_80,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_71,c_0_76]),c_0_29])).

cnf(c_0_81,plain,
    ( r1_xboole_0(X1,X2)
    | k4_xboole_0(X2,k4_xboole_0(X2,X1)) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_77,c_0_44])).

cnf(c_0_82,negated_conjecture,
    ( k4_xboole_0(esk2_0,k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk3_0))) = esk2_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_78]),c_0_34])).

cnf(c_0_83,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_79,c_0_80]),c_0_40])).

cnf(c_0_84,negated_conjecture,
    ( r1_xboole_0(k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk3_0)),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_82]),c_0_80])])).

cnf(c_0_85,negated_conjecture,
    ( k4_xboole_0(esk1_0,k2_xboole_0(X1,esk2_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_59,c_0_83])).

cnf(c_0_86,negated_conjecture,
    ( k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk3_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_84]),c_0_35]),c_0_85]),c_0_35]),c_0_29])).

cnf(c_0_87,negated_conjecture,
    ( ~ r1_xboole_0(esk1_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_88,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_86]),c_0_87]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 16:46:38 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.44  # AutoSched0-Mode selected heuristic G_____Y1346__C12_02_nc_F1_AE_CS_SP_S2S
% 0.19/0.44  # and selection function SelectNewComplexAHP.
% 0.19/0.44  #
% 0.19/0.44  # Preprocessing time       : 0.041 s
% 0.19/0.44  # Presaturation interreduction done
% 0.19/0.44  
% 0.19/0.44  # Proof found!
% 0.19/0.44  # SZS status Theorem
% 0.19/0.44  # SZS output start CNFRefutation
% 0.19/0.44  fof(t51_xboole_1, axiom, ![X1, X2]:k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 0.19/0.44  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.19/0.44  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 0.19/0.44  fof(t63_xboole_1, conjecture, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_xboole_0(X2,X3))=>r1_xboole_0(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 0.19/0.44  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.19/0.44  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 0.19/0.44  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 0.19/0.44  fof(t41_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 0.19/0.44  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.19/0.44  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.19/0.44  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.19/0.44  fof(c_0_11, plain, ![X22, X23]:k2_xboole_0(k3_xboole_0(X22,X23),k4_xboole_0(X22,X23))=X22, inference(variable_rename,[status(thm)],[t51_xboole_1])).
% 0.19/0.44  fof(c_0_12, plain, ![X20, X21]:k4_xboole_0(X20,k4_xboole_0(X20,X21))=k3_xboole_0(X20,X21), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.19/0.44  fof(c_0_13, plain, ![X8, X9]:((~r1_xboole_0(X8,X9)|k3_xboole_0(X8,X9)=k1_xboole_0)&(k3_xboole_0(X8,X9)!=k1_xboole_0|r1_xboole_0(X8,X9))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 0.19/0.44  fof(c_0_14, negated_conjecture, ~(![X1, X2, X3]:((r1_tarski(X1,X2)&r1_xboole_0(X2,X3))=>r1_xboole_0(X1,X3))), inference(assume_negation,[status(cth)],[t63_xboole_1])).
% 0.19/0.44  cnf(c_0_15, plain, (k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.44  cnf(c_0_16, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.44  fof(c_0_17, plain, ![X4, X5]:k2_xboole_0(X4,X5)=k2_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.19/0.44  cnf(c_0_18, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.44  fof(c_0_19, negated_conjecture, ((r1_tarski(esk1_0,esk2_0)&r1_xboole_0(esk2_0,esk3_0))&~r1_xboole_0(esk1_0,esk3_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).
% 0.19/0.44  fof(c_0_20, plain, ![X10, X11]:(~r1_xboole_0(X10,X11)|r1_xboole_0(X11,X10)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 0.19/0.44  cnf(c_0_21, plain, (k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,X2))=X1), inference(rw,[status(thm)],[c_0_15, c_0_16])).
% 0.19/0.44  cnf(c_0_22, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.44  cnf(c_0_23, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_18, c_0_16])).
% 0.19/0.44  cnf(c_0_24, negated_conjecture, (r1_xboole_0(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.44  fof(c_0_25, plain, ![X16]:k2_xboole_0(X16,k1_xboole_0)=X16, inference(variable_rename,[status(thm)],[t1_boole])).
% 0.19/0.44  cnf(c_0_26, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.44  cnf(c_0_27, plain, (k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))=X1), inference(rw,[status(thm)],[c_0_21, c_0_22])).
% 0.19/0.44  cnf(c_0_28, negated_conjecture, (k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.19/0.44  cnf(c_0_29, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.44  fof(c_0_30, plain, ![X17, X18, X19]:k4_xboole_0(k4_xboole_0(X17,X18),X19)=k4_xboole_0(X17,k2_xboole_0(X18,X19)), inference(variable_rename,[status(thm)],[t41_xboole_1])).
% 0.19/0.44  fof(c_0_31, plain, ![X12, X13]:((k4_xboole_0(X12,X13)!=k1_xboole_0|r1_tarski(X12,X13))&(~r1_tarski(X12,X13)|k4_xboole_0(X12,X13)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.19/0.44  fof(c_0_32, plain, ![X6, X7]:k3_xboole_0(X6,X7)=k3_xboole_0(X7,X6), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.19/0.44  cnf(c_0_33, negated_conjecture, (r1_xboole_0(esk3_0,esk2_0)), inference(spm,[status(thm)],[c_0_26, c_0_24])).
% 0.19/0.44  cnf(c_0_34, negated_conjecture, (k4_xboole_0(esk2_0,esk3_0)=esk2_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_29])).
% 0.19/0.44  cnf(c_0_35, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.44  cnf(c_0_36, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.44  cnf(c_0_37, negated_conjecture, (r1_tarski(esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.44  cnf(c_0_38, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.44  cnf(c_0_39, negated_conjecture, (k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk2_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_23, c_0_33])).
% 0.19/0.44  cnf(c_0_40, plain, (k2_xboole_0(k1_xboole_0,X1)=X1), inference(spm,[status(thm)],[c_0_29, c_0_22])).
% 0.19/0.44  cnf(c_0_41, negated_conjecture, (k4_xboole_0(esk2_0,esk2_0)=k1_xboole_0), inference(rw,[status(thm)],[c_0_28, c_0_34])).
% 0.19/0.44  cnf(c_0_42, negated_conjecture, (k4_xboole_0(esk2_0,k2_xboole_0(esk3_0,X1))=k4_xboole_0(esk2_0,X1)), inference(spm,[status(thm)],[c_0_35, c_0_34])).
% 0.19/0.44  cnf(c_0_43, negated_conjecture, (k4_xboole_0(esk1_0,esk2_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.19/0.44  cnf(c_0_44, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k4_xboole_0(X2,k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_16]), c_0_16])).
% 0.19/0.44  cnf(c_0_45, negated_conjecture, (k4_xboole_0(esk3_0,k1_xboole_0)=esk3_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_39]), c_0_40])).
% 0.19/0.44  cnf(c_0_46, negated_conjecture, (k4_xboole_0(esk2_0,k2_xboole_0(esk2_0,X1))=k4_xboole_0(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_35, c_0_41])).
% 0.19/0.44  cnf(c_0_47, negated_conjecture, (k4_xboole_0(esk2_0,k2_xboole_0(X1,esk3_0))=k4_xboole_0(esk2_0,X1)), inference(spm,[status(thm)],[c_0_42, c_0_22])).
% 0.19/0.44  cnf(c_0_48, negated_conjecture, (k4_xboole_0(esk1_0,k2_xboole_0(esk2_0,X1))=k4_xboole_0(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_35, c_0_43])).
% 0.19/0.44  cnf(c_0_49, negated_conjecture, (k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,esk3_0))=k4_xboole_0(esk3_0,esk3_0)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.19/0.44  cnf(c_0_50, negated_conjecture, (k4_xboole_0(k1_xboole_0,esk3_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_41])).
% 0.19/0.44  cnf(c_0_51, negated_conjecture, (k4_xboole_0(k1_xboole_0,k1_xboole_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_29]), c_0_43])).
% 0.19/0.44  cnf(c_0_52, negated_conjecture, (k4_xboole_0(esk3_0,esk3_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49, c_0_50]), c_0_51])).
% 0.19/0.44  fof(c_0_53, plain, ![X14, X15]:(~r1_tarski(X14,X15)|k2_xboole_0(X14,X15)=X15), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.19/0.44  cnf(c_0_54, plain, (r1_tarski(X1,X2)|k4_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.44  cnf(c_0_55, negated_conjecture, (k4_xboole_0(esk3_0,k2_xboole_0(esk3_0,X1))=k4_xboole_0(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_35, c_0_52])).
% 0.19/0.44  cnf(c_0_56, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.19/0.44  cnf(c_0_57, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|k4_xboole_0(X1,k2_xboole_0(X2,X3))!=k1_xboole_0), inference(spm,[status(thm)],[c_0_54, c_0_35])).
% 0.19/0.44  cnf(c_0_58, negated_conjecture, (k4_xboole_0(esk3_0,k2_xboole_0(X1,esk3_0))=k4_xboole_0(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_55, c_0_22])).
% 0.19/0.44  cnf(c_0_59, negated_conjecture, (k4_xboole_0(esk1_0,k2_xboole_0(X1,esk2_0))=k4_xboole_0(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_48, c_0_22])).
% 0.19/0.44  cnf(c_0_60, negated_conjecture, (k2_xboole_0(esk1_0,esk2_0)=esk2_0), inference(spm,[status(thm)],[c_0_56, c_0_37])).
% 0.19/0.44  cnf(c_0_61, negated_conjecture, (r1_tarski(k4_xboole_0(esk3_0,X1),esk3_0)|k4_xboole_0(k1_xboole_0,X1)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 0.19/0.44  cnf(c_0_62, negated_conjecture, (k4_xboole_0(k1_xboole_0,esk1_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_43])).
% 0.19/0.44  cnf(c_0_63, plain, (k2_xboole_0(k4_xboole_0(X1,k2_xboole_0(X2,X3)),k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,k2_xboole_0(X2,X3)))))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_35]), c_0_35])).
% 0.19/0.44  cnf(c_0_64, negated_conjecture, (r1_tarski(k4_xboole_0(esk3_0,esk1_0),esk3_0)), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 0.19/0.44  cnf(c_0_65, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_40]), c_0_40]), c_0_27])).
% 0.19/0.44  cnf(c_0_66, negated_conjecture, (k4_xboole_0(k1_xboole_0,k2_xboole_0(esk3_0,X1))=k4_xboole_0(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_35, c_0_50])).
% 0.19/0.44  cnf(c_0_67, negated_conjecture, (k2_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk1_0))=esk3_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_64]), c_0_22])).
% 0.19/0.44  cnf(c_0_68, plain, (k4_xboole_0(X1,X1)=k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))), inference(spm,[status(thm)],[c_0_44, c_0_65])).
% 0.19/0.44  cnf(c_0_69, negated_conjecture, (k4_xboole_0(k1_xboole_0,k4_xboole_0(esk3_0,esk1_0))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_50])).
% 0.19/0.44  cnf(c_0_70, plain, (k4_xboole_0(k1_xboole_0,k2_xboole_0(X1,k4_xboole_0(k1_xboole_0,X1)))=k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_68]), c_0_35])).
% 0.19/0.44  cnf(c_0_71, plain, (k2_xboole_0(k4_xboole_0(X1,X1),k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,X1)))=k1_xboole_0), inference(spm,[status(thm)],[c_0_27, c_0_68])).
% 0.19/0.44  cnf(c_0_72, plain, (k2_xboole_0(X1,k4_xboole_0(X1,X1))=X1), inference(spm,[status(thm)],[c_0_27, c_0_65])).
% 0.19/0.44  cnf(c_0_73, plain, (r1_xboole_0(X1,X2)|k3_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.44  cnf(c_0_74, negated_conjecture, (r1_tarski(k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk3_0)),esk3_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_69]), c_0_44])).
% 0.19/0.44  cnf(c_0_75, plain, (k2_xboole_0(k4_xboole_0(k1_xboole_0,X1),k4_xboole_0(X1,X1))=k1_xboole_0), inference(spm,[status(thm)],[c_0_27, c_0_68])).
% 0.19/0.44  cnf(c_0_76, plain, (k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,X1))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_71]), c_0_65]), c_0_35]), c_0_72])).
% 0.19/0.44  cnf(c_0_77, plain, (r1_xboole_0(X1,X2)|k4_xboole_0(X1,k4_xboole_0(X1,X2))!=k1_xboole_0), inference(rw,[status(thm)],[c_0_73, c_0_16])).
% 0.19/0.44  cnf(c_0_78, negated_conjecture, (k2_xboole_0(esk3_0,k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk3_0)))=esk3_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_74]), c_0_22])).
% 0.19/0.44  cnf(c_0_79, plain, (k2_xboole_0(k4_xboole_0(X1,X1),k4_xboole_0(k1_xboole_0,X1))=k1_xboole_0), inference(spm,[status(thm)],[c_0_22, c_0_75])).
% 0.19/0.44  cnf(c_0_80, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_71, c_0_76]), c_0_29])).
% 0.19/0.44  cnf(c_0_81, plain, (r1_xboole_0(X1,X2)|k4_xboole_0(X2,k4_xboole_0(X2,X1))!=k1_xboole_0), inference(spm,[status(thm)],[c_0_77, c_0_44])).
% 0.19/0.44  cnf(c_0_82, negated_conjecture, (k4_xboole_0(esk2_0,k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk3_0)))=esk2_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_78]), c_0_34])).
% 0.19/0.44  cnf(c_0_83, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_79, c_0_80]), c_0_40])).
% 0.19/0.44  cnf(c_0_84, negated_conjecture, (r1_xboole_0(k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk3_0)),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_82]), c_0_80])])).
% 0.19/0.44  cnf(c_0_85, negated_conjecture, (k4_xboole_0(esk1_0,k2_xboole_0(X1,esk2_0))=k1_xboole_0), inference(rw,[status(thm)],[c_0_59, c_0_83])).
% 0.19/0.44  cnf(c_0_86, negated_conjecture, (k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk3_0))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_84]), c_0_35]), c_0_85]), c_0_35]), c_0_29])).
% 0.19/0.44  cnf(c_0_87, negated_conjecture, (~r1_xboole_0(esk1_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.44  cnf(c_0_88, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_86]), c_0_87]), ['proof']).
% 0.19/0.44  # SZS output end CNFRefutation
% 0.19/0.44  # Proof object total steps             : 89
% 0.19/0.44  # Proof object clause steps            : 66
% 0.19/0.44  # Proof object formula steps           : 23
% 0.19/0.44  # Proof object conjectures             : 38
% 0.19/0.44  # Proof object clause conjectures      : 35
% 0.19/0.44  # Proof object formula conjectures     : 3
% 0.19/0.44  # Proof object initial clauses used    : 15
% 0.19/0.44  # Proof object initial formulas used   : 11
% 0.19/0.44  # Proof object generating inferences   : 41
% 0.19/0.44  # Proof object simplifying inferences  : 38
% 0.19/0.44  # Training examples: 0 positive, 0 negative
% 0.19/0.44  # Parsed axioms                        : 11
% 0.19/0.44  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.44  # Initial clauses                      : 15
% 0.19/0.44  # Removed in clause preprocessing      : 1
% 0.19/0.44  # Initial clauses in saturation        : 14
% 0.19/0.44  # Processed clauses                    : 434
% 0.19/0.44  # ...of these trivial                  : 109
% 0.19/0.44  # ...subsumed                          : 37
% 0.19/0.44  # ...remaining for further processing  : 288
% 0.19/0.44  # Other redundant clauses eliminated   : 0
% 0.19/0.44  # Clauses deleted for lack of memory   : 0
% 0.19/0.44  # Backward-subsumed                    : 6
% 0.19/0.44  # Backward-rewritten                   : 173
% 0.19/0.44  # Generated clauses                    : 3330
% 0.19/0.44  # ...of the previous two non-trivial   : 1898
% 0.19/0.44  # Contextual simplify-reflections      : 0
% 0.19/0.44  # Paramodulations                      : 3328
% 0.19/0.44  # Factorizations                       : 0
% 0.19/0.44  # Equation resolutions                 : 2
% 0.19/0.44  # Propositional unsat checks           : 0
% 0.19/0.44  #    Propositional check models        : 0
% 0.19/0.44  #    Propositional check unsatisfiable : 0
% 0.19/0.44  #    Propositional clauses             : 0
% 0.19/0.44  #    Propositional clauses after purity: 0
% 0.19/0.44  #    Propositional unsat core size     : 0
% 0.19/0.44  #    Propositional preprocessing time  : 0.000
% 0.19/0.44  #    Propositional encoding time       : 0.000
% 0.19/0.44  #    Propositional solver time         : 0.000
% 0.19/0.44  #    Success case prop preproc time    : 0.000
% 0.19/0.44  #    Success case prop encoding time   : 0.000
% 0.19/0.44  #    Success case prop solver time     : 0.000
% 0.19/0.44  # Current number of processed clauses  : 95
% 0.19/0.44  #    Positive orientable unit clauses  : 67
% 0.19/0.44  #    Positive unorientable unit clauses: 3
% 0.19/0.44  #    Negative unit clauses             : 1
% 0.19/0.44  #    Non-unit-clauses                  : 24
% 0.19/0.44  # Current number of unprocessed clauses: 1442
% 0.19/0.44  # ...number of literals in the above   : 2230
% 0.19/0.44  # Current number of archived formulas  : 0
% 0.19/0.44  # Current number of archived clauses   : 194
% 0.19/0.44  # Clause-clause subsumption calls (NU) : 139
% 0.19/0.44  # Rec. Clause-clause subsumption calls : 138
% 0.19/0.44  # Non-unit clause-clause subsumptions  : 42
% 0.19/0.44  # Unit Clause-clause subsumption calls : 64
% 0.19/0.44  # Rewrite failures with RHS unbound    : 0
% 0.19/0.44  # BW rewrite match attempts            : 562
% 0.19/0.44  # BW rewrite match successes           : 147
% 0.19/0.44  # Condensation attempts                : 0
% 0.19/0.44  # Condensation successes               : 0
% 0.19/0.44  # Termbank termtop insertions          : 33704
% 0.19/0.44  
% 0.19/0.44  # -------------------------------------------------
% 0.19/0.44  # User time                : 0.091 s
% 0.19/0.44  # System time              : 0.008 s
% 0.19/0.44  # Total time               : 0.100 s
% 0.19/0.44  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
