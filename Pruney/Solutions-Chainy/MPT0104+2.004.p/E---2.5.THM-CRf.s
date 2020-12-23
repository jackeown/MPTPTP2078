%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:34:07 EST 2020

% Result     : Theorem 0.59s
% Output     : CNFRefutation 0.59s
% Verified   : 
% Statistics : Number of formulae       :   86 (1489 expanded)
%              Number of clauses        :   65 ( 701 expanded)
%              Number of leaves         :   10 ( 392 expanded)
%              Depth                    :   16
%              Number of atoms          :  105 (2117 expanded)
%              Number of equality atoms :   57 (1190 expanded)
%              Maximal formula depth    :    7 (   2 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(t97_xboole_1,conjecture,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(k4_xboole_0(X1,X2),X3)
        & r1_tarski(k4_xboole_0(X2,X1),X3) )
     => r1_tarski(k5_xboole_0(X1,X2),X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_xboole_1)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(t44_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k4_xboole_0(X1,X2),X3)
     => r1_tarski(X1,k2_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

fof(d6_xboole_0,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).

fof(l98_xboole_1,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k4_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l98_xboole_1)).

fof(c_0_10,plain,(
    ! [X14,X15] : r1_tarski(k4_xboole_0(X14,X15),X14) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

fof(c_0_11,plain,(
    ! [X18] : k4_xboole_0(X18,k1_xboole_0) = X18 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

fof(c_0_12,plain,(
    ! [X6,X7] :
      ( ( k4_xboole_0(X6,X7) != k1_xboole_0
        | r1_tarski(X6,X7) )
      & ( ~ r1_tarski(X6,X7)
        | k4_xboole_0(X6,X7) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

cnf(c_0_13,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_17,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

fof(c_0_18,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( r1_tarski(k4_xboole_0(X1,X2),X3)
          & r1_tarski(k4_xboole_0(X2,X1),X3) )
       => r1_tarski(k5_xboole_0(X1,X2),X3) ) ),
    inference(assume_negation,[status(cth)],[t97_xboole_1])).

fof(c_0_19,plain,(
    ! [X16,X17] : k2_xboole_0(X16,k4_xboole_0(X17,X16)) = k2_xboole_0(X16,X17) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

fof(c_0_20,plain,(
    ! [X10,X11] :
      ( ~ r1_tarski(X10,X11)
      | k2_xboole_0(X10,X11) = X11 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

fof(c_0_21,plain,(
    ! [X19,X20,X21] : k4_xboole_0(k4_xboole_0(X19,X20),X21) = k4_xboole_0(X19,k2_xboole_0(X20,X21)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

cnf(c_0_22,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_13,c_0_17])).

fof(c_0_23,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk1_0,esk2_0),esk3_0)
    & r1_tarski(k4_xboole_0(esk2_0,esk1_0),esk3_0)
    & ~ r1_tarski(k5_xboole_0(esk1_0,esk2_0),esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).

cnf(c_0_24,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_15,c_0_22])).

cnf(c_0_28,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk2_0,esk1_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_29,plain,(
    ! [X22,X23,X24] :
      ( ~ r1_tarski(k4_xboole_0(X22,X23),X24)
      | r1_tarski(X22,k2_xboole_0(X23,X24)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_xboole_1])])).

cnf(c_0_30,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = k2_xboole_0(X1,X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_17])).

cnf(c_0_31,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_25,c_0_16])).

cnf(c_0_32,plain,
    ( r1_tarski(X1,X2)
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_33,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_17]),c_0_27])).

cnf(c_0_34,negated_conjecture,
    ( k4_xboole_0(esk2_0,k2_xboole_0(esk1_0,esk3_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_28]),c_0_26])).

cnf(c_0_35,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r1_tarski(k4_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_36,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,X1)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_13]),c_0_26])).

cnf(c_0_37,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X3,X1))) = k2_xboole_0(X1,k4_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_26])).

cnf(c_0_38,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_39,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_40,negated_conjecture,
    ( r1_tarski(esk2_0,k2_xboole_0(esk1_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_34])).

cnf(c_0_41,plain,
    ( r1_tarski(X1,k2_xboole_0(k2_xboole_0(X2,X1),X3)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_22])])).

cnf(c_0_42,negated_conjecture,
    ( k2_xboole_0(esk3_0,k4_xboole_0(esk2_0,esk1_0)) = esk3_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_34]),c_0_38])).

cnf(c_0_43,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_36])).

cnf(c_0_44,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_25,c_0_39])).

cnf(c_0_45,plain,
    ( r1_tarski(k4_xboole_0(X1,k2_xboole_0(X2,X3)),k4_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_13,c_0_26])).

cnf(c_0_46,negated_conjecture,
    ( k2_xboole_0(esk2_0,k2_xboole_0(esk1_0,esk3_0)) = k2_xboole_0(esk1_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_40])).

cnf(c_0_47,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk2_0,esk1_0),k2_xboole_0(esk3_0,X1)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_48,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X2,X1)) = k2_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_43])).

cnf(c_0_49,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X3,X1)) = k2_xboole_0(k2_xboole_0(X1,X2),X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_44]),c_0_24])).

cnf(c_0_50,plain,
    ( k4_xboole_0(X1,k2_xboole_0(k2_xboole_0(X2,X3),X4)) = k4_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X3,X4))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_26]),c_0_26]),c_0_26])).

cnf(c_0_51,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),k2_xboole_0(X3,X4))
    | ~ r1_tarski(k4_xboole_0(X1,k2_xboole_0(X2,X3)),X4) ),
    inference(spm,[status(thm)],[c_0_35,c_0_26])).

cnf(c_0_52,negated_conjecture,
    ( r1_tarski(k4_xboole_0(X1,k2_xboole_0(esk1_0,esk3_0)),k4_xboole_0(X1,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_53,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk1_0,esk2_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_54,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk2_0,esk1_0),k2_xboole_0(X1,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_55,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X3,X2)) = k2_xboole_0(k2_xboole_0(X1,X2),X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_48]),c_0_24])).

cnf(c_0_56,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),X1) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_17]),c_0_38])).

cnf(c_0_57,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,k2_xboole_0(X2,X3))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_33,c_0_50])).

cnf(c_0_58,negated_conjecture,
    ( r1_tarski(k4_xboole_0(X1,esk1_0),k2_xboole_0(esk3_0,k4_xboole_0(X1,esk2_0))) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_59,plain,
    ( k2_xboole_0(X1,k4_xboole_0(k2_xboole_0(X2,X1),X2)) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_17]),c_0_38])).

cnf(c_0_60,negated_conjecture,
    ( k4_xboole_0(esk1_0,k2_xboole_0(esk2_0,esk3_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_53]),c_0_26])).

cnf(c_0_61,negated_conjecture,
    ( k2_xboole_0(k4_xboole_0(esk2_0,esk1_0),k2_xboole_0(X1,esk3_0)) = k2_xboole_0(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_54])).

cnf(c_0_62,plain,
    ( k2_xboole_0(k2_xboole_0(k4_xboole_0(X1,X2),X2),X1) = k2_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_63,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X2,X1)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_57,c_0_48])).

cnf(c_0_64,plain,
    ( k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_25,c_0_22])).

cnf(c_0_65,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X2),k2_xboole_0(X2,X1)) = k2_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_48,c_0_24])).

cnf(c_0_66,negated_conjecture,
    ( r1_tarski(k4_xboole_0(k2_xboole_0(esk2_0,esk3_0),esk1_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_67,negated_conjecture,
    ( r1_tarski(esk1_0,k2_xboole_0(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_60])).

cnf(c_0_68,negated_conjecture,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(esk2_0,esk1_0),X1),k2_xboole_0(X1,esk3_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_57,c_0_61])).

cnf(c_0_69,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_64]),c_0_64])).

fof(c_0_70,plain,(
    ! [X4,X5] : k5_xboole_0(X4,X5) = k2_xboole_0(k4_xboole_0(X4,X5),k4_xboole_0(X5,X4)) ),
    inference(variable_rename,[status(thm)],[d6_xboole_0])).

fof(c_0_71,plain,(
    ! [X8,X9] : k5_xboole_0(X8,X9) = k4_xboole_0(k2_xboole_0(X8,X9),k3_xboole_0(X8,X9)) ),
    inference(variable_rename,[status(thm)],[l98_xboole_1])).

cnf(c_0_72,plain,
    ( k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X2,X3),X3)) = k4_xboole_0(X1,k2_xboole_0(X3,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_62]),c_0_65])).

cnf(c_0_73,negated_conjecture,
    ( k4_xboole_0(k2_xboole_0(esk2_0,esk3_0),k2_xboole_0(esk1_0,esk3_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_66]),c_0_26])).

cnf(c_0_74,negated_conjecture,
    ( k2_xboole_0(esk1_0,k2_xboole_0(esk2_0,esk3_0)) = k2_xboole_0(esk2_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_67])).

cnf(c_0_75,negated_conjecture,
    ( r1_tarski(k2_xboole_0(k4_xboole_0(esk2_0,esk1_0),X1),k2_xboole_0(X1,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_68])).

cnf(c_0_76,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_69]),c_0_69])).

cnf(c_0_77,plain,
    ( k5_xboole_0(X1,X2) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_78,plain,
    ( k5_xboole_0(X1,X2) = k4_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_79,negated_conjecture,
    ( k4_xboole_0(X1,k2_xboole_0(esk2_0,esk3_0)) = k4_xboole_0(X1,k2_xboole_0(esk1_0,esk3_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_64]),c_0_50]),c_0_48]),c_0_74])).

cnf(c_0_80,negated_conjecture,
    ( ~ r1_tarski(k5_xboole_0(esk1_0,esk2_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_81,negated_conjecture,
    ( r1_tarski(k2_xboole_0(X1,k4_xboole_0(esk2_0,esk1_0)),k2_xboole_0(X1,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_82,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) = k4_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[c_0_77,c_0_78])).

cnf(c_0_83,negated_conjecture,
    ( k2_xboole_0(esk3_0,k4_xboole_0(X1,esk2_0)) = k2_xboole_0(esk3_0,k4_xboole_0(X1,esk1_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_79]),c_0_37])).

cnf(c_0_84,negated_conjecture,
    ( ~ r1_tarski(k4_xboole_0(k2_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,esk2_0)),esk3_0) ),
    inference(rw,[status(thm)],[c_0_80,c_0_78])).

cnf(c_0_85,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_82]),c_0_76]),c_0_83]),c_0_17]),c_0_38]),c_0_84]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:22:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.59/0.75  # AutoSched0-Mode selected heuristic G_____Y1346__C12_02_nc_F1_AE_CS_SP_S2S
% 0.59/0.75  # and selection function SelectNewComplexAHP.
% 0.59/0.75  #
% 0.59/0.75  # Preprocessing time       : 0.027 s
% 0.59/0.75  # Presaturation interreduction done
% 0.59/0.75  
% 0.59/0.75  # Proof found!
% 0.59/0.75  # SZS status Theorem
% 0.59/0.75  # SZS output start CNFRefutation
% 0.59/0.75  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.59/0.75  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 0.59/0.75  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.59/0.75  fof(t97_xboole_1, conjecture, ![X1, X2, X3]:((r1_tarski(k4_xboole_0(X1,X2),X3)&r1_tarski(k4_xboole_0(X2,X1),X3))=>r1_tarski(k5_xboole_0(X1,X2),X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_xboole_1)).
% 0.59/0.75  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 0.59/0.75  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.59/0.75  fof(t41_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 0.59/0.75  fof(t44_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(k4_xboole_0(X1,X2),X3)=>r1_tarski(X1,k2_xboole_0(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_xboole_1)).
% 0.59/0.75  fof(d6_xboole_0, axiom, ![X1, X2]:k5_xboole_0(X1,X2)=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_xboole_0)).
% 0.59/0.75  fof(l98_xboole_1, axiom, ![X1, X2]:k5_xboole_0(X1,X2)=k4_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l98_xboole_1)).
% 0.59/0.75  fof(c_0_10, plain, ![X14, X15]:r1_tarski(k4_xboole_0(X14,X15),X14), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.59/0.75  fof(c_0_11, plain, ![X18]:k4_xboole_0(X18,k1_xboole_0)=X18, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.59/0.75  fof(c_0_12, plain, ![X6, X7]:((k4_xboole_0(X6,X7)!=k1_xboole_0|r1_tarski(X6,X7))&(~r1_tarski(X6,X7)|k4_xboole_0(X6,X7)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.59/0.75  cnf(c_0_13, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.59/0.75  cnf(c_0_14, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.59/0.75  cnf(c_0_15, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.59/0.75  cnf(c_0_16, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.59/0.75  cnf(c_0_17, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.59/0.75  fof(c_0_18, negated_conjecture, ~(![X1, X2, X3]:((r1_tarski(k4_xboole_0(X1,X2),X3)&r1_tarski(k4_xboole_0(X2,X1),X3))=>r1_tarski(k5_xboole_0(X1,X2),X3))), inference(assume_negation,[status(cth)],[t97_xboole_1])).
% 0.59/0.75  fof(c_0_19, plain, ![X16, X17]:k2_xboole_0(X16,k4_xboole_0(X17,X16))=k2_xboole_0(X16,X17), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 0.59/0.75  fof(c_0_20, plain, ![X10, X11]:(~r1_tarski(X10,X11)|k2_xboole_0(X10,X11)=X11), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.59/0.75  fof(c_0_21, plain, ![X19, X20, X21]:k4_xboole_0(k4_xboole_0(X19,X20),X21)=k4_xboole_0(X19,k2_xboole_0(X20,X21)), inference(variable_rename,[status(thm)],[t41_xboole_1])).
% 0.59/0.75  cnf(c_0_22, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_13, c_0_17])).
% 0.59/0.75  fof(c_0_23, negated_conjecture, ((r1_tarski(k4_xboole_0(esk1_0,esk2_0),esk3_0)&r1_tarski(k4_xboole_0(esk2_0,esk1_0),esk3_0))&~r1_tarski(k5_xboole_0(esk1_0,esk2_0),esk3_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).
% 0.59/0.75  cnf(c_0_24, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.59/0.75  cnf(c_0_25, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.59/0.75  cnf(c_0_26, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.59/0.75  cnf(c_0_27, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_15, c_0_22])).
% 0.59/0.75  cnf(c_0_28, negated_conjecture, (r1_tarski(k4_xboole_0(esk2_0,esk1_0),esk3_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.59/0.75  fof(c_0_29, plain, ![X22, X23, X24]:(~r1_tarski(k4_xboole_0(X22,X23),X24)|r1_tarski(X22,k2_xboole_0(X23,X24))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_xboole_1])])).
% 0.59/0.75  cnf(c_0_30, plain, (k2_xboole_0(X1,k1_xboole_0)=k2_xboole_0(X1,X1)), inference(spm,[status(thm)],[c_0_24, c_0_17])).
% 0.59/0.75  cnf(c_0_31, plain, (k2_xboole_0(X1,X1)=X1), inference(spm,[status(thm)],[c_0_25, c_0_16])).
% 0.59/0.75  cnf(c_0_32, plain, (r1_tarski(X1,X2)|k4_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.59/0.75  cnf(c_0_33, plain, (k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_17]), c_0_27])).
% 0.59/0.75  cnf(c_0_34, negated_conjecture, (k4_xboole_0(esk2_0,k2_xboole_0(esk1_0,esk3_0))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_28]), c_0_26])).
% 0.59/0.75  cnf(c_0_35, plain, (r1_tarski(X1,k2_xboole_0(X2,X3))|~r1_tarski(k4_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.59/0.75  cnf(c_0_36, plain, (k4_xboole_0(X1,k2_xboole_0(X2,X1))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_13]), c_0_26])).
% 0.59/0.75  cnf(c_0_37, plain, (k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X3,X1)))=k2_xboole_0(X1,k4_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_24, c_0_26])).
% 0.59/0.75  cnf(c_0_38, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[c_0_30, c_0_31])).
% 0.59/0.75  cnf(c_0_39, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.59/0.75  cnf(c_0_40, negated_conjecture, (r1_tarski(esk2_0,k2_xboole_0(esk1_0,esk3_0))), inference(spm,[status(thm)],[c_0_32, c_0_34])).
% 0.59/0.75  cnf(c_0_41, plain, (r1_tarski(X1,k2_xboole_0(k2_xboole_0(X2,X1),X3))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_22])])).
% 0.59/0.75  cnf(c_0_42, negated_conjecture, (k2_xboole_0(esk3_0,k4_xboole_0(esk2_0,esk1_0))=esk3_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_34]), c_0_38])).
% 0.59/0.75  cnf(c_0_43, plain, (r1_tarski(X1,k2_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_32, c_0_36])).
% 0.59/0.75  cnf(c_0_44, plain, (k2_xboole_0(X1,k2_xboole_0(X1,X2))=k2_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_25, c_0_39])).
% 0.59/0.75  cnf(c_0_45, plain, (r1_tarski(k4_xboole_0(X1,k2_xboole_0(X2,X3)),k4_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_13, c_0_26])).
% 0.59/0.75  cnf(c_0_46, negated_conjecture, (k2_xboole_0(esk2_0,k2_xboole_0(esk1_0,esk3_0))=k2_xboole_0(esk1_0,esk3_0)), inference(spm,[status(thm)],[c_0_25, c_0_40])).
% 0.59/0.75  cnf(c_0_47, negated_conjecture, (r1_tarski(k4_xboole_0(esk2_0,esk1_0),k2_xboole_0(esk3_0,X1))), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.59/0.75  cnf(c_0_48, plain, (k2_xboole_0(X1,k2_xboole_0(X2,X1))=k2_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_25, c_0_43])).
% 0.59/0.75  cnf(c_0_49, plain, (k2_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X3,X1))=k2_xboole_0(k2_xboole_0(X1,X2),X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_44]), c_0_24])).
% 0.59/0.75  cnf(c_0_50, plain, (k4_xboole_0(X1,k2_xboole_0(k2_xboole_0(X2,X3),X4))=k4_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X3,X4)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_26]), c_0_26]), c_0_26])).
% 0.59/0.75  cnf(c_0_51, plain, (r1_tarski(k4_xboole_0(X1,X2),k2_xboole_0(X3,X4))|~r1_tarski(k4_xboole_0(X1,k2_xboole_0(X2,X3)),X4)), inference(spm,[status(thm)],[c_0_35, c_0_26])).
% 0.59/0.75  cnf(c_0_52, negated_conjecture, (r1_tarski(k4_xboole_0(X1,k2_xboole_0(esk1_0,esk3_0)),k4_xboole_0(X1,esk2_0))), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.59/0.75  cnf(c_0_53, negated_conjecture, (r1_tarski(k4_xboole_0(esk1_0,esk2_0),esk3_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.59/0.75  cnf(c_0_54, negated_conjecture, (r1_tarski(k4_xboole_0(esk2_0,esk1_0),k2_xboole_0(X1,esk3_0))), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.59/0.75  cnf(c_0_55, plain, (k2_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X3,X2))=k2_xboole_0(k2_xboole_0(X1,X2),X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_48]), c_0_24])).
% 0.59/0.75  cnf(c_0_56, plain, (k2_xboole_0(k2_xboole_0(X1,X2),X1)=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_17]), c_0_38])).
% 0.59/0.75  cnf(c_0_57, plain, (k4_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,k2_xboole_0(X2,X3)))=k1_xboole_0), inference(spm,[status(thm)],[c_0_33, c_0_50])).
% 0.59/0.75  cnf(c_0_58, negated_conjecture, (r1_tarski(k4_xboole_0(X1,esk1_0),k2_xboole_0(esk3_0,k4_xboole_0(X1,esk2_0)))), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.59/0.75  cnf(c_0_59, plain, (k2_xboole_0(X1,k4_xboole_0(k2_xboole_0(X2,X1),X2))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_17]), c_0_38])).
% 0.59/0.75  cnf(c_0_60, negated_conjecture, (k4_xboole_0(esk1_0,k2_xboole_0(esk2_0,esk3_0))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_53]), c_0_26])).
% 0.59/0.75  cnf(c_0_61, negated_conjecture, (k2_xboole_0(k4_xboole_0(esk2_0,esk1_0),k2_xboole_0(X1,esk3_0))=k2_xboole_0(X1,esk3_0)), inference(spm,[status(thm)],[c_0_25, c_0_54])).
% 0.59/0.75  cnf(c_0_62, plain, (k2_xboole_0(k2_xboole_0(k4_xboole_0(X1,X2),X2),X1)=k2_xboole_0(k4_xboole_0(X1,X2),X2)), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.59/0.75  cnf(c_0_63, plain, (k4_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X2,X1))=k1_xboole_0), inference(spm,[status(thm)],[c_0_57, c_0_48])).
% 0.59/0.75  cnf(c_0_64, plain, (k2_xboole_0(k1_xboole_0,X1)=X1), inference(spm,[status(thm)],[c_0_25, c_0_22])).
% 0.59/0.75  cnf(c_0_65, plain, (k2_xboole_0(k4_xboole_0(X1,X2),k2_xboole_0(X2,X1))=k2_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_48, c_0_24])).
% 0.59/0.75  cnf(c_0_66, negated_conjecture, (r1_tarski(k4_xboole_0(k2_xboole_0(esk2_0,esk3_0),esk1_0),esk3_0)), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.59/0.75  cnf(c_0_67, negated_conjecture, (r1_tarski(esk1_0,k2_xboole_0(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_32, c_0_60])).
% 0.59/0.75  cnf(c_0_68, negated_conjecture, (k4_xboole_0(k2_xboole_0(k4_xboole_0(esk2_0,esk1_0),X1),k2_xboole_0(X1,esk3_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_57, c_0_61])).
% 0.59/0.75  cnf(c_0_69, plain, (k2_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_64]), c_0_64])).
% 0.59/0.75  fof(c_0_70, plain, ![X4, X5]:k5_xboole_0(X4,X5)=k2_xboole_0(k4_xboole_0(X4,X5),k4_xboole_0(X5,X4)), inference(variable_rename,[status(thm)],[d6_xboole_0])).
% 0.59/0.75  fof(c_0_71, plain, ![X8, X9]:k5_xboole_0(X8,X9)=k4_xboole_0(k2_xboole_0(X8,X9),k3_xboole_0(X8,X9)), inference(variable_rename,[status(thm)],[l98_xboole_1])).
% 0.59/0.75  cnf(c_0_72, plain, (k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X2,X3),X3))=k4_xboole_0(X1,k2_xboole_0(X3,X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_62]), c_0_65])).
% 0.59/0.75  cnf(c_0_73, negated_conjecture, (k4_xboole_0(k2_xboole_0(esk2_0,esk3_0),k2_xboole_0(esk1_0,esk3_0))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_66]), c_0_26])).
% 0.59/0.75  cnf(c_0_74, negated_conjecture, (k2_xboole_0(esk1_0,k2_xboole_0(esk2_0,esk3_0))=k2_xboole_0(esk2_0,esk3_0)), inference(spm,[status(thm)],[c_0_25, c_0_67])).
% 0.59/0.75  cnf(c_0_75, negated_conjecture, (r1_tarski(k2_xboole_0(k4_xboole_0(esk2_0,esk1_0),X1),k2_xboole_0(X1,esk3_0))), inference(spm,[status(thm)],[c_0_32, c_0_68])).
% 0.59/0.75  cnf(c_0_76, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_69]), c_0_69])).
% 0.59/0.75  cnf(c_0_77, plain, (k5_xboole_0(X1,X2)=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_70])).
% 0.59/0.75  cnf(c_0_78, plain, (k5_xboole_0(X1,X2)=k4_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_71])).
% 0.59/0.75  cnf(c_0_79, negated_conjecture, (k4_xboole_0(X1,k2_xboole_0(esk2_0,esk3_0))=k4_xboole_0(X1,k2_xboole_0(esk1_0,esk3_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_73]), c_0_64]), c_0_50]), c_0_48]), c_0_74])).
% 0.59/0.75  cnf(c_0_80, negated_conjecture, (~r1_tarski(k5_xboole_0(esk1_0,esk2_0),esk3_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.59/0.75  cnf(c_0_81, negated_conjecture, (r1_tarski(k2_xboole_0(X1,k4_xboole_0(esk2_0,esk1_0)),k2_xboole_0(X1,esk3_0))), inference(spm,[status(thm)],[c_0_75, c_0_76])).
% 0.59/0.75  cnf(c_0_82, plain, (k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1))=k4_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X2))), inference(rw,[status(thm)],[c_0_77, c_0_78])).
% 0.59/0.75  cnf(c_0_83, negated_conjecture, (k2_xboole_0(esk3_0,k4_xboole_0(X1,esk2_0))=k2_xboole_0(esk3_0,k4_xboole_0(X1,esk1_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_79]), c_0_37])).
% 0.59/0.75  cnf(c_0_84, negated_conjecture, (~r1_tarski(k4_xboole_0(k2_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,esk2_0)),esk3_0)), inference(rw,[status(thm)],[c_0_80, c_0_78])).
% 0.59/0.75  cnf(c_0_85, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_82]), c_0_76]), c_0_83]), c_0_17]), c_0_38]), c_0_84]), ['proof']).
% 0.59/0.75  # SZS output end CNFRefutation
% 0.59/0.75  # Proof object total steps             : 86
% 0.59/0.75  # Proof object clause steps            : 65
% 0.59/0.75  # Proof object formula steps           : 21
% 0.59/0.75  # Proof object conjectures             : 27
% 0.59/0.75  # Proof object clause conjectures      : 24
% 0.59/0.75  # Proof object formula conjectures     : 3
% 0.59/0.75  # Proof object initial clauses used    : 13
% 0.59/0.75  # Proof object initial formulas used   : 10
% 0.59/0.75  # Proof object generating inferences   : 49
% 0.59/0.75  # Proof object simplifying inferences  : 31
% 0.59/0.75  # Training examples: 0 positive, 0 negative
% 0.59/0.75  # Parsed axioms                        : 11
% 0.59/0.75  # Removed by relevancy pruning/SinE    : 0
% 0.59/0.75  # Initial clauses                      : 14
% 0.59/0.75  # Removed in clause preprocessing      : 1
% 0.59/0.75  # Initial clauses in saturation        : 13
% 0.59/0.75  # Processed clauses                    : 1918
% 0.59/0.75  # ...of these trivial                  : 884
% 0.59/0.75  # ...subsumed                          : 13
% 0.59/0.75  # ...remaining for further processing  : 1021
% 0.59/0.75  # Other redundant clauses eliminated   : 0
% 0.59/0.75  # Clauses deleted for lack of memory   : 0
% 0.59/0.75  # Backward-subsumed                    : 0
% 0.59/0.75  # Backward-rewritten                   : 350
% 0.59/0.75  # Generated clauses                    : 75685
% 0.59/0.75  # ...of the previous two non-trivial   : 29624
% 0.59/0.75  # Contextual simplify-reflections      : 0
% 0.59/0.75  # Paramodulations                      : 75683
% 0.59/0.75  # Factorizations                       : 0
% 0.59/0.75  # Equation resolutions                 : 2
% 0.59/0.75  # Propositional unsat checks           : 0
% 0.59/0.75  #    Propositional check models        : 0
% 0.59/0.75  #    Propositional check unsatisfiable : 0
% 0.59/0.75  #    Propositional clauses             : 0
% 0.59/0.75  #    Propositional clauses after purity: 0
% 0.59/0.75  #    Propositional unsat core size     : 0
% 0.59/0.75  #    Propositional preprocessing time  : 0.000
% 0.59/0.75  #    Propositional encoding time       : 0.000
% 0.59/0.75  #    Propositional solver time         : 0.000
% 0.59/0.75  #    Success case prop preproc time    : 0.000
% 0.59/0.75  #    Success case prop encoding time   : 0.000
% 0.59/0.75  #    Success case prop solver time     : 0.000
% 0.59/0.75  # Current number of processed clauses  : 658
% 0.59/0.75  #    Positive orientable unit clauses  : 645
% 0.59/0.75  #    Positive unorientable unit clauses: 1
% 0.59/0.75  #    Negative unit clauses             : 1
% 0.59/0.75  #    Non-unit-clauses                  : 11
% 0.59/0.75  # Current number of unprocessed clauses: 26497
% 0.59/0.75  # ...number of literals in the above   : 27738
% 0.59/0.75  # Current number of archived formulas  : 0
% 0.59/0.75  # Current number of archived clauses   : 364
% 0.59/0.75  # Clause-clause subsumption calls (NU) : 19
% 0.59/0.75  # Rec. Clause-clause subsumption calls : 19
% 0.59/0.75  # Non-unit clause-clause subsumptions  : 5
% 0.59/0.75  # Unit Clause-clause subsumption calls : 152
% 0.59/0.75  # Rewrite failures with RHS unbound    : 0
% 0.59/0.75  # BW rewrite match attempts            : 3127
% 0.59/0.75  # BW rewrite match successes           : 680
% 0.59/0.75  # Condensation attempts                : 0
% 0.59/0.75  # Condensation successes               : 0
% 0.59/0.75  # Termbank termtop insertions          : 786984
% 0.59/0.76  
% 0.59/0.76  # -------------------------------------------------
% 0.59/0.76  # User time                : 0.392 s
% 0.59/0.76  # System time              : 0.024 s
% 0.59/0.76  # Total time               : 0.417 s
% 0.59/0.76  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
