%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:34:45 EST 2020

% Result     : Theorem 0.41s
% Output     : CNFRefutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 579 expanded)
%              Number of clauses        :   67 ( 279 expanded)
%              Number of leaves         :    9 ( 148 expanded)
%              Depth                    :   17
%              Number of atoms          :  152 (1211 expanded)
%              Number of equality atoms :    7 ( 101 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(t79_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(t44_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k4_xboole_0(X1,X2),X3)
     => r1_tarski(X1,k2_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(t63_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_xboole_0(X2,X3) )
     => r1_xboole_0(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

fof(t73_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,k2_xboole_0(X2,X3))
        & r1_xboole_0(X1,X3) )
     => r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_xboole_1)).

fof(t106_xboole_1,conjecture,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k4_xboole_0(X2,X3))
     => ( r1_tarski(X1,X2)
        & r1_xboole_0(X1,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

fof(c_0_9,plain,(
    ! [X10,X11] :
      ( ~ r1_xboole_0(X10,X11)
      | r1_xboole_0(X11,X10) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

fof(c_0_10,plain,(
    ! [X26,X27] : r1_xboole_0(k4_xboole_0(X26,X27),X27) ),
    inference(variable_rename,[status(thm)],[t79_xboole_1])).

fof(c_0_11,plain,(
    ! [X4,X5,X6,X7,X8] :
      ( ( ~ r1_tarski(X4,X5)
        | ~ r2_hidden(X6,X4)
        | r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_2(X7,X8),X7)
        | r1_tarski(X7,X8) )
      & ( ~ r2_hidden(esk1_2(X7,X8),X8)
        | r1_tarski(X7,X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_12,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_14,plain,(
    ! [X14,X15,X16] : k4_xboole_0(k4_xboole_0(X14,X15),X16) = k4_xboole_0(X14,k2_xboole_0(X15,X16)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

fof(c_0_15,plain,(
    ! [X17,X18,X19] :
      ( ~ r1_tarski(k4_xboole_0(X17,X18),X19)
      | r1_tarski(X17,k2_xboole_0(X18,X19)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_xboole_1])])).

cnf(c_0_16,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_18,plain,(
    ! [X12,X13] : k2_xboole_0(X12,k4_xboole_0(X13,X12)) = k2_xboole_0(X12,X13) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

cnf(c_0_19,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_20,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_21,plain,(
    ! [X20,X21,X22] :
      ( ~ r1_tarski(X20,X21)
      | ~ r1_xboole_0(X21,X22)
      | r1_xboole_0(X20,X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_xboole_1])])).

cnf(c_0_22,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r1_tarski(k4_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_24,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_25,plain,(
    ! [X23,X24,X25] :
      ( ~ r1_tarski(X23,k2_xboole_0(X24,X25))
      | ~ r1_xboole_0(X23,X25)
      | r1_tarski(X23,X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t73_xboole_1])])).

cnf(c_0_26,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X3,X1))) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_27,plain,
    ( r1_xboole_0(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24])).

fof(c_0_29,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( r1_tarski(X1,k4_xboole_0(X2,X3))
       => ( r1_tarski(X1,X2)
          & r1_xboole_0(X1,X3) ) ) ),
    inference(assume_negation,[status(cth)],[t106_xboole_1])).

cnf(c_0_30,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r1_xboole_0(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_31,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,k2_xboole_0(X2,X1))) ),
    inference(spm,[status(thm)],[c_0_26,c_0_24])).

cnf(c_0_32,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_27,c_0_19])).

cnf(c_0_33,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),k2_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_24])).

fof(c_0_34,negated_conjecture,
    ( r1_tarski(esk2_0,k4_xboole_0(esk3_0,esk4_0))
    & ( ~ r1_tarski(esk2_0,esk3_0)
      | ~ r1_xboole_0(esk2_0,esk4_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_29])])])).

cnf(c_0_35,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_xboole_0(X1,X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_28])).

cnf(c_0_36,plain,
    ( r1_xboole_0(k4_xboole_0(X1,k2_xboole_0(X2,X2)),k4_xboole_0(X3,k2_xboole_0(X2,X1))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_24]),c_0_20])).

cnf(c_0_37,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_12,c_0_32])).

cnf(c_0_38,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X2)
    | ~ r1_xboole_0(k4_xboole_0(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_33])).

cnf(c_0_39,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_tarski(X1,k4_xboole_0(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_13])).

cnf(c_0_40,negated_conjecture,
    ( r1_tarski(esk2_0,k4_xboole_0(esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_41,plain,
    ( r1_tarski(k4_xboole_0(X1,k2_xboole_0(X1,X1)),X2) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_42,plain,
    ( r1_xboole_0(k4_xboole_0(X1,k2_xboole_0(X2,X3)),X3) ),
    inference(spm,[status(thm)],[c_0_13,c_0_20])).

cnf(c_0_43,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(k4_xboole_0(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_35,c_0_37])).

cnf(c_0_44,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X2)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_38,c_0_37])).

cnf(c_0_45,negated_conjecture,
    ( r1_xboole_0(esk2_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_46,plain,
    ( r1_xboole_0(k4_xboole_0(X1,k2_xboole_0(X1,X1)),X2) ),
    inference(spm,[status(thm)],[c_0_39,c_0_41])).

cnf(c_0_47,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_tarski(X1,k4_xboole_0(X3,k2_xboole_0(X4,X2))) ),
    inference(spm,[status(thm)],[c_0_27,c_0_42])).

cnf(c_0_48,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_49,negated_conjecture,
    ( r1_xboole_0(esk4_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_12,c_0_45])).

cnf(c_0_50,plain,
    ( r1_tarski(k2_xboole_0(X1,X2),X1)
    | ~ r1_xboole_0(k2_xboole_0(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_30,c_0_23])).

cnf(c_0_51,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X2,X2))) ),
    inference(spm,[status(thm)],[c_0_12,c_0_46])).

cnf(c_0_52,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_53,negated_conjecture,
    ( r1_xboole_0(X1,esk2_0)
    | ~ r1_tarski(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_49])).

cnf(c_0_54,plain,
    ( r1_tarski(k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X2,X2))),X1) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_55,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X3,X1))) = k2_xboole_0(X1,k4_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_20])).

cnf(c_0_56,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X2,X3))
    | ~ r1_tarski(X2,X3) ),
    inference(spm,[status(thm)],[c_0_12,c_0_52])).

cnf(c_0_57,plain,
    ( r1_tarski(k4_xboole_0(X1,k2_xboole_0(X2,X1)),k2_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_42])).

cnf(c_0_58,negated_conjecture,
    ( r1_xboole_0(X1,esk2_0)
    | ~ r1_tarski(X2,esk4_0)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_27,c_0_53])).

cnf(c_0_59,plain,
    ( r1_tarski(k2_xboole_0(X1,X1),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_24])).

cnf(c_0_60,plain,
    ( r1_tarski(k2_xboole_0(X1,k4_xboole_0(X2,X3)),X1)
    | ~ r1_tarski(X2,X3) ),
    inference(spm,[status(thm)],[c_0_50,c_0_56])).

cnf(c_0_61,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X4)
    | ~ r1_tarski(X4,X3) ),
    inference(spm,[status(thm)],[c_0_27,c_0_32])).

cnf(c_0_62,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),k2_xboole_0(X3,X4))
    | ~ r1_tarski(k4_xboole_0(X1,k2_xboole_0(X2,X3)),X4) ),
    inference(spm,[status(thm)],[c_0_22,c_0_20])).

cnf(c_0_63,plain,
    ( r1_tarski(k4_xboole_0(X1,k2_xboole_0(X2,X1)),X3) ),
    inference(spm,[status(thm)],[c_0_43,c_0_57])).

cnf(c_0_64,negated_conjecture,
    ( r1_xboole_0(X1,esk2_0)
    | ~ r1_tarski(X1,k2_xboole_0(esk4_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_65,plain,
    ( r1_tarski(k2_xboole_0(X1,X2),X1)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_60,c_0_24])).

cnf(c_0_66,negated_conjecture,
    ( r1_xboole_0(esk2_0,k4_xboole_0(X1,X2))
    | ~ r1_tarski(k4_xboole_0(esk3_0,esk4_0),X2) ),
    inference(spm,[status(thm)],[c_0_61,c_0_40])).

cnf(c_0_67,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),k2_xboole_0(X1,X3)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_68,plain,
    ( r1_xboole_0(k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X2)),X2) ),
    inference(spm,[status(thm)],[c_0_39,c_0_59])).

cnf(c_0_69,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,k2_xboole_0(X3,k4_xboole_0(X1,X2)))) ),
    inference(spm,[status(thm)],[c_0_22,c_0_28])).

cnf(c_0_70,negated_conjecture,
    ( r1_xboole_0(k2_xboole_0(k2_xboole_0(esk4_0,esk4_0),X1),esk2_0)
    | ~ r1_tarski(X1,k2_xboole_0(esk4_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_71,negated_conjecture,
    ( r1_xboole_0(k4_xboole_0(X1,X2),esk2_0)
    | ~ r1_tarski(k4_xboole_0(esk3_0,esk4_0),X2) ),
    inference(spm,[status(thm)],[c_0_12,c_0_66])).

cnf(c_0_72,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1)
    | ~ r1_xboole_0(k4_xboole_0(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_30,c_0_67])).

cnf(c_0_73,plain,
    ( r1_xboole_0(X1,k2_xboole_0(k4_xboole_0(X2,X1),k4_xboole_0(X2,X1))) ),
    inference(spm,[status(thm)],[c_0_12,c_0_68])).

cnf(c_0_74,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_xboole_0(X1,k2_xboole_0(X3,k4_xboole_0(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_30,c_0_69])).

cnf(c_0_75,negated_conjecture,
    ( r1_xboole_0(esk2_0,k2_xboole_0(k2_xboole_0(esk4_0,esk4_0),X1))
    | ~ r1_tarski(X1,k2_xboole_0(esk4_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_12,c_0_70])).

cnf(c_0_76,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk2_0,X1),X1)
    | ~ r1_tarski(k4_xboole_0(esk3_0,esk4_0),X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_71])).

cnf(c_0_77,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_78,negated_conjecture,
    ( r1_tarski(esk2_0,X1)
    | ~ r1_tarski(k4_xboole_0(esk2_0,X1),k2_xboole_0(esk4_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_79,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_22,c_0_48])).

cnf(c_0_80,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk2_0,esk3_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_76,c_0_77])).

cnf(c_0_81,negated_conjecture,
    ( ~ r1_tarski(esk2_0,esk3_0)
    | ~ r1_xboole_0(esk2_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_82,negated_conjecture,
    ( r1_tarski(esk2_0,X1)
    | ~ r1_tarski(k4_xboole_0(esk2_0,X1),esk4_0) ),
    inference(spm,[status(thm)],[c_0_78,c_0_79])).

cnf(c_0_83,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk2_0,esk3_0),X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_80])).

cnf(c_0_84,negated_conjecture,
    ( ~ r1_tarski(esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_81,c_0_45])])).

cnf(c_0_85,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_84]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:57:31 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.41/0.59  # AutoSched0-Mode selected heuristic G_____X1276__C12_02_nc_F1_AE_CS_SP_RG_S04AN
% 0.41/0.59  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.41/0.59  #
% 0.41/0.59  # Preprocessing time       : 0.026 s
% 0.41/0.59  # Presaturation interreduction done
% 0.41/0.59  
% 0.41/0.59  # Proof found!
% 0.41/0.59  # SZS status Theorem
% 0.41/0.59  # SZS output start CNFRefutation
% 0.41/0.59  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 0.41/0.59  fof(t79_xboole_1, axiom, ![X1, X2]:r1_xboole_0(k4_xboole_0(X1,X2),X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 0.41/0.59  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.41/0.59  fof(t41_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 0.41/0.59  fof(t44_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(k4_xboole_0(X1,X2),X3)=>r1_tarski(X1,k2_xboole_0(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_xboole_1)).
% 0.41/0.59  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 0.41/0.59  fof(t63_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_xboole_0(X2,X3))=>r1_xboole_0(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 0.41/0.59  fof(t73_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,k2_xboole_0(X2,X3))&r1_xboole_0(X1,X3))=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_xboole_1)).
% 0.41/0.59  fof(t106_xboole_1, conjecture, ![X1, X2, X3]:(r1_tarski(X1,k4_xboole_0(X2,X3))=>(r1_tarski(X1,X2)&r1_xboole_0(X1,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 0.41/0.59  fof(c_0_9, plain, ![X10, X11]:(~r1_xboole_0(X10,X11)|r1_xboole_0(X11,X10)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 0.41/0.59  fof(c_0_10, plain, ![X26, X27]:r1_xboole_0(k4_xboole_0(X26,X27),X27), inference(variable_rename,[status(thm)],[t79_xboole_1])).
% 0.41/0.59  fof(c_0_11, plain, ![X4, X5, X6, X7, X8]:((~r1_tarski(X4,X5)|(~r2_hidden(X6,X4)|r2_hidden(X6,X5)))&((r2_hidden(esk1_2(X7,X8),X7)|r1_tarski(X7,X8))&(~r2_hidden(esk1_2(X7,X8),X8)|r1_tarski(X7,X8)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.41/0.59  cnf(c_0_12, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.41/0.59  cnf(c_0_13, plain, (r1_xboole_0(k4_xboole_0(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.41/0.59  fof(c_0_14, plain, ![X14, X15, X16]:k4_xboole_0(k4_xboole_0(X14,X15),X16)=k4_xboole_0(X14,k2_xboole_0(X15,X16)), inference(variable_rename,[status(thm)],[t41_xboole_1])).
% 0.41/0.59  fof(c_0_15, plain, ![X17, X18, X19]:(~r1_tarski(k4_xboole_0(X17,X18),X19)|r1_tarski(X17,k2_xboole_0(X18,X19))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_xboole_1])])).
% 0.41/0.59  cnf(c_0_16, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.41/0.59  cnf(c_0_17, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.41/0.59  fof(c_0_18, plain, ![X12, X13]:k2_xboole_0(X12,k4_xboole_0(X13,X12))=k2_xboole_0(X12,X13), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 0.41/0.59  cnf(c_0_19, plain, (r1_xboole_0(X1,k4_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.41/0.59  cnf(c_0_20, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.41/0.59  fof(c_0_21, plain, ![X20, X21, X22]:(~r1_tarski(X20,X21)|~r1_xboole_0(X21,X22)|r1_xboole_0(X20,X22)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_xboole_1])])).
% 0.41/0.59  cnf(c_0_22, plain, (r1_tarski(X1,k2_xboole_0(X2,X3))|~r1_tarski(k4_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.41/0.59  cnf(c_0_23, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.41/0.59  cnf(c_0_24, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.41/0.59  fof(c_0_25, plain, ![X23, X24, X25]:(~r1_tarski(X23,k2_xboole_0(X24,X25))|~r1_xboole_0(X23,X25)|r1_tarski(X23,X24)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t73_xboole_1])])).
% 0.41/0.59  cnf(c_0_26, plain, (r1_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X3,X1)))), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.41/0.59  cnf(c_0_27, plain, (r1_xboole_0(X1,X3)|~r1_tarski(X1,X2)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.41/0.59  cnf(c_0_28, plain, (r1_tarski(X1,k2_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24])).
% 0.41/0.59  fof(c_0_29, negated_conjecture, ~(![X1, X2, X3]:(r1_tarski(X1,k4_xboole_0(X2,X3))=>(r1_tarski(X1,X2)&r1_xboole_0(X1,X3)))), inference(assume_negation,[status(cth)],[t106_xboole_1])).
% 0.41/0.59  cnf(c_0_30, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k2_xboole_0(X2,X3))|~r1_xboole_0(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.41/0.59  cnf(c_0_31, plain, (r1_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,k2_xboole_0(X2,X1)))), inference(spm,[status(thm)],[c_0_26, c_0_24])).
% 0.41/0.59  cnf(c_0_32, plain, (r1_xboole_0(X1,k4_xboole_0(X2,X3))|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_27, c_0_19])).
% 0.41/0.59  cnf(c_0_33, plain, (r1_tarski(k4_xboole_0(X1,X2),k2_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_28, c_0_24])).
% 0.41/0.59  fof(c_0_34, negated_conjecture, (r1_tarski(esk2_0,k4_xboole_0(esk3_0,esk4_0))&(~r1_tarski(esk2_0,esk3_0)|~r1_xboole_0(esk2_0,esk4_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_29])])])).
% 0.41/0.59  cnf(c_0_35, plain, (r1_tarski(X1,X2)|~r1_xboole_0(X1,X1)), inference(spm,[status(thm)],[c_0_30, c_0_28])).
% 0.41/0.59  cnf(c_0_36, plain, (r1_xboole_0(k4_xboole_0(X1,k2_xboole_0(X2,X2)),k4_xboole_0(X3,k2_xboole_0(X2,X1)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_24]), c_0_20])).
% 0.41/0.59  cnf(c_0_37, plain, (r1_xboole_0(k4_xboole_0(X1,X2),X3)|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_12, c_0_32])).
% 0.41/0.59  cnf(c_0_38, plain, (r1_tarski(k4_xboole_0(X1,X2),X2)|~r1_xboole_0(k4_xboole_0(X1,X2),X1)), inference(spm,[status(thm)],[c_0_30, c_0_33])).
% 0.41/0.59  cnf(c_0_39, plain, (r1_xboole_0(X1,X2)|~r1_tarski(X1,k4_xboole_0(X3,X2))), inference(spm,[status(thm)],[c_0_27, c_0_13])).
% 0.41/0.59  cnf(c_0_40, negated_conjecture, (r1_tarski(esk2_0,k4_xboole_0(esk3_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.41/0.59  cnf(c_0_41, plain, (r1_tarski(k4_xboole_0(X1,k2_xboole_0(X1,X1)),X2)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.41/0.59  cnf(c_0_42, plain, (r1_xboole_0(k4_xboole_0(X1,k2_xboole_0(X2,X3)),X3)), inference(spm,[status(thm)],[c_0_13, c_0_20])).
% 0.41/0.59  cnf(c_0_43, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|~r1_tarski(k4_xboole_0(X1,X2),X2)), inference(spm,[status(thm)],[c_0_35, c_0_37])).
% 0.41/0.59  cnf(c_0_44, plain, (r1_tarski(k4_xboole_0(X1,X2),X2)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_38, c_0_37])).
% 0.41/0.59  cnf(c_0_45, negated_conjecture, (r1_xboole_0(esk2_0,esk4_0)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.41/0.59  cnf(c_0_46, plain, (r1_xboole_0(k4_xboole_0(X1,k2_xboole_0(X1,X1)),X2)), inference(spm,[status(thm)],[c_0_39, c_0_41])).
% 0.41/0.59  cnf(c_0_47, plain, (r1_xboole_0(X1,X2)|~r1_tarski(X1,k4_xboole_0(X3,k2_xboole_0(X4,X2)))), inference(spm,[status(thm)],[c_0_27, c_0_42])).
% 0.41/0.59  cnf(c_0_48, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.41/0.59  cnf(c_0_49, negated_conjecture, (r1_xboole_0(esk4_0,esk2_0)), inference(spm,[status(thm)],[c_0_12, c_0_45])).
% 0.41/0.59  cnf(c_0_50, plain, (r1_tarski(k2_xboole_0(X1,X2),X1)|~r1_xboole_0(k2_xboole_0(X1,X2),X2)), inference(spm,[status(thm)],[c_0_30, c_0_23])).
% 0.41/0.59  cnf(c_0_51, plain, (r1_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X2,X2)))), inference(spm,[status(thm)],[c_0_12, c_0_46])).
% 0.41/0.59  cnf(c_0_52, plain, (r1_xboole_0(k4_xboole_0(X1,X2),X3)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.41/0.59  cnf(c_0_53, negated_conjecture, (r1_xboole_0(X1,esk2_0)|~r1_tarski(X1,esk4_0)), inference(spm,[status(thm)],[c_0_27, c_0_49])).
% 0.41/0.59  cnf(c_0_54, plain, (r1_tarski(k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X2,X2))),X1)), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.41/0.59  cnf(c_0_55, plain, (k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X3,X1)))=k2_xboole_0(X1,k4_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_24, c_0_20])).
% 0.41/0.59  cnf(c_0_56, plain, (r1_xboole_0(X1,k4_xboole_0(X2,X3))|~r1_tarski(X2,X3)), inference(spm,[status(thm)],[c_0_12, c_0_52])).
% 0.41/0.59  cnf(c_0_57, plain, (r1_tarski(k4_xboole_0(X1,k2_xboole_0(X2,X1)),k2_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_38, c_0_42])).
% 0.41/0.59  cnf(c_0_58, negated_conjecture, (r1_xboole_0(X1,esk2_0)|~r1_tarski(X2,esk4_0)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_27, c_0_53])).
% 0.41/0.59  cnf(c_0_59, plain, (r1_tarski(k2_xboole_0(X1,X1),X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_24])).
% 0.41/0.59  cnf(c_0_60, plain, (r1_tarski(k2_xboole_0(X1,k4_xboole_0(X2,X3)),X1)|~r1_tarski(X2,X3)), inference(spm,[status(thm)],[c_0_50, c_0_56])).
% 0.41/0.59  cnf(c_0_61, plain, (r1_xboole_0(X1,k4_xboole_0(X2,X3))|~r1_tarski(X1,X4)|~r1_tarski(X4,X3)), inference(spm,[status(thm)],[c_0_27, c_0_32])).
% 0.41/0.59  cnf(c_0_62, plain, (r1_tarski(k4_xboole_0(X1,X2),k2_xboole_0(X3,X4))|~r1_tarski(k4_xboole_0(X1,k2_xboole_0(X2,X3)),X4)), inference(spm,[status(thm)],[c_0_22, c_0_20])).
% 0.41/0.59  cnf(c_0_63, plain, (r1_tarski(k4_xboole_0(X1,k2_xboole_0(X2,X1)),X3)), inference(spm,[status(thm)],[c_0_43, c_0_57])).
% 0.41/0.59  cnf(c_0_64, negated_conjecture, (r1_xboole_0(X1,esk2_0)|~r1_tarski(X1,k2_xboole_0(esk4_0,esk4_0))), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.41/0.59  cnf(c_0_65, plain, (r1_tarski(k2_xboole_0(X1,X2),X1)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_60, c_0_24])).
% 0.41/0.59  cnf(c_0_66, negated_conjecture, (r1_xboole_0(esk2_0,k4_xboole_0(X1,X2))|~r1_tarski(k4_xboole_0(esk3_0,esk4_0),X2)), inference(spm,[status(thm)],[c_0_61, c_0_40])).
% 0.41/0.59  cnf(c_0_67, plain, (r1_tarski(k4_xboole_0(X1,X2),k2_xboole_0(X1,X3))), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 0.41/0.59  cnf(c_0_68, plain, (r1_xboole_0(k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X2)),X2)), inference(spm,[status(thm)],[c_0_39, c_0_59])).
% 0.41/0.59  cnf(c_0_69, plain, (r1_tarski(X1,k2_xboole_0(X2,k2_xboole_0(X3,k4_xboole_0(X1,X2))))), inference(spm,[status(thm)],[c_0_22, c_0_28])).
% 0.41/0.59  cnf(c_0_70, negated_conjecture, (r1_xboole_0(k2_xboole_0(k2_xboole_0(esk4_0,esk4_0),X1),esk2_0)|~r1_tarski(X1,k2_xboole_0(esk4_0,esk4_0))), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 0.41/0.59  cnf(c_0_71, negated_conjecture, (r1_xboole_0(k4_xboole_0(X1,X2),esk2_0)|~r1_tarski(k4_xboole_0(esk3_0,esk4_0),X2)), inference(spm,[status(thm)],[c_0_12, c_0_66])).
% 0.41/0.59  cnf(c_0_72, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)|~r1_xboole_0(k4_xboole_0(X1,X2),X3)), inference(spm,[status(thm)],[c_0_30, c_0_67])).
% 0.41/0.59  cnf(c_0_73, plain, (r1_xboole_0(X1,k2_xboole_0(k4_xboole_0(X2,X1),k4_xboole_0(X2,X1)))), inference(spm,[status(thm)],[c_0_12, c_0_68])).
% 0.41/0.59  cnf(c_0_74, plain, (r1_tarski(X1,X2)|~r1_xboole_0(X1,k2_xboole_0(X3,k4_xboole_0(X1,X2)))), inference(spm,[status(thm)],[c_0_30, c_0_69])).
% 0.41/0.59  cnf(c_0_75, negated_conjecture, (r1_xboole_0(esk2_0,k2_xboole_0(k2_xboole_0(esk4_0,esk4_0),X1))|~r1_tarski(X1,k2_xboole_0(esk4_0,esk4_0))), inference(spm,[status(thm)],[c_0_12, c_0_70])).
% 0.41/0.59  cnf(c_0_76, negated_conjecture, (r1_tarski(k4_xboole_0(esk2_0,X1),X1)|~r1_tarski(k4_xboole_0(esk3_0,esk4_0),X1)), inference(spm,[status(thm)],[c_0_38, c_0_71])).
% 0.41/0.59  cnf(c_0_77, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(spm,[status(thm)],[c_0_72, c_0_73])).
% 0.41/0.59  cnf(c_0_78, negated_conjecture, (r1_tarski(esk2_0,X1)|~r1_tarski(k4_xboole_0(esk2_0,X1),k2_xboole_0(esk4_0,esk4_0))), inference(spm,[status(thm)],[c_0_74, c_0_75])).
% 0.41/0.59  cnf(c_0_79, plain, (r1_tarski(X1,k2_xboole_0(X2,X3))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_22, c_0_48])).
% 0.41/0.59  cnf(c_0_80, negated_conjecture, (r1_tarski(k4_xboole_0(esk2_0,esk3_0),esk3_0)), inference(spm,[status(thm)],[c_0_76, c_0_77])).
% 0.41/0.59  cnf(c_0_81, negated_conjecture, (~r1_tarski(esk2_0,esk3_0)|~r1_xboole_0(esk2_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.41/0.59  cnf(c_0_82, negated_conjecture, (r1_tarski(esk2_0,X1)|~r1_tarski(k4_xboole_0(esk2_0,X1),esk4_0)), inference(spm,[status(thm)],[c_0_78, c_0_79])).
% 0.41/0.59  cnf(c_0_83, negated_conjecture, (r1_tarski(k4_xboole_0(esk2_0,esk3_0),X1)), inference(spm,[status(thm)],[c_0_43, c_0_80])).
% 0.41/0.59  cnf(c_0_84, negated_conjecture, (~r1_tarski(esk2_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_81, c_0_45])])).
% 0.41/0.59  cnf(c_0_85, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_83]), c_0_84]), ['proof']).
% 0.41/0.59  # SZS output end CNFRefutation
% 0.41/0.59  # Proof object total steps             : 86
% 0.41/0.59  # Proof object clause steps            : 67
% 0.41/0.59  # Proof object formula steps           : 19
% 0.41/0.59  # Proof object conjectures             : 21
% 0.41/0.59  # Proof object clause conjectures      : 18
% 0.41/0.59  # Proof object formula conjectures     : 3
% 0.41/0.59  # Proof object initial clauses used    : 11
% 0.41/0.59  # Proof object initial formulas used   : 9
% 0.41/0.59  # Proof object generating inferences   : 55
% 0.41/0.59  # Proof object simplifying inferences  : 6
% 0.41/0.59  # Training examples: 0 positive, 0 negative
% 0.41/0.59  # Parsed axioms                        : 9
% 0.41/0.59  # Removed by relevancy pruning/SinE    : 0
% 0.41/0.59  # Initial clauses                      : 12
% 0.41/0.59  # Removed in clause preprocessing      : 0
% 0.41/0.59  # Initial clauses in saturation        : 12
% 0.41/0.59  # Processed clauses                    : 2177
% 0.41/0.59  # ...of these trivial                  : 367
% 0.41/0.59  # ...subsumed                          : 538
% 0.41/0.59  # ...remaining for further processing  : 1272
% 0.41/0.59  # Other redundant clauses eliminated   : 0
% 0.41/0.59  # Clauses deleted for lack of memory   : 0
% 0.41/0.59  # Backward-subsumed                    : 70
% 0.41/0.59  # Backward-rewritten                   : 454
% 0.41/0.59  # Generated clauses                    : 20006
% 0.41/0.59  # ...of the previous two non-trivial   : 14564
% 0.41/0.59  # Contextual simplify-reflections      : 0
% 0.41/0.59  # Paramodulations                      : 20006
% 0.41/0.59  # Factorizations                       : 0
% 0.41/0.59  # Equation resolutions                 : 0
% 0.41/0.59  # Propositional unsat checks           : 0
% 0.41/0.59  #    Propositional check models        : 0
% 0.41/0.59  #    Propositional check unsatisfiable : 0
% 0.41/0.59  #    Propositional clauses             : 0
% 0.41/0.59  #    Propositional clauses after purity: 0
% 0.41/0.59  #    Propositional unsat core size     : 0
% 0.41/0.59  #    Propositional preprocessing time  : 0.000
% 0.41/0.59  #    Propositional encoding time       : 0.000
% 0.41/0.59  #    Propositional solver time         : 0.000
% 0.41/0.59  #    Success case prop preproc time    : 0.000
% 0.41/0.59  #    Success case prop encoding time   : 0.000
% 0.41/0.59  #    Success case prop solver time     : 0.000
% 0.41/0.59  # Current number of processed clauses  : 736
% 0.41/0.59  #    Positive orientable unit clauses  : 529
% 0.41/0.59  #    Positive unorientable unit clauses: 0
% 0.41/0.59  #    Negative unit clauses             : 3
% 0.41/0.59  #    Non-unit-clauses                  : 204
% 0.41/0.59  # Current number of unprocessed clauses: 12022
% 0.41/0.59  # ...number of literals in the above   : 16118
% 0.41/0.59  # Current number of archived formulas  : 0
% 0.41/0.59  # Current number of archived clauses   : 536
% 0.41/0.59  # Clause-clause subsumption calls (NU) : 6183
% 0.41/0.59  # Rec. Clause-clause subsumption calls : 6161
% 0.41/0.59  # Non-unit clause-clause subsumptions  : 602
% 0.41/0.59  # Unit Clause-clause subsumption calls : 1633
% 0.41/0.59  # Rewrite failures with RHS unbound    : 0
% 0.41/0.59  # BW rewrite match attempts            : 8016
% 0.41/0.59  # BW rewrite match successes           : 455
% 0.41/0.59  # Condensation attempts                : 0
% 0.41/0.59  # Condensation successes               : 0
% 0.41/0.59  # Termbank termtop insertions          : 284621
% 0.41/0.60  
% 0.41/0.60  # -------------------------------------------------
% 0.41/0.60  # User time                : 0.237 s
% 0.41/0.60  # System time              : 0.018 s
% 0.41/0.60  # Total time               : 0.256 s
% 0.41/0.60  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
