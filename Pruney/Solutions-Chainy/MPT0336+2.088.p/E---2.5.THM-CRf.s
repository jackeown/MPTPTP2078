%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:45:00 EST 2020

% Result     : Theorem 0.39s
% Output     : CNFRefutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   91 (1218 expanded)
%              Number of clauses        :   64 ( 547 expanded)
%              Number of leaves         :   13 ( 312 expanded)
%              Depth                    :   21
%              Number of atoms          :  158 (2457 expanded)
%              Number of equality atoms :   40 ( 727 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal clause size      :    7 (   1 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t149_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( r1_tarski(k3_xboole_0(X1,X2),k1_tarski(X4))
        & r2_hidden(X4,X3)
        & r1_xboole_0(X3,X2) )
     => r1_xboole_0(k2_xboole_0(X1,X3),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_zfmisc_1)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t83_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k4_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(t3_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X2) ) )
      & ~ ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(X3,X2) )
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(t65_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,k1_tarski(X2)) = X1
    <=> ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t79_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(t106_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k4_xboole_0(X2,X3))
     => ( r1_tarski(X1,X2)
        & r1_xboole_0(X1,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

fof(t74_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( ~ r1_xboole_0(X1,k3_xboole_0(X2,X3))
        & r1_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_xboole_1)).

fof(t70_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ~ ( ~ r1_xboole_0(X1,k2_xboole_0(X2,X3))
          & r1_xboole_0(X1,X2)
          & r1_xboole_0(X1,X3) )
      & ~ ( ~ ( r1_xboole_0(X1,X2)
              & r1_xboole_0(X1,X3) )
          & r1_xboole_0(X1,k2_xboole_0(X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( r1_tarski(k3_xboole_0(X1,X2),k1_tarski(X4))
          & r2_hidden(X4,X3)
          & r1_xboole_0(X3,X2) )
       => r1_xboole_0(k2_xboole_0(X1,X3),X2) ) ),
    inference(assume_negation,[status(cth)],[t149_zfmisc_1])).

fof(c_0_14,plain,(
    ! [X7,X8] :
      ( ~ r1_xboole_0(X7,X8)
      | r1_xboole_0(X8,X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

fof(c_0_15,negated_conjecture,
    ( r1_tarski(k3_xboole_0(esk2_0,esk3_0),k1_tarski(esk5_0))
    & r2_hidden(esk5_0,esk4_0)
    & r1_xboole_0(esk4_0,esk3_0)
    & ~ r1_xboole_0(k2_xboole_0(esk2_0,esk4_0),esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).

fof(c_0_16,plain,(
    ! [X5,X6] : k3_xboole_0(X5,X6) = k3_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_17,plain,(
    ! [X18,X19] : k4_xboole_0(X18,k4_xboole_0(X18,X19)) = k3_xboole_0(X18,X19) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_18,plain,(
    ! [X28,X29] :
      ( ( ~ r1_xboole_0(X28,X29)
        | k4_xboole_0(X28,X29) = X28 )
      & ( k4_xboole_0(X28,X29) != X28
        | r1_xboole_0(X28,X29) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).

cnf(c_0_19,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,negated_conjecture,
    ( r1_xboole_0(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,plain,
    ( k4_xboole_0(X1,X2) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,negated_conjecture,
    ( r1_xboole_0(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

fof(c_0_25,plain,(
    ! [X9,X10,X12,X13,X14] :
      ( ( r2_hidden(esk1_2(X9,X10),X9)
        | r1_xboole_0(X9,X10) )
      & ( r2_hidden(esk1_2(X9,X10),X10)
        | r1_xboole_0(X9,X10) )
      & ( ~ r2_hidden(X14,X12)
        | ~ r2_hidden(X14,X13)
        | ~ r1_xboole_0(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

fof(c_0_26,plain,(
    ! [X33,X34] :
      ( ( k4_xboole_0(X33,k1_tarski(X34)) != X33
        | ~ r2_hidden(X34,X33) )
      & ( r2_hidden(X34,X33)
        | k4_xboole_0(X33,k1_tarski(X34)) = X33 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_zfmisc_1])])])).

fof(c_0_27,plain,(
    ! [X30] : k2_tarski(X30,X30) = k1_tarski(X30) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_28,plain,(
    ! [X31,X32] : k1_enumset1(X31,X31,X32) = k2_tarski(X31,X32) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_29,plain,(
    ! [X26,X27] : r1_xboole_0(k4_xboole_0(X26,X27),X27) ),
    inference(variable_rename,[status(thm)],[t79_xboole_1])).

cnf(c_0_30,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X2,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21,c_0_22]),c_0_22])).

cnf(c_0_31,negated_conjecture,
    ( k4_xboole_0(esk3_0,esk4_0) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_32,negated_conjecture,
    ( k4_xboole_0(esk4_0,esk3_0) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_23,c_0_20])).

cnf(c_0_33,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_35,plain,
    ( r2_hidden(X1,X2)
    | k4_xboole_0(X2,k1_tarski(X1)) = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_36,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_37,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_38,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_39,negated_conjecture,
    ( k4_xboole_0(esk3_0,esk3_0) = k4_xboole_0(esk4_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32])).

cnf(c_0_40,negated_conjecture,
    ( ~ r2_hidden(esk5_0,X1)
    | ~ r1_xboole_0(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_41,plain,
    ( k4_xboole_0(X2,k1_enumset1(X1,X1,X1)) = X2
    | r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_36]),c_0_37])).

cnf(c_0_42,negated_conjecture,
    ( r1_xboole_0(k4_xboole_0(esk4_0,esk4_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_43,negated_conjecture,
    ( k4_xboole_0(X1,k1_enumset1(esk5_0,esk5_0,esk5_0)) = X1
    | ~ r1_xboole_0(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_44,negated_conjecture,
    ( r1_xboole_0(esk3_0,k4_xboole_0(esk4_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_42])).

cnf(c_0_45,negated_conjecture,
    ( k4_xboole_0(esk3_0,k1_enumset1(esk5_0,esk5_0,esk5_0)) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_43,c_0_24])).

cnf(c_0_46,plain,
    ( r2_hidden(esk1_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_47,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(esk4_0,esk4_0),esk3_0) = k4_xboole_0(esk4_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_42])).

cnf(c_0_48,negated_conjecture,
    ( k4_xboole_0(esk3_0,k4_xboole_0(esk4_0,esk4_0)) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_23,c_0_44])).

cnf(c_0_49,negated_conjecture,
    ( r1_xboole_0(esk3_0,k1_enumset1(esk5_0,esk5_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_45])).

cnf(c_0_50,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X3)
    | ~ r1_xboole_0(X3,X2) ),
    inference(spm,[status(thm)],[c_0_33,c_0_46])).

cnf(c_0_51,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(esk4_0,esk4_0),k4_xboole_0(esk4_0,esk4_0)) = k4_xboole_0(esk4_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_47]),c_0_48]),c_0_39])).

fof(c_0_52,plain,(
    ! [X15,X16,X17] :
      ( ( r1_tarski(X15,X16)
        | ~ r1_tarski(X15,k4_xboole_0(X16,X17)) )
      & ( r1_xboole_0(X15,X17)
        | ~ r1_tarski(X15,k4_xboole_0(X16,X17)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t106_xboole_1])])])).

cnf(c_0_53,negated_conjecture,
    ( r1_xboole_0(k1_enumset1(esk5_0,esk5_0,esk5_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_49])).

cnf(c_0_54,negated_conjecture,
    ( r1_tarski(k3_xboole_0(esk2_0,esk3_0),k1_tarski(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_55,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X2,X2) ),
    inference(spm,[status(thm)],[c_0_50,c_0_46])).

cnf(c_0_56,negated_conjecture,
    ( r1_xboole_0(k4_xboole_0(esk4_0,esk4_0),k4_xboole_0(esk4_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_51])).

fof(c_0_57,plain,(
    ! [X23,X24,X25] :
      ( r1_xboole_0(X23,k3_xboole_0(X24,X25))
      | ~ r1_xboole_0(X23,X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t74_xboole_1])])])).

cnf(c_0_58,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_tarski(X1,k4_xboole_0(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_59,negated_conjecture,
    ( k4_xboole_0(k1_enumset1(esk5_0,esk5_0,esk5_0),esk3_0) = k1_enumset1(esk5_0,esk5_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_53])).

cnf(c_0_60,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0)),k1_enumset1(esk5_0,esk5_0,esk5_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54,c_0_36]),c_0_37]),c_0_22])).

cnf(c_0_61,negated_conjecture,
    ( r1_xboole_0(X1,k4_xboole_0(esk4_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_62,plain,
    ( r1_xboole_0(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_63,negated_conjecture,
    ( r1_xboole_0(X1,esk3_0)
    | ~ r1_tarski(X1,k1_enumset1(esk5_0,esk5_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_64,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk2_0)),k1_enumset1(esk5_0,esk5_0,esk5_0)) ),
    inference(rw,[status(thm)],[c_0_60,c_0_30])).

cnf(c_0_65,negated_conjecture,
    ( r1_xboole_0(k4_xboole_0(esk4_0,esk4_0),X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_61])).

cnf(c_0_66,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_62,c_0_22])).

cnf(c_0_67,negated_conjecture,
    ( r1_xboole_0(k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk2_0)),esk3_0) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_68,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(esk4_0,esk4_0),X1) = k4_xboole_0(esk4_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_65])).

cnf(c_0_69,negated_conjecture,
    ( k4_xboole_0(X1,k4_xboole_0(esk4_0,esk4_0)) = X1 ),
    inference(spm,[status(thm)],[c_0_23,c_0_61])).

cnf(c_0_70,negated_conjecture,
    ( r1_xboole_0(k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk2_0)),k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,X1))) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_71,negated_conjecture,
    ( k4_xboole_0(esk4_0,esk4_0) = k4_xboole_0(X1,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_68]),c_0_69])).

cnf(c_0_72,negated_conjecture,
    ( r1_xboole_0(X1,k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk2_0))) ),
    inference(spm,[status(thm)],[c_0_55,c_0_70])).

fof(c_0_73,plain,(
    ! [X20,X21,X22] :
      ( ( r1_xboole_0(X20,k2_xboole_0(X21,X22))
        | ~ r1_xboole_0(X20,X21)
        | ~ r1_xboole_0(X20,X22) )
      & ( r1_xboole_0(X20,X21)
        | ~ r1_xboole_0(X20,k2_xboole_0(X21,X22)) )
      & ( r1_xboole_0(X20,X22)
        | ~ r1_xboole_0(X20,k2_xboole_0(X21,X22)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t70_xboole_1])])])])).

cnf(c_0_74,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,k4_xboole_0(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_66,c_0_38])).

cnf(c_0_75,negated_conjecture,
    ( k4_xboole_0(X1,X1) = k4_xboole_0(X2,X2) ),
    inference(spm,[status(thm)],[c_0_71,c_0_71])).

cnf(c_0_76,negated_conjecture,
    ( k4_xboole_0(X1,k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk2_0))) = X1 ),
    inference(spm,[status(thm)],[c_0_23,c_0_72])).

cnf(c_0_77,plain,
    ( r1_xboole_0(X1,k2_xboole_0(X2,X3))
    | ~ r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_78,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,k4_xboole_0(X3,X2))) ),
    inference(spm,[status(thm)],[c_0_74,c_0_30])).

cnf(c_0_79,negated_conjecture,
    ( k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk2_0)) = k4_xboole_0(X1,X1) ),
    inference(spm,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_80,negated_conjecture,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X2)) = X1 ),
    inference(spm,[status(thm)],[c_0_69,c_0_71])).

cnf(c_0_81,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_38])).

cnf(c_0_82,negated_conjecture,
    ( r1_xboole_0(esk3_0,k2_xboole_0(X1,esk4_0))
    | ~ r1_xboole_0(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_77,c_0_24])).

cnf(c_0_83,negated_conjecture,
    ( r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(esk3_0,esk2_0)),esk3_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_80])).

cnf(c_0_84,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_23,c_0_81])).

cnf(c_0_85,negated_conjecture,
    ( r1_xboole_0(esk3_0,k2_xboole_0(k4_xboole_0(X1,esk3_0),esk4_0)) ),
    inference(spm,[status(thm)],[c_0_82,c_0_81])).

cnf(c_0_86,negated_conjecture,
    ( r1_xboole_0(esk2_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_83,c_0_84])).

cnf(c_0_87,negated_conjecture,
    ( r1_xboole_0(k2_xboole_0(k4_xboole_0(X1,esk3_0),esk4_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_85])).

cnf(c_0_88,negated_conjecture,
    ( k4_xboole_0(esk2_0,esk3_0) = esk2_0 ),
    inference(spm,[status(thm)],[c_0_23,c_0_86])).

cnf(c_0_89,negated_conjecture,
    ( ~ r1_xboole_0(k2_xboole_0(esk2_0,esk4_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_90,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_88]),c_0_89]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:52:59 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.39/0.57  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S03EI
% 0.39/0.57  # and selection function SelectLComplex.
% 0.39/0.57  #
% 0.39/0.57  # Preprocessing time       : 0.030 s
% 0.39/0.57  # Presaturation interreduction done
% 0.39/0.57  
% 0.39/0.57  # Proof found!
% 0.39/0.57  # SZS status Theorem
% 0.39/0.57  # SZS output start CNFRefutation
% 0.39/0.57  fof(t149_zfmisc_1, conjecture, ![X1, X2, X3, X4]:(((r1_tarski(k3_xboole_0(X1,X2),k1_tarski(X4))&r2_hidden(X4,X3))&r1_xboole_0(X3,X2))=>r1_xboole_0(k2_xboole_0(X1,X3),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t149_zfmisc_1)).
% 0.39/0.57  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 0.39/0.57  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.39/0.57  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.39/0.57  fof(t83_xboole_1, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k4_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 0.39/0.57  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.39/0.57  fof(t65_zfmisc_1, axiom, ![X1, X2]:(k4_xboole_0(X1,k1_tarski(X2))=X1<=>~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 0.39/0.57  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.39/0.57  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.39/0.57  fof(t79_xboole_1, axiom, ![X1, X2]:r1_xboole_0(k4_xboole_0(X1,X2),X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 0.39/0.57  fof(t106_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k4_xboole_0(X2,X3))=>(r1_tarski(X1,X2)&r1_xboole_0(X1,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 0.39/0.57  fof(t74_xboole_1, axiom, ![X1, X2, X3]:~((~(r1_xboole_0(X1,k3_xboole_0(X2,X3)))&r1_xboole_0(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_xboole_1)).
% 0.39/0.57  fof(t70_xboole_1, axiom, ![X1, X2, X3]:(~(((~(r1_xboole_0(X1,k2_xboole_0(X2,X3)))&r1_xboole_0(X1,X2))&r1_xboole_0(X1,X3)))&~((~((r1_xboole_0(X1,X2)&r1_xboole_0(X1,X3)))&r1_xboole_0(X1,k2_xboole_0(X2,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_xboole_1)).
% 0.39/0.57  fof(c_0_13, negated_conjecture, ~(![X1, X2, X3, X4]:(((r1_tarski(k3_xboole_0(X1,X2),k1_tarski(X4))&r2_hidden(X4,X3))&r1_xboole_0(X3,X2))=>r1_xboole_0(k2_xboole_0(X1,X3),X2))), inference(assume_negation,[status(cth)],[t149_zfmisc_1])).
% 0.39/0.57  fof(c_0_14, plain, ![X7, X8]:(~r1_xboole_0(X7,X8)|r1_xboole_0(X8,X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 0.39/0.57  fof(c_0_15, negated_conjecture, (((r1_tarski(k3_xboole_0(esk2_0,esk3_0),k1_tarski(esk5_0))&r2_hidden(esk5_0,esk4_0))&r1_xboole_0(esk4_0,esk3_0))&~r1_xboole_0(k2_xboole_0(esk2_0,esk4_0),esk3_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).
% 0.39/0.57  fof(c_0_16, plain, ![X5, X6]:k3_xboole_0(X5,X6)=k3_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.39/0.57  fof(c_0_17, plain, ![X18, X19]:k4_xboole_0(X18,k4_xboole_0(X18,X19))=k3_xboole_0(X18,X19), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.39/0.57  fof(c_0_18, plain, ![X28, X29]:((~r1_xboole_0(X28,X29)|k4_xboole_0(X28,X29)=X28)&(k4_xboole_0(X28,X29)!=X28|r1_xboole_0(X28,X29))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).
% 0.39/0.57  cnf(c_0_19, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.39/0.57  cnf(c_0_20, negated_conjecture, (r1_xboole_0(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.39/0.57  cnf(c_0_21, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.39/0.57  cnf(c_0_22, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.39/0.57  cnf(c_0_23, plain, (k4_xboole_0(X1,X2)=X1|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.39/0.57  cnf(c_0_24, negated_conjecture, (r1_xboole_0(esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.39/0.57  fof(c_0_25, plain, ![X9, X10, X12, X13, X14]:(((r2_hidden(esk1_2(X9,X10),X9)|r1_xboole_0(X9,X10))&(r2_hidden(esk1_2(X9,X10),X10)|r1_xboole_0(X9,X10)))&(~r2_hidden(X14,X12)|~r2_hidden(X14,X13)|~r1_xboole_0(X12,X13))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.39/0.57  fof(c_0_26, plain, ![X33, X34]:((k4_xboole_0(X33,k1_tarski(X34))!=X33|~r2_hidden(X34,X33))&(r2_hidden(X34,X33)|k4_xboole_0(X33,k1_tarski(X34))=X33)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_zfmisc_1])])])).
% 0.39/0.57  fof(c_0_27, plain, ![X30]:k2_tarski(X30,X30)=k1_tarski(X30), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.39/0.57  fof(c_0_28, plain, ![X31, X32]:k1_enumset1(X31,X31,X32)=k2_tarski(X31,X32), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.39/0.57  fof(c_0_29, plain, ![X26, X27]:r1_xboole_0(k4_xboole_0(X26,X27),X27), inference(variable_rename,[status(thm)],[t79_xboole_1])).
% 0.39/0.57  cnf(c_0_30, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k4_xboole_0(X2,k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21, c_0_22]), c_0_22])).
% 0.39/0.57  cnf(c_0_31, negated_conjecture, (k4_xboole_0(esk3_0,esk4_0)=esk3_0), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.39/0.57  cnf(c_0_32, negated_conjecture, (k4_xboole_0(esk4_0,esk3_0)=esk4_0), inference(spm,[status(thm)],[c_0_23, c_0_20])).
% 0.39/0.57  cnf(c_0_33, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.39/0.57  cnf(c_0_34, negated_conjecture, (r2_hidden(esk5_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.39/0.57  cnf(c_0_35, plain, (r2_hidden(X1,X2)|k4_xboole_0(X2,k1_tarski(X1))=X2), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.39/0.57  cnf(c_0_36, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.39/0.57  cnf(c_0_37, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.39/0.57  cnf(c_0_38, plain, (r1_xboole_0(k4_xboole_0(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.39/0.57  cnf(c_0_39, negated_conjecture, (k4_xboole_0(esk3_0,esk3_0)=k4_xboole_0(esk4_0,esk4_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32])).
% 0.39/0.57  cnf(c_0_40, negated_conjecture, (~r2_hidden(esk5_0,X1)|~r1_xboole_0(X1,esk4_0)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.39/0.57  cnf(c_0_41, plain, (k4_xboole_0(X2,k1_enumset1(X1,X1,X1))=X2|r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_36]), c_0_37])).
% 0.39/0.57  cnf(c_0_42, negated_conjecture, (r1_xboole_0(k4_xboole_0(esk4_0,esk4_0),esk3_0)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.39/0.57  cnf(c_0_43, negated_conjecture, (k4_xboole_0(X1,k1_enumset1(esk5_0,esk5_0,esk5_0))=X1|~r1_xboole_0(X1,esk4_0)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.39/0.57  cnf(c_0_44, negated_conjecture, (r1_xboole_0(esk3_0,k4_xboole_0(esk4_0,esk4_0))), inference(spm,[status(thm)],[c_0_19, c_0_42])).
% 0.39/0.57  cnf(c_0_45, negated_conjecture, (k4_xboole_0(esk3_0,k1_enumset1(esk5_0,esk5_0,esk5_0))=esk3_0), inference(spm,[status(thm)],[c_0_43, c_0_24])).
% 0.39/0.57  cnf(c_0_46, plain, (r2_hidden(esk1_2(X1,X2),X2)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.39/0.57  cnf(c_0_47, negated_conjecture, (k4_xboole_0(k4_xboole_0(esk4_0,esk4_0),esk3_0)=k4_xboole_0(esk4_0,esk4_0)), inference(spm,[status(thm)],[c_0_23, c_0_42])).
% 0.39/0.57  cnf(c_0_48, negated_conjecture, (k4_xboole_0(esk3_0,k4_xboole_0(esk4_0,esk4_0))=esk3_0), inference(spm,[status(thm)],[c_0_23, c_0_44])).
% 0.39/0.57  cnf(c_0_49, negated_conjecture, (r1_xboole_0(esk3_0,k1_enumset1(esk5_0,esk5_0,esk5_0))), inference(spm,[status(thm)],[c_0_38, c_0_45])).
% 0.39/0.57  cnf(c_0_50, plain, (r1_xboole_0(X1,X2)|~r2_hidden(esk1_2(X1,X2),X3)|~r1_xboole_0(X3,X2)), inference(spm,[status(thm)],[c_0_33, c_0_46])).
% 0.39/0.57  cnf(c_0_51, negated_conjecture, (k4_xboole_0(k4_xboole_0(esk4_0,esk4_0),k4_xboole_0(esk4_0,esk4_0))=k4_xboole_0(esk4_0,esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_47]), c_0_48]), c_0_39])).
% 0.39/0.57  fof(c_0_52, plain, ![X15, X16, X17]:((r1_tarski(X15,X16)|~r1_tarski(X15,k4_xboole_0(X16,X17)))&(r1_xboole_0(X15,X17)|~r1_tarski(X15,k4_xboole_0(X16,X17)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t106_xboole_1])])])).
% 0.39/0.57  cnf(c_0_53, negated_conjecture, (r1_xboole_0(k1_enumset1(esk5_0,esk5_0,esk5_0),esk3_0)), inference(spm,[status(thm)],[c_0_19, c_0_49])).
% 0.39/0.57  cnf(c_0_54, negated_conjecture, (r1_tarski(k3_xboole_0(esk2_0,esk3_0),k1_tarski(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.39/0.57  cnf(c_0_55, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(X2,X2)), inference(spm,[status(thm)],[c_0_50, c_0_46])).
% 0.39/0.57  cnf(c_0_56, negated_conjecture, (r1_xboole_0(k4_xboole_0(esk4_0,esk4_0),k4_xboole_0(esk4_0,esk4_0))), inference(spm,[status(thm)],[c_0_38, c_0_51])).
% 0.39/0.57  fof(c_0_57, plain, ![X23, X24, X25]:(r1_xboole_0(X23,k3_xboole_0(X24,X25))|~r1_xboole_0(X23,X24)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t74_xboole_1])])])).
% 0.39/0.57  cnf(c_0_58, plain, (r1_xboole_0(X1,X2)|~r1_tarski(X1,k4_xboole_0(X3,X2))), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.39/0.57  cnf(c_0_59, negated_conjecture, (k4_xboole_0(k1_enumset1(esk5_0,esk5_0,esk5_0),esk3_0)=k1_enumset1(esk5_0,esk5_0,esk5_0)), inference(spm,[status(thm)],[c_0_23, c_0_53])).
% 0.39/0.57  cnf(c_0_60, negated_conjecture, (r1_tarski(k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0)),k1_enumset1(esk5_0,esk5_0,esk5_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54, c_0_36]), c_0_37]), c_0_22])).
% 0.39/0.57  cnf(c_0_61, negated_conjecture, (r1_xboole_0(X1,k4_xboole_0(esk4_0,esk4_0))), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.39/0.57  cnf(c_0_62, plain, (r1_xboole_0(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.39/0.57  cnf(c_0_63, negated_conjecture, (r1_xboole_0(X1,esk3_0)|~r1_tarski(X1,k1_enumset1(esk5_0,esk5_0,esk5_0))), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.39/0.57  cnf(c_0_64, negated_conjecture, (r1_tarski(k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk2_0)),k1_enumset1(esk5_0,esk5_0,esk5_0))), inference(rw,[status(thm)],[c_0_60, c_0_30])).
% 0.39/0.57  cnf(c_0_65, negated_conjecture, (r1_xboole_0(k4_xboole_0(esk4_0,esk4_0),X1)), inference(spm,[status(thm)],[c_0_19, c_0_61])).
% 0.39/0.57  cnf(c_0_66, plain, (r1_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_62, c_0_22])).
% 0.39/0.57  cnf(c_0_67, negated_conjecture, (r1_xboole_0(k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk2_0)),esk3_0)), inference(spm,[status(thm)],[c_0_63, c_0_64])).
% 0.39/0.57  cnf(c_0_68, negated_conjecture, (k4_xboole_0(k4_xboole_0(esk4_0,esk4_0),X1)=k4_xboole_0(esk4_0,esk4_0)), inference(spm,[status(thm)],[c_0_23, c_0_65])).
% 0.39/0.57  cnf(c_0_69, negated_conjecture, (k4_xboole_0(X1,k4_xboole_0(esk4_0,esk4_0))=X1), inference(spm,[status(thm)],[c_0_23, c_0_61])).
% 0.39/0.57  cnf(c_0_70, negated_conjecture, (r1_xboole_0(k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk2_0)),k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,X1)))), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 0.39/0.57  cnf(c_0_71, negated_conjecture, (k4_xboole_0(esk4_0,esk4_0)=k4_xboole_0(X1,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_68]), c_0_69])).
% 0.39/0.57  cnf(c_0_72, negated_conjecture, (r1_xboole_0(X1,k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk2_0)))), inference(spm,[status(thm)],[c_0_55, c_0_70])).
% 0.39/0.57  fof(c_0_73, plain, ![X20, X21, X22]:((r1_xboole_0(X20,k2_xboole_0(X21,X22))|~r1_xboole_0(X20,X21)|~r1_xboole_0(X20,X22))&((r1_xboole_0(X20,X21)|~r1_xboole_0(X20,k2_xboole_0(X21,X22)))&(r1_xboole_0(X20,X22)|~r1_xboole_0(X20,k2_xboole_0(X21,X22))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t70_xboole_1])])])])).
% 0.39/0.57  cnf(c_0_74, plain, (r1_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,k4_xboole_0(X2,X3)))), inference(spm,[status(thm)],[c_0_66, c_0_38])).
% 0.39/0.57  cnf(c_0_75, negated_conjecture, (k4_xboole_0(X1,X1)=k4_xboole_0(X2,X2)), inference(spm,[status(thm)],[c_0_71, c_0_71])).
% 0.39/0.57  cnf(c_0_76, negated_conjecture, (k4_xboole_0(X1,k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk2_0)))=X1), inference(spm,[status(thm)],[c_0_23, c_0_72])).
% 0.39/0.57  cnf(c_0_77, plain, (r1_xboole_0(X1,k2_xboole_0(X2,X3))|~r1_xboole_0(X1,X2)|~r1_xboole_0(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_73])).
% 0.39/0.57  cnf(c_0_78, plain, (r1_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,k4_xboole_0(X3,X2)))), inference(spm,[status(thm)],[c_0_74, c_0_30])).
% 0.39/0.57  cnf(c_0_79, negated_conjecture, (k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk2_0))=k4_xboole_0(X1,X1)), inference(spm,[status(thm)],[c_0_75, c_0_76])).
% 0.39/0.57  cnf(c_0_80, negated_conjecture, (k4_xboole_0(X1,k4_xboole_0(X2,X2))=X1), inference(spm,[status(thm)],[c_0_69, c_0_71])).
% 0.39/0.57  cnf(c_0_81, plain, (r1_xboole_0(X1,k4_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_19, c_0_38])).
% 0.39/0.57  cnf(c_0_82, negated_conjecture, (r1_xboole_0(esk3_0,k2_xboole_0(X1,esk4_0))|~r1_xboole_0(esk3_0,X1)), inference(spm,[status(thm)],[c_0_77, c_0_24])).
% 0.39/0.57  cnf(c_0_83, negated_conjecture, (r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(esk3_0,esk2_0)),esk3_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_79]), c_0_80])).
% 0.39/0.57  cnf(c_0_84, plain, (k4_xboole_0(X1,k4_xboole_0(X2,X1))=X1), inference(spm,[status(thm)],[c_0_23, c_0_81])).
% 0.39/0.57  cnf(c_0_85, negated_conjecture, (r1_xboole_0(esk3_0,k2_xboole_0(k4_xboole_0(X1,esk3_0),esk4_0))), inference(spm,[status(thm)],[c_0_82, c_0_81])).
% 0.39/0.57  cnf(c_0_86, negated_conjecture, (r1_xboole_0(esk2_0,esk3_0)), inference(spm,[status(thm)],[c_0_83, c_0_84])).
% 0.39/0.57  cnf(c_0_87, negated_conjecture, (r1_xboole_0(k2_xboole_0(k4_xboole_0(X1,esk3_0),esk4_0),esk3_0)), inference(spm,[status(thm)],[c_0_19, c_0_85])).
% 0.39/0.57  cnf(c_0_88, negated_conjecture, (k4_xboole_0(esk2_0,esk3_0)=esk2_0), inference(spm,[status(thm)],[c_0_23, c_0_86])).
% 0.39/0.57  cnf(c_0_89, negated_conjecture, (~r1_xboole_0(k2_xboole_0(esk2_0,esk4_0),esk3_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.39/0.57  cnf(c_0_90, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_88]), c_0_89]), ['proof']).
% 0.39/0.57  # SZS output end CNFRefutation
% 0.39/0.57  # Proof object total steps             : 91
% 0.39/0.57  # Proof object clause steps            : 64
% 0.39/0.57  # Proof object formula steps           : 27
% 0.39/0.57  # Proof object conjectures             : 45
% 0.39/0.57  # Proof object clause conjectures      : 42
% 0.39/0.57  # Proof object formula conjectures     : 3
% 0.39/0.57  # Proof object initial clauses used    : 17
% 0.39/0.57  # Proof object initial formulas used   : 13
% 0.39/0.57  # Proof object generating inferences   : 42
% 0.39/0.57  # Proof object simplifying inferences  : 15
% 0.39/0.57  # Training examples: 0 positive, 0 negative
% 0.39/0.57  # Parsed axioms                        : 13
% 0.39/0.57  # Removed by relevancy pruning/SinE    : 0
% 0.39/0.57  # Initial clauses                      : 23
% 0.39/0.57  # Removed in clause preprocessing      : 3
% 0.39/0.57  # Initial clauses in saturation        : 20
% 0.39/0.57  # Processed clauses                    : 2289
% 0.39/0.57  # ...of these trivial                  : 235
% 0.39/0.57  # ...subsumed                          : 1176
% 0.39/0.57  # ...remaining for further processing  : 878
% 0.39/0.57  # Other redundant clauses eliminated   : 14
% 0.39/0.57  # Clauses deleted for lack of memory   : 0
% 0.39/0.57  # Backward-subsumed                    : 18
% 0.39/0.57  # Backward-rewritten                   : 66
% 0.39/0.57  # Generated clauses                    : 23639
% 0.39/0.57  # ...of the previous two non-trivial   : 13559
% 0.39/0.57  # Contextual simplify-reflections      : 0
% 0.39/0.57  # Paramodulations                      : 23625
% 0.39/0.57  # Factorizations                       : 0
% 0.39/0.57  # Equation resolutions                 : 14
% 0.39/0.57  # Propositional unsat checks           : 0
% 0.39/0.57  #    Propositional check models        : 0
% 0.39/0.57  #    Propositional check unsatisfiable : 0
% 0.39/0.57  #    Propositional clauses             : 0
% 0.39/0.57  #    Propositional clauses after purity: 0
% 0.39/0.57  #    Propositional unsat core size     : 0
% 0.39/0.57  #    Propositional preprocessing time  : 0.000
% 0.39/0.57  #    Propositional encoding time       : 0.000
% 0.39/0.57  #    Propositional solver time         : 0.000
% 0.39/0.57  #    Success case prop preproc time    : 0.000
% 0.39/0.57  #    Success case prop encoding time   : 0.000
% 0.39/0.57  #    Success case prop solver time     : 0.000
% 0.39/0.57  # Current number of processed clauses  : 773
% 0.39/0.57  #    Positive orientable unit clauses  : 559
% 0.39/0.57  #    Positive unorientable unit clauses: 3
% 0.39/0.57  #    Negative unit clauses             : 77
% 0.39/0.57  #    Non-unit-clauses                  : 134
% 0.39/0.57  # Current number of unprocessed clauses: 11095
% 0.39/0.57  # ...number of literals in the above   : 14844
% 0.39/0.57  # Current number of archived formulas  : 0
% 0.39/0.57  # Current number of archived clauses   : 107
% 0.39/0.57  # Clause-clause subsumption calls (NU) : 2632
% 0.39/0.57  # Rec. Clause-clause subsumption calls : 2572
% 0.39/0.57  # Non-unit clause-clause subsumptions  : 424
% 0.39/0.57  # Unit Clause-clause subsumption calls : 1045
% 0.39/0.57  # Rewrite failures with RHS unbound    : 122
% 0.39/0.57  # BW rewrite match attempts            : 2622
% 0.39/0.57  # BW rewrite match successes           : 84
% 0.39/0.57  # Condensation attempts                : 0
% 0.39/0.57  # Condensation successes               : 0
% 0.39/0.57  # Termbank termtop insertions          : 393292
% 0.39/0.57  
% 0.39/0.57  # -------------------------------------------------
% 0.39/0.57  # User time                : 0.209 s
% 0.39/0.57  # System time              : 0.015 s
% 0.39/0.57  # Total time               : 0.224 s
% 0.39/0.57  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
