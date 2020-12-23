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
% DateTime   : Thu Dec  3 11:00:06 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 359 expanded)
%              Number of clauses        :   37 ( 150 expanded)
%              Number of leaves         :   16 ( 103 expanded)
%              Depth                    :   12
%              Number of atoms          :   99 ( 420 expanded)
%              Number of equality atoms :   75 ( 370 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal clause size      :    9 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(d6_xboole_0,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t52_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(X1,k4_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t90_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_enumset1)).

fof(l36_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(X1,k3_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l36_xboole_1)).

fof(t92_xboole_1,axiom,(
    ! [X1] : k5_xboole_0(X1,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(t47_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(t51_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t103_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ~ ( r1_tarski(X1,k2_zfmisc_1(X2,X3))
        & r2_hidden(X4,X1)
        & ! [X5,X6] :
            ~ ( r2_hidden(X5,X2)
              & r2_hidden(X6,X3)
              & X4 = k4_tarski(X5,X6) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_zfmisc_1)).

fof(t67_mcart_1,conjecture,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k2_zfmisc_1(X2,X3))
     => ( X1 != k1_mcart_1(X1)
        & X1 != k2_mcart_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_mcart_1)).

fof(t20_mcart_1,axiom,(
    ! [X1] :
      ( ? [X2,X3] : X1 = k4_tarski(X2,X3)
     => ( X1 != k1_mcart_1(X1)
        & X1 != k2_mcart_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).

fof(c_0_16,plain,(
    ! [X35,X36] : k3_tarski(k2_tarski(X35,X36)) = k2_xboole_0(X35,X36) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_17,plain,(
    ! [X26,X27] : k1_enumset1(X26,X26,X27) = k2_tarski(X26,X27) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_18,plain,(
    ! [X7,X8] : k5_xboole_0(X7,X8) = k2_xboole_0(k4_xboole_0(X7,X8),k4_xboole_0(X8,X7)) ),
    inference(variable_rename,[status(thm)],[d6_xboole_0])).

cnf(c_0_19,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_21,plain,(
    ! [X28,X29,X30] : k2_enumset1(X28,X28,X29,X30) = k1_enumset1(X28,X29,X30) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_22,plain,(
    ! [X20,X21,X22] : k4_xboole_0(X20,k4_xboole_0(X21,X22)) = k2_xboole_0(k4_xboole_0(X20,X21),k3_xboole_0(X20,X22)) ),
    inference(variable_rename,[status(thm)],[t52_xboole_1])).

fof(c_0_23,plain,(
    ! [X16,X17] : k4_xboole_0(X16,k4_xboole_0(X16,X17)) = k3_xboole_0(X16,X17) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_24,plain,(
    ! [X31,X32,X33,X34] : k6_enumset1(X31,X31,X31,X31,X31,X32,X33,X34) = k2_enumset1(X31,X32,X33,X34) ),
    inference(variable_rename,[status(thm)],[t90_enumset1])).

fof(c_0_25,plain,(
    ! [X9,X10,X11] : k4_xboole_0(X9,k3_xboole_0(X10,X11)) = k2_xboole_0(k4_xboole_0(X9,X10),k4_xboole_0(X9,X11)) ),
    inference(variable_rename,[status(thm)],[l36_xboole_1])).

fof(c_0_26,plain,(
    ! [X23] : k5_xboole_0(X23,X23) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t92_xboole_1])).

cnf(c_0_27,plain,
    ( k5_xboole_0(X1,X2) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_28,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_29,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_30,plain,(
    ! [X14,X15] : k4_xboole_0(X14,k3_xboole_0(X14,X15)) = k4_xboole_0(X14,X15) ),
    inference(variable_rename,[status(thm)],[t47_xboole_1])).

fof(c_0_31,plain,(
    ! [X18,X19] : k2_xboole_0(k3_xboole_0(X18,X19),k4_xboole_0(X18,X19)) = X18 ),
    inference(variable_rename,[status(thm)],[t51_xboole_1])).

fof(c_0_32,plain,(
    ! [X24,X25] : k2_tarski(X24,X25) = k2_tarski(X25,X24) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

cnf(c_0_33,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_34,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_35,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_36,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_37,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_38,plain,
    ( k5_xboole_0(X1,X2) = k3_tarski(k2_enumset1(k4_xboole_0(X1,X2),k4_xboole_0(X1,X2),k4_xboole_0(X1,X2),k4_xboole_0(X2,X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_28]),c_0_29])).

cnf(c_0_39,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_40,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_41,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_42,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X3)) = k3_tarski(k6_enumset1(k4_xboole_0(X1,X2),k4_xboole_0(X1,X2),k4_xboole_0(X1,X2),k4_xboole_0(X1,X2),k4_xboole_0(X1,X2),k4_xboole_0(X1,X2),k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X3)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_28]),c_0_29]),c_0_34]),c_0_35])).

cnf(c_0_43,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))) = k3_tarski(k6_enumset1(k4_xboole_0(X1,X2),k4_xboole_0(X1,X2),k4_xboole_0(X1,X2),k4_xboole_0(X1,X2),k4_xboole_0(X1,X2),k4_xboole_0(X1,X2),k4_xboole_0(X1,X2),k4_xboole_0(X1,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_28]),c_0_29]),c_0_34]),c_0_35])).

cnf(c_0_44,plain,
    ( k3_tarski(k6_enumset1(k4_xboole_0(X1,X1),k4_xboole_0(X1,X1),k4_xboole_0(X1,X1),k4_xboole_0(X1,X1),k4_xboole_0(X1,X1),k4_xboole_0(X1,X1),k4_xboole_0(X1,X1),k4_xboole_0(X1,X1))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_38]),c_0_35])).

cnf(c_0_45,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_39,c_0_34])).

fof(c_0_46,plain,(
    ! [X12,X13] : r1_tarski(k4_xboole_0(X12,X13),X12) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

cnf(c_0_47,plain,
    ( k3_tarski(k6_enumset1(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,X2))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_28]),c_0_29]),c_0_34]),c_0_34]),c_0_34]),c_0_35])).

cnf(c_0_48,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2) = k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_20]),c_0_20]),c_0_29]),c_0_29]),c_0_35]),c_0_35])).

cnf(c_0_49,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X1,X3)))) = k4_xboole_0(X1,k4_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_50,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44,c_0_43]),c_0_45])).

fof(c_0_51,plain,(
    ! [X37,X38,X39,X40] :
      ( ( r2_hidden(esk1_4(X37,X38,X39,X40),X38)
        | ~ r1_tarski(X37,k2_zfmisc_1(X38,X39))
        | ~ r2_hidden(X40,X37) )
      & ( r2_hidden(esk2_4(X37,X38,X39,X40),X39)
        | ~ r1_tarski(X37,k2_zfmisc_1(X38,X39))
        | ~ r2_hidden(X40,X37) )
      & ( X40 = k4_tarski(esk1_4(X37,X38,X39,X40),esk2_4(X37,X38,X39,X40))
        | ~ r1_tarski(X37,k2_zfmisc_1(X38,X39))
        | ~ r2_hidden(X40,X37) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t103_zfmisc_1])])])])).

cnf(c_0_52,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_53,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_48]),c_0_43]),c_0_49]),c_0_50])).

fof(c_0_54,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( r2_hidden(X1,k2_zfmisc_1(X2,X3))
       => ( X1 != k1_mcart_1(X1)
          & X1 != k2_mcart_1(X1) ) ) ),
    inference(assume_negation,[status(cth)],[t67_mcart_1])).

fof(c_0_55,plain,(
    ! [X43,X44,X45] :
      ( ( X43 != k1_mcart_1(X43)
        | X43 != k4_tarski(X44,X45) )
      & ( X43 != k2_mcart_1(X43)
        | X43 != k4_tarski(X44,X45) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_mcart_1])])])])).

cnf(c_0_56,plain,
    ( X1 = k4_tarski(esk1_4(X2,X3,X4,X1),esk2_4(X2,X3,X4,X1))
    | ~ r1_tarski(X2,k2_zfmisc_1(X3,X4))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_57,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

fof(c_0_58,negated_conjecture,
    ( r2_hidden(esk3_0,k2_zfmisc_1(esk4_0,esk5_0))
    & ( esk3_0 = k1_mcart_1(esk3_0)
      | esk3_0 = k2_mcart_1(esk3_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_54])])])).

cnf(c_0_59,plain,
    ( X1 != k1_mcart_1(X1)
    | X1 != k4_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_60,plain,
    ( k4_tarski(esk1_4(k2_zfmisc_1(X1,X2),X1,X2,X3),esk2_4(k2_zfmisc_1(X1,X2),X1,X2,X3)) = X3
    | ~ r2_hidden(X3,k2_zfmisc_1(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_61,negated_conjecture,
    ( r2_hidden(esk3_0,k2_zfmisc_1(esk4_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_62,plain,
    ( X1 != k2_mcart_1(X1)
    | X1 != k4_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_63,plain,
    ( k1_mcart_1(k4_tarski(X1,X2)) != k4_tarski(X1,X2) ),
    inference(er,[status(thm)],[c_0_59])).

cnf(c_0_64,negated_conjecture,
    ( k4_tarski(esk1_4(k2_zfmisc_1(esk4_0,esk5_0),esk4_0,esk5_0,esk3_0),esk2_4(k2_zfmisc_1(esk4_0,esk5_0),esk4_0,esk5_0,esk3_0)) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_65,plain,
    ( k2_mcart_1(k4_tarski(X1,X2)) != k4_tarski(X1,X2) ),
    inference(er,[status(thm)],[c_0_62])).

cnf(c_0_66,negated_conjecture,
    ( esk3_0 = k1_mcart_1(esk3_0)
    | esk3_0 = k2_mcart_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_67,negated_conjecture,
    ( k1_mcart_1(esk3_0) != esk3_0 ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_68,negated_conjecture,
    ( k2_mcart_1(esk3_0) != esk3_0 ),
    inference(spm,[status(thm)],[c_0_65,c_0_64])).

cnf(c_0_69,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[c_0_66,c_0_67]),c_0_68]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:38:47 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 0.12/0.38  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.12/0.38  # and selection function SelectNegativeLiterals.
% 0.12/0.38  #
% 0.12/0.38  # Preprocessing time       : 0.027 s
% 0.12/0.38  # Presaturation interreduction done
% 0.12/0.38  
% 0.12/0.38  # Proof found!
% 0.12/0.38  # SZS status Theorem
% 0.12/0.38  # SZS output start CNFRefutation
% 0.12/0.38  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.12/0.38  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.12/0.38  fof(d6_xboole_0, axiom, ![X1, X2]:k5_xboole_0(X1,X2)=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_xboole_0)).
% 0.12/0.38  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.12/0.38  fof(t52_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(X1,k4_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_xboole_1)).
% 0.12/0.38  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.12/0.38  fof(t90_enumset1, axiom, ![X1, X2, X3, X4]:k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_enumset1)).
% 0.12/0.38  fof(l36_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(X1,k3_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l36_xboole_1)).
% 0.12/0.38  fof(t92_xboole_1, axiom, ![X1]:k5_xboole_0(X1,X1)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 0.12/0.38  fof(t47_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 0.12/0.38  fof(t51_xboole_1, axiom, ![X1, X2]:k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 0.12/0.38  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 0.12/0.38  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.12/0.38  fof(t103_zfmisc_1, axiom, ![X1, X2, X3, X4]:~(((r1_tarski(X1,k2_zfmisc_1(X2,X3))&r2_hidden(X4,X1))&![X5, X6]:~(((r2_hidden(X5,X2)&r2_hidden(X6,X3))&X4=k4_tarski(X5,X6))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t103_zfmisc_1)).
% 0.12/0.38  fof(t67_mcart_1, conjecture, ![X1, X2, X3]:(r2_hidden(X1,k2_zfmisc_1(X2,X3))=>(X1!=k1_mcart_1(X1)&X1!=k2_mcart_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_mcart_1)).
% 0.12/0.38  fof(t20_mcart_1, axiom, ![X1]:(?[X2, X3]:X1=k4_tarski(X2,X3)=>(X1!=k1_mcart_1(X1)&X1!=k2_mcart_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_mcart_1)).
% 0.12/0.38  fof(c_0_16, plain, ![X35, X36]:k3_tarski(k2_tarski(X35,X36))=k2_xboole_0(X35,X36), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.12/0.38  fof(c_0_17, plain, ![X26, X27]:k1_enumset1(X26,X26,X27)=k2_tarski(X26,X27), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.12/0.38  fof(c_0_18, plain, ![X7, X8]:k5_xboole_0(X7,X8)=k2_xboole_0(k4_xboole_0(X7,X8),k4_xboole_0(X8,X7)), inference(variable_rename,[status(thm)],[d6_xboole_0])).
% 0.12/0.38  cnf(c_0_19, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.38  cnf(c_0_20, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.12/0.38  fof(c_0_21, plain, ![X28, X29, X30]:k2_enumset1(X28,X28,X29,X30)=k1_enumset1(X28,X29,X30), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.12/0.38  fof(c_0_22, plain, ![X20, X21, X22]:k4_xboole_0(X20,k4_xboole_0(X21,X22))=k2_xboole_0(k4_xboole_0(X20,X21),k3_xboole_0(X20,X22)), inference(variable_rename,[status(thm)],[t52_xboole_1])).
% 0.12/0.38  fof(c_0_23, plain, ![X16, X17]:k4_xboole_0(X16,k4_xboole_0(X16,X17))=k3_xboole_0(X16,X17), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.12/0.38  fof(c_0_24, plain, ![X31, X32, X33, X34]:k6_enumset1(X31,X31,X31,X31,X31,X32,X33,X34)=k2_enumset1(X31,X32,X33,X34), inference(variable_rename,[status(thm)],[t90_enumset1])).
% 0.12/0.38  fof(c_0_25, plain, ![X9, X10, X11]:k4_xboole_0(X9,k3_xboole_0(X10,X11))=k2_xboole_0(k4_xboole_0(X9,X10),k4_xboole_0(X9,X11)), inference(variable_rename,[status(thm)],[l36_xboole_1])).
% 0.12/0.38  fof(c_0_26, plain, ![X23]:k5_xboole_0(X23,X23)=k1_xboole_0, inference(variable_rename,[status(thm)],[t92_xboole_1])).
% 0.12/0.38  cnf(c_0_27, plain, (k5_xboole_0(X1,X2)=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.12/0.38  cnf(c_0_28, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_19, c_0_20])).
% 0.12/0.38  cnf(c_0_29, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.12/0.38  fof(c_0_30, plain, ![X14, X15]:k4_xboole_0(X14,k3_xboole_0(X14,X15))=k4_xboole_0(X14,X15), inference(variable_rename,[status(thm)],[t47_xboole_1])).
% 0.12/0.38  fof(c_0_31, plain, ![X18, X19]:k2_xboole_0(k3_xboole_0(X18,X19),k4_xboole_0(X18,X19))=X18, inference(variable_rename,[status(thm)],[t51_xboole_1])).
% 0.12/0.38  fof(c_0_32, plain, ![X24, X25]:k2_tarski(X24,X25)=k2_tarski(X25,X24), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 0.12/0.38  cnf(c_0_33, plain, (k4_xboole_0(X1,k4_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.12/0.38  cnf(c_0_34, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.12/0.38  cnf(c_0_35, plain, (k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.12/0.38  cnf(c_0_36, plain, (k4_xboole_0(X1,k3_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.12/0.38  cnf(c_0_37, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.12/0.38  cnf(c_0_38, plain, (k5_xboole_0(X1,X2)=k3_tarski(k2_enumset1(k4_xboole_0(X1,X2),k4_xboole_0(X1,X2),k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27, c_0_28]), c_0_29])).
% 0.12/0.38  cnf(c_0_39, plain, (k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.12/0.38  cnf(c_0_40, plain, (k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.12/0.38  cnf(c_0_41, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.12/0.38  cnf(c_0_42, plain, (k4_xboole_0(X1,k4_xboole_0(X2,X3))=k3_tarski(k6_enumset1(k4_xboole_0(X1,X2),k4_xboole_0(X1,X2),k4_xboole_0(X1,X2),k4_xboole_0(X1,X2),k4_xboole_0(X1,X2),k4_xboole_0(X1,X2),k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X3))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33, c_0_28]), c_0_29]), c_0_34]), c_0_35])).
% 0.12/0.38  cnf(c_0_43, plain, (k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))=k3_tarski(k6_enumset1(k4_xboole_0(X1,X2),k4_xboole_0(X1,X2),k4_xboole_0(X1,X2),k4_xboole_0(X1,X2),k4_xboole_0(X1,X2),k4_xboole_0(X1,X2),k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36, c_0_28]), c_0_29]), c_0_34]), c_0_35])).
% 0.12/0.38  cnf(c_0_44, plain, (k3_tarski(k6_enumset1(k4_xboole_0(X1,X1),k4_xboole_0(X1,X1),k4_xboole_0(X1,X1),k4_xboole_0(X1,X1),k4_xboole_0(X1,X1),k4_xboole_0(X1,X1),k4_xboole_0(X1,X1),k4_xboole_0(X1,X1)))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37, c_0_38]), c_0_35])).
% 0.12/0.38  cnf(c_0_45, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2)))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_39, c_0_34])).
% 0.12/0.38  fof(c_0_46, plain, ![X12, X13]:r1_tarski(k4_xboole_0(X12,X13),X12), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.12/0.38  cnf(c_0_47, plain, (k3_tarski(k6_enumset1(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,X2)))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_28]), c_0_29]), c_0_34]), c_0_34]), c_0_34]), c_0_35])).
% 0.12/0.38  cnf(c_0_48, plain, (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)=k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_20]), c_0_20]), c_0_29]), c_0_29]), c_0_35]), c_0_35])).
% 0.12/0.38  cnf(c_0_49, plain, (k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X1,X3))))=k4_xboole_0(X1,k4_xboole_0(X2,X3))), inference(rw,[status(thm)],[c_0_42, c_0_43])).
% 0.12/0.38  cnf(c_0_50, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44, c_0_43]), c_0_45])).
% 0.12/0.38  fof(c_0_51, plain, ![X37, X38, X39, X40]:(((r2_hidden(esk1_4(X37,X38,X39,X40),X38)|(~r1_tarski(X37,k2_zfmisc_1(X38,X39))|~r2_hidden(X40,X37)))&(r2_hidden(esk2_4(X37,X38,X39,X40),X39)|(~r1_tarski(X37,k2_zfmisc_1(X38,X39))|~r2_hidden(X40,X37))))&(X40=k4_tarski(esk1_4(X37,X38,X39,X40),esk2_4(X37,X38,X39,X40))|(~r1_tarski(X37,k2_zfmisc_1(X38,X39))|~r2_hidden(X40,X37)))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t103_zfmisc_1])])])])).
% 0.12/0.38  cnf(c_0_52, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.12/0.38  cnf(c_0_53, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47, c_0_48]), c_0_43]), c_0_49]), c_0_50])).
% 0.12/0.38  fof(c_0_54, negated_conjecture, ~(![X1, X2, X3]:(r2_hidden(X1,k2_zfmisc_1(X2,X3))=>(X1!=k1_mcart_1(X1)&X1!=k2_mcart_1(X1)))), inference(assume_negation,[status(cth)],[t67_mcart_1])).
% 0.12/0.38  fof(c_0_55, plain, ![X43, X44, X45]:((X43!=k1_mcart_1(X43)|X43!=k4_tarski(X44,X45))&(X43!=k2_mcart_1(X43)|X43!=k4_tarski(X44,X45))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_mcart_1])])])])).
% 0.12/0.38  cnf(c_0_56, plain, (X1=k4_tarski(esk1_4(X2,X3,X4,X1),esk2_4(X2,X3,X4,X1))|~r1_tarski(X2,k2_zfmisc_1(X3,X4))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.12/0.38  cnf(c_0_57, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.12/0.38  fof(c_0_58, negated_conjecture, (r2_hidden(esk3_0,k2_zfmisc_1(esk4_0,esk5_0))&(esk3_0=k1_mcart_1(esk3_0)|esk3_0=k2_mcart_1(esk3_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_54])])])).
% 0.12/0.38  cnf(c_0_59, plain, (X1!=k1_mcart_1(X1)|X1!=k4_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.12/0.38  cnf(c_0_60, plain, (k4_tarski(esk1_4(k2_zfmisc_1(X1,X2),X1,X2,X3),esk2_4(k2_zfmisc_1(X1,X2),X1,X2,X3))=X3|~r2_hidden(X3,k2_zfmisc_1(X1,X2))), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.12/0.38  cnf(c_0_61, negated_conjecture, (r2_hidden(esk3_0,k2_zfmisc_1(esk4_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.12/0.38  cnf(c_0_62, plain, (X1!=k2_mcart_1(X1)|X1!=k4_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.12/0.38  cnf(c_0_63, plain, (k1_mcart_1(k4_tarski(X1,X2))!=k4_tarski(X1,X2)), inference(er,[status(thm)],[c_0_59])).
% 0.12/0.38  cnf(c_0_64, negated_conjecture, (k4_tarski(esk1_4(k2_zfmisc_1(esk4_0,esk5_0),esk4_0,esk5_0,esk3_0),esk2_4(k2_zfmisc_1(esk4_0,esk5_0),esk4_0,esk5_0,esk3_0))=esk3_0), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.12/0.38  cnf(c_0_65, plain, (k2_mcart_1(k4_tarski(X1,X2))!=k4_tarski(X1,X2)), inference(er,[status(thm)],[c_0_62])).
% 0.12/0.38  cnf(c_0_66, negated_conjecture, (esk3_0=k1_mcart_1(esk3_0)|esk3_0=k2_mcart_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.12/0.38  cnf(c_0_67, negated_conjecture, (k1_mcart_1(esk3_0)!=esk3_0), inference(spm,[status(thm)],[c_0_63, c_0_64])).
% 0.12/0.38  cnf(c_0_68, negated_conjecture, (k2_mcart_1(esk3_0)!=esk3_0), inference(spm,[status(thm)],[c_0_65, c_0_64])).
% 0.12/0.38  cnf(c_0_69, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[c_0_66, c_0_67]), c_0_68]), ['proof']).
% 0.12/0.38  # SZS output end CNFRefutation
% 0.12/0.38  # Proof object total steps             : 70
% 0.12/0.38  # Proof object clause steps            : 37
% 0.12/0.38  # Proof object formula steps           : 33
% 0.12/0.38  # Proof object conjectures             : 9
% 0.12/0.38  # Proof object clause conjectures      : 6
% 0.12/0.38  # Proof object formula conjectures     : 3
% 0.12/0.38  # Proof object initial clauses used    : 18
% 0.12/0.38  # Proof object initial formulas used   : 16
% 0.12/0.38  # Proof object generating inferences   : 5
% 0.12/0.38  # Proof object simplifying inferences  : 37
% 0.12/0.38  # Training examples: 0 positive, 0 negative
% 0.12/0.38  # Parsed axioms                        : 16
% 0.12/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.38  # Initial clauses                      : 20
% 0.12/0.38  # Removed in clause preprocessing      : 6
% 0.12/0.38  # Initial clauses in saturation        : 14
% 0.12/0.38  # Processed clauses                    : 142
% 0.12/0.38  # ...of these trivial                  : 35
% 0.12/0.38  # ...subsumed                          : 25
% 0.12/0.38  # ...remaining for further processing  : 81
% 0.12/0.38  # Other redundant clauses eliminated   : 2
% 0.12/0.38  # Clauses deleted for lack of memory   : 0
% 0.12/0.38  # Backward-subsumed                    : 0
% 0.12/0.38  # Backward-rewritten                   : 5
% 0.12/0.38  # Generated clauses                    : 2708
% 0.12/0.38  # ...of the previous two non-trivial   : 940
% 0.12/0.38  # Contextual simplify-reflections      : 0
% 0.12/0.38  # Paramodulations                      : 2705
% 0.12/0.38  # Factorizations                       : 0
% 0.12/0.38  # Equation resolutions                 : 2
% 0.12/0.38  # Propositional unsat checks           : 0
% 0.12/0.38  #    Propositional check models        : 0
% 0.12/0.38  #    Propositional check unsatisfiable : 0
% 0.12/0.38  #    Propositional clauses             : 0
% 0.12/0.38  #    Propositional clauses after purity: 0
% 0.12/0.38  #    Propositional unsat core size     : 0
% 0.12/0.38  #    Propositional preprocessing time  : 0.000
% 0.12/0.38  #    Propositional encoding time       : 0.000
% 0.12/0.38  #    Propositional solver time         : 0.000
% 0.12/0.38  #    Success case prop preproc time    : 0.000
% 0.12/0.38  #    Success case prop encoding time   : 0.000
% 0.12/0.38  #    Success case prop solver time     : 0.000
% 0.12/0.38  # Current number of processed clauses  : 59
% 0.12/0.38  #    Positive orientable unit clauses  : 41
% 0.12/0.38  #    Positive unorientable unit clauses: 3
% 0.12/0.38  #    Negative unit clauses             : 4
% 0.12/0.38  #    Non-unit-clauses                  : 11
% 0.12/0.38  # Current number of unprocessed clauses: 811
% 0.12/0.38  # ...number of literals in the above   : 826
% 0.12/0.38  # Current number of archived formulas  : 0
% 0.12/0.38  # Current number of archived clauses   : 26
% 0.12/0.38  # Clause-clause subsumption calls (NU) : 37
% 0.12/0.38  # Rec. Clause-clause subsumption calls : 37
% 0.12/0.38  # Non-unit clause-clause subsumptions  : 24
% 0.12/0.38  # Unit Clause-clause subsumption calls : 30
% 0.12/0.38  # Rewrite failures with RHS unbound    : 0
% 0.12/0.38  # BW rewrite match attempts            : 158
% 0.12/0.38  # BW rewrite match successes           : 18
% 0.12/0.38  # Condensation attempts                : 0
% 0.12/0.38  # Condensation successes               : 0
% 0.12/0.38  # Termbank termtop insertions          : 21416
% 0.12/0.38  
% 0.12/0.38  # -------------------------------------------------
% 0.12/0.38  # User time                : 0.047 s
% 0.12/0.38  # System time              : 0.006 s
% 0.12/0.38  # Total time               : 0.053 s
% 0.12/0.38  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
