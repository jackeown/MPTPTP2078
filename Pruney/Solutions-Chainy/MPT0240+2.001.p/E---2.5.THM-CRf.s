%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:39:28 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   45 ( 273 expanded)
%              Number of clauses        :   34 ( 131 expanded)
%              Number of leaves         :    5 (  68 expanded)
%              Depth                    :   15
%              Number of atoms          :  162 ( 759 expanded)
%              Number of equality atoms :  115 ( 557 expanded)
%              Maximal formula depth    :   23 (   4 average)
%              Maximal clause size      :   28 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(t82_enumset1,axiom,(
    ! [X1] : k2_enumset1(X1,X1,X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_enumset1)).

fof(t35_zfmisc_1,conjecture,(
    ! [X1,X2] : k2_zfmisc_1(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(k4_tarski(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_zfmisc_1)).

fof(d2_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_zfmisc_1(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ? [X5,X6] :
              ( r2_hidden(X5,X1)
              & r2_hidden(X6,X2)
              & X4 = k4_tarski(X5,X6) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(t34_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(k1_tarski(X3),k1_tarski(X4)))
    <=> ( X1 = X3
        & X2 = X4 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_zfmisc_1)).

fof(c_0_5,plain,(
    ! [X7,X8,X9,X10,X11,X12] :
      ( ( ~ r2_hidden(X9,X8)
        | X9 = X7
        | X8 != k1_tarski(X7) )
      & ( X10 != X7
        | r2_hidden(X10,X8)
        | X8 != k1_tarski(X7) )
      & ( ~ r2_hidden(esk1_2(X11,X12),X12)
        | esk1_2(X11,X12) != X11
        | X12 = k1_tarski(X11) )
      & ( r2_hidden(esk1_2(X11,X12),X12)
        | esk1_2(X11,X12) = X11
        | X12 = k1_tarski(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

fof(c_0_6,plain,(
    ! [X14] : k2_enumset1(X14,X14,X14,X14) = k1_tarski(X14) ),
    inference(variable_rename,[status(thm)],[t82_enumset1])).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1,X2] : k2_zfmisc_1(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(k4_tarski(X1,X2)) ),
    inference(assume_negation,[status(cth)],[t35_zfmisc_1])).

cnf(c_0_8,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( k2_enumset1(X1,X1,X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_10,negated_conjecture,(
    k2_zfmisc_1(k1_tarski(esk7_0),k1_tarski(esk8_0)) != k1_tarski(k4_tarski(esk7_0,esk8_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

cnf(c_0_11,plain,
    ( X1 = X3
    | X2 != k2_enumset1(X3,X3,X3,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_8,c_0_9])).

cnf(c_0_12,plain,
    ( r2_hidden(esk1_2(X1,X2),X2)
    | esk1_2(X1,X2) = X1
    | X2 = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_13,plain,(
    ! [X15,X16,X17,X18,X21,X22,X23,X24,X25,X26,X28,X29] :
      ( ( r2_hidden(esk2_4(X15,X16,X17,X18),X15)
        | ~ r2_hidden(X18,X17)
        | X17 != k2_zfmisc_1(X15,X16) )
      & ( r2_hidden(esk3_4(X15,X16,X17,X18),X16)
        | ~ r2_hidden(X18,X17)
        | X17 != k2_zfmisc_1(X15,X16) )
      & ( X18 = k4_tarski(esk2_4(X15,X16,X17,X18),esk3_4(X15,X16,X17,X18))
        | ~ r2_hidden(X18,X17)
        | X17 != k2_zfmisc_1(X15,X16) )
      & ( ~ r2_hidden(X22,X15)
        | ~ r2_hidden(X23,X16)
        | X21 != k4_tarski(X22,X23)
        | r2_hidden(X21,X17)
        | X17 != k2_zfmisc_1(X15,X16) )
      & ( ~ r2_hidden(esk4_3(X24,X25,X26),X26)
        | ~ r2_hidden(X28,X24)
        | ~ r2_hidden(X29,X25)
        | esk4_3(X24,X25,X26) != k4_tarski(X28,X29)
        | X26 = k2_zfmisc_1(X24,X25) )
      & ( r2_hidden(esk5_3(X24,X25,X26),X24)
        | r2_hidden(esk4_3(X24,X25,X26),X26)
        | X26 = k2_zfmisc_1(X24,X25) )
      & ( r2_hidden(esk6_3(X24,X25,X26),X25)
        | r2_hidden(esk4_3(X24,X25,X26),X26)
        | X26 = k2_zfmisc_1(X24,X25) )
      & ( esk4_3(X24,X25,X26) = k4_tarski(esk5_3(X24,X25,X26),esk6_3(X24,X25,X26))
        | r2_hidden(esk4_3(X24,X25,X26),X26)
        | X26 = k2_zfmisc_1(X24,X25) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_zfmisc_1])])])])])])).

cnf(c_0_14,negated_conjecture,
    ( k2_zfmisc_1(k1_tarski(esk7_0),k1_tarski(esk8_0)) != k1_tarski(k4_tarski(esk7_0,esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k2_enumset1(X2,X2,X2,X2)) ),
    inference(er,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( esk1_2(X1,X2) = X1
    | X2 = k2_enumset1(X1,X1,X1,X1)
    | r2_hidden(esk1_2(X1,X2),X2) ),
    inference(rw,[status(thm)],[c_0_12,c_0_9])).

cnf(c_0_17,plain,
    ( X1 = k4_tarski(esk2_4(X2,X3,X4,X1),esk3_4(X2,X3,X4,X1))
    | ~ r2_hidden(X1,X4)
    | X4 != k2_zfmisc_1(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( k2_zfmisc_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0)) != k2_enumset1(k4_tarski(esk7_0,esk8_0),k4_tarski(esk7_0,esk8_0),k4_tarski(esk7_0,esk8_0),k4_tarski(esk7_0,esk8_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_14,c_0_9]),c_0_9]),c_0_9])).

cnf(c_0_19,plain,
    ( k2_enumset1(X1,X1,X1,X1) = k2_enumset1(X2,X2,X2,X2)
    | esk1_2(X2,k2_enumset1(X1,X1,X1,X1)) = X2
    | esk1_2(X2,k2_enumset1(X1,X1,X1,X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_20,plain,
    ( k4_tarski(esk2_4(X1,X2,k2_zfmisc_1(X1,X2),X3),esk3_4(X1,X2,k2_zfmisc_1(X1,X2),X3)) = X3
    | ~ r2_hidden(X3,k2_zfmisc_1(X1,X2)) ),
    inference(er,[status(thm)],[c_0_17])).

fof(c_0_21,plain,(
    ! [X32,X33,X34,X35] :
      ( ( X32 = X34
        | ~ r2_hidden(k4_tarski(X32,X33),k2_zfmisc_1(k1_tarski(X34),k1_tarski(X35))) )
      & ( X33 = X35
        | ~ r2_hidden(k4_tarski(X32,X33),k2_zfmisc_1(k1_tarski(X34),k1_tarski(X35))) )
      & ( X32 != X34
        | X33 != X35
        | r2_hidden(k4_tarski(X32,X33),k2_zfmisc_1(k1_tarski(X34),k1_tarski(X35))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_zfmisc_1])])])).

cnf(c_0_22,negated_conjecture,
    ( esk1_2(k4_tarski(esk7_0,esk8_0),k2_enumset1(X1,X1,X1,X1)) = k4_tarski(esk7_0,esk8_0)
    | esk1_2(k4_tarski(esk7_0,esk8_0),k2_enumset1(X1,X1,X1,X1)) = X1
    | k2_enumset1(X1,X1,X1,X1) != k2_zfmisc_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_23,plain,
    ( k4_tarski(esk2_4(X1,X2,k2_zfmisc_1(X1,X2),esk1_2(X3,k2_zfmisc_1(X1,X2))),esk3_4(X1,X2,k2_zfmisc_1(X1,X2),esk1_2(X3,k2_zfmisc_1(X1,X2)))) = esk1_2(X3,k2_zfmisc_1(X1,X2))
    | k2_zfmisc_1(X1,X2) = k2_enumset1(X3,X3,X3,X3)
    | esk1_2(X3,k2_zfmisc_1(X1,X2)) = X3 ),
    inference(spm,[status(thm)],[c_0_20,c_0_16])).

cnf(c_0_24,plain,
    ( X1 = X2
    | ~ r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(k1_tarski(X4),k1_tarski(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_25,negated_conjecture,
    ( k4_tarski(esk2_4(X1,X2,k2_zfmisc_1(X1,X2),esk1_2(X3,k2_zfmisc_1(X1,X2))),esk3_4(X1,X2,k2_zfmisc_1(X1,X2),esk1_2(X3,k2_zfmisc_1(X1,X2)))) = esk1_2(X3,k2_zfmisc_1(X1,X2))
    | esk1_2(k4_tarski(esk7_0,esk8_0),k2_zfmisc_1(X1,X2)) = k4_tarski(esk7_0,esk8_0)
    | esk1_2(k4_tarski(esk7_0,esk8_0),k2_zfmisc_1(X1,X2)) = X3
    | esk1_2(X3,k2_zfmisc_1(X1,X2)) = X3
    | k2_zfmisc_1(X1,X2) != k2_zfmisc_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_26,plain,
    ( X1 = X2
    | ~ r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(k2_enumset1(X4,X4,X4,X4),k2_enumset1(X2,X2,X2,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_9]),c_0_9])).

cnf(c_0_27,negated_conjecture,
    ( k4_tarski(esk2_4(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0),k2_zfmisc_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0)),esk1_2(X1,k2_zfmisc_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0)))),esk3_4(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0),k2_zfmisc_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0)),esk1_2(X1,k2_zfmisc_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0))))) = esk1_2(X1,k2_zfmisc_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0)))
    | esk1_2(k4_tarski(esk7_0,esk8_0),k2_zfmisc_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0))) = k4_tarski(esk7_0,esk8_0)
    | esk1_2(k4_tarski(esk7_0,esk8_0),k2_zfmisc_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0))) = X1
    | esk1_2(X1,k2_zfmisc_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0))) = X1 ),
    inference(er,[status(thm)],[c_0_25])).

cnf(c_0_28,plain,
    ( X1 = X2
    | ~ r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,negated_conjecture,
    ( esk3_4(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0),k2_zfmisc_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0)),esk1_2(X1,k2_zfmisc_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0)))) = X2
    | esk1_2(k4_tarski(esk7_0,esk8_0),k2_zfmisc_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0))) = k4_tarski(esk7_0,esk8_0)
    | esk1_2(k4_tarski(esk7_0,esk8_0),k2_zfmisc_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0))) = X1
    | esk1_2(X1,k2_zfmisc_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0))) = X1
    | ~ r2_hidden(esk1_2(X1,k2_zfmisc_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0))),k2_zfmisc_1(k2_enumset1(X3,X3,X3,X3),k2_enumset1(X2,X2,X2,X2))) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_30,plain,
    ( X1 = X2
    | ~ r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(k2_enumset1(X2,X2,X2,X2),k2_enumset1(X4,X4,X4,X4))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_9]),c_0_9])).

cnf(c_0_31,negated_conjecture,
    ( esk3_4(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0),k2_zfmisc_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0)),esk1_2(X1,k2_zfmisc_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0)))) = esk8_0
    | esk1_2(k4_tarski(esk7_0,esk8_0),k2_zfmisc_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0))) = k4_tarski(esk7_0,esk8_0)
    | esk1_2(k4_tarski(esk7_0,esk8_0),k2_zfmisc_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0))) = X1
    | k2_zfmisc_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0)) = k2_enumset1(X1,X1,X1,X1)
    | esk1_2(X1,k2_zfmisc_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0))) = X1 ),
    inference(spm,[status(thm)],[c_0_29,c_0_16])).

cnf(c_0_32,negated_conjecture,
    ( esk2_4(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0),k2_zfmisc_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0)),esk1_2(X1,k2_zfmisc_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0)))) = X2
    | esk1_2(k4_tarski(esk7_0,esk8_0),k2_zfmisc_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0))) = k4_tarski(esk7_0,esk8_0)
    | esk1_2(k4_tarski(esk7_0,esk8_0),k2_zfmisc_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0))) = X1
    | esk1_2(X1,k2_zfmisc_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0))) = X1
    | ~ r2_hidden(esk1_2(X1,k2_zfmisc_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0))),k2_zfmisc_1(k2_enumset1(X2,X2,X2,X2),k2_enumset1(X3,X3,X3,X3))) ),
    inference(spm,[status(thm)],[c_0_30,c_0_27])).

cnf(c_0_33,negated_conjecture,
    ( esk3_4(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0),k2_zfmisc_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0)),esk1_2(X1,k2_zfmisc_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0)))) = esk8_0
    | esk1_2(k4_tarski(esk7_0,esk8_0),k2_zfmisc_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0))) = k4_tarski(esk7_0,esk8_0)
    | esk1_2(k4_tarski(esk7_0,esk8_0),k2_zfmisc_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0))) = X1
    | esk1_2(X1,k2_zfmisc_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0))) = X1 ),
    inference(spm,[status(thm)],[c_0_22,c_0_31])).

cnf(c_0_34,negated_conjecture,
    ( esk2_4(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0),k2_zfmisc_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0)),esk1_2(X1,k2_zfmisc_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0)))) = esk7_0
    | esk1_2(k4_tarski(esk7_0,esk8_0),k2_zfmisc_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0))) = k4_tarski(esk7_0,esk8_0)
    | esk1_2(k4_tarski(esk7_0,esk8_0),k2_zfmisc_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0))) = X1
    | k2_zfmisc_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0)) = k2_enumset1(X1,X1,X1,X1)
    | esk1_2(X1,k2_zfmisc_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0))) = X1 ),
    inference(spm,[status(thm)],[c_0_32,c_0_16])).

cnf(c_0_35,negated_conjecture,
    ( k4_tarski(esk2_4(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0),k2_zfmisc_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0)),esk1_2(X1,k2_zfmisc_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0)))),esk8_0) = esk1_2(X1,k2_zfmisc_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0)))
    | esk1_2(k4_tarski(esk7_0,esk8_0),k2_zfmisc_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0))) = k4_tarski(esk7_0,esk8_0)
    | esk1_2(k4_tarski(esk7_0,esk8_0),k2_zfmisc_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0))) = X1
    | esk1_2(X1,k2_zfmisc_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0))) = X1 ),
    inference(spm,[status(thm)],[c_0_27,c_0_33])).

cnf(c_0_36,negated_conjecture,
    ( esk2_4(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0),k2_zfmisc_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0)),esk1_2(X1,k2_zfmisc_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0)))) = esk7_0
    | esk1_2(k4_tarski(esk7_0,esk8_0),k2_zfmisc_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0))) = k4_tarski(esk7_0,esk8_0)
    | esk1_2(k4_tarski(esk7_0,esk8_0),k2_zfmisc_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0))) = X1
    | esk1_2(X1,k2_zfmisc_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0))) = X1 ),
    inference(spm,[status(thm)],[c_0_22,c_0_34])).

cnf(c_0_37,plain,
    ( r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X4)))
    | X1 != X2
    | X3 != X4 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_38,plain,
    ( X2 = k1_tarski(X1)
    | ~ r2_hidden(esk1_2(X1,X2),X2)
    | esk1_2(X1,X2) != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_39,negated_conjecture,
    ( esk1_2(k4_tarski(esk7_0,esk8_0),k2_zfmisc_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0))) = k4_tarski(esk7_0,esk8_0)
    | esk1_2(k4_tarski(esk7_0,esk8_0),k2_zfmisc_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0))) = X1
    | esk1_2(X1,k2_zfmisc_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0))) = k4_tarski(esk7_0,esk8_0)
    | esk1_2(X1,k2_zfmisc_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0))) = X1 ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_40,plain,
    ( r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(k2_enumset1(X2,X2,X2,X2),k2_enumset1(X4,X4,X4,X4)))
    | X3 != X4
    | X1 != X2 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_9]),c_0_9])).

cnf(c_0_41,plain,
    ( X2 = k2_enumset1(X1,X1,X1,X1)
    | esk1_2(X1,X2) != X1
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(rw,[status(thm)],[c_0_38,c_0_9])).

cnf(c_0_42,negated_conjecture,
    ( esk1_2(k4_tarski(esk7_0,esk8_0),k2_zfmisc_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0))) = k4_tarski(esk7_0,esk8_0) ),
    inference(ef,[status(thm)],[c_0_39])).

cnf(c_0_43,plain,
    ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2))) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_40])])).

cnf(c_0_44,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_43])]),c_0_18]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:56:04 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.52  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S080I
% 0.21/0.52  # and selection function SelectCQIArNXTEqFirst.
% 0.21/0.52  #
% 0.21/0.52  # Preprocessing time       : 0.027 s
% 0.21/0.52  # Presaturation interreduction done
% 0.21/0.52  
% 0.21/0.52  # Proof found!
% 0.21/0.52  # SZS status Theorem
% 0.21/0.52  # SZS output start CNFRefutation
% 0.21/0.52  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 0.21/0.52  fof(t82_enumset1, axiom, ![X1]:k2_enumset1(X1,X1,X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t82_enumset1)).
% 0.21/0.52  fof(t35_zfmisc_1, conjecture, ![X1, X2]:k2_zfmisc_1(k1_tarski(X1),k1_tarski(X2))=k1_tarski(k4_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_zfmisc_1)).
% 0.21/0.52  fof(d2_zfmisc_1, axiom, ![X1, X2, X3]:(X3=k2_zfmisc_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5, X6]:((r2_hidden(X5,X1)&r2_hidden(X6,X2))&X4=k4_tarski(X5,X6)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 0.21/0.52  fof(t34_zfmisc_1, axiom, ![X1, X2, X3, X4]:(r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(k1_tarski(X3),k1_tarski(X4)))<=>(X1=X3&X2=X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_zfmisc_1)).
% 0.21/0.52  fof(c_0_5, plain, ![X7, X8, X9, X10, X11, X12]:(((~r2_hidden(X9,X8)|X9=X7|X8!=k1_tarski(X7))&(X10!=X7|r2_hidden(X10,X8)|X8!=k1_tarski(X7)))&((~r2_hidden(esk1_2(X11,X12),X12)|esk1_2(X11,X12)!=X11|X12=k1_tarski(X11))&(r2_hidden(esk1_2(X11,X12),X12)|esk1_2(X11,X12)=X11|X12=k1_tarski(X11)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.21/0.52  fof(c_0_6, plain, ![X14]:k2_enumset1(X14,X14,X14,X14)=k1_tarski(X14), inference(variable_rename,[status(thm)],[t82_enumset1])).
% 0.21/0.52  fof(c_0_7, negated_conjecture, ~(![X1, X2]:k2_zfmisc_1(k1_tarski(X1),k1_tarski(X2))=k1_tarski(k4_tarski(X1,X2))), inference(assume_negation,[status(cth)],[t35_zfmisc_1])).
% 0.21/0.52  cnf(c_0_8, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.21/0.52  cnf(c_0_9, plain, (k2_enumset1(X1,X1,X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.21/0.52  fof(c_0_10, negated_conjecture, k2_zfmisc_1(k1_tarski(esk7_0),k1_tarski(esk8_0))!=k1_tarski(k4_tarski(esk7_0,esk8_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).
% 0.21/0.52  cnf(c_0_11, plain, (X1=X3|X2!=k2_enumset1(X3,X3,X3,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_8, c_0_9])).
% 0.21/0.52  cnf(c_0_12, plain, (r2_hidden(esk1_2(X1,X2),X2)|esk1_2(X1,X2)=X1|X2=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.21/0.52  fof(c_0_13, plain, ![X15, X16, X17, X18, X21, X22, X23, X24, X25, X26, X28, X29]:(((((r2_hidden(esk2_4(X15,X16,X17,X18),X15)|~r2_hidden(X18,X17)|X17!=k2_zfmisc_1(X15,X16))&(r2_hidden(esk3_4(X15,X16,X17,X18),X16)|~r2_hidden(X18,X17)|X17!=k2_zfmisc_1(X15,X16)))&(X18=k4_tarski(esk2_4(X15,X16,X17,X18),esk3_4(X15,X16,X17,X18))|~r2_hidden(X18,X17)|X17!=k2_zfmisc_1(X15,X16)))&(~r2_hidden(X22,X15)|~r2_hidden(X23,X16)|X21!=k4_tarski(X22,X23)|r2_hidden(X21,X17)|X17!=k2_zfmisc_1(X15,X16)))&((~r2_hidden(esk4_3(X24,X25,X26),X26)|(~r2_hidden(X28,X24)|~r2_hidden(X29,X25)|esk4_3(X24,X25,X26)!=k4_tarski(X28,X29))|X26=k2_zfmisc_1(X24,X25))&(((r2_hidden(esk5_3(X24,X25,X26),X24)|r2_hidden(esk4_3(X24,X25,X26),X26)|X26=k2_zfmisc_1(X24,X25))&(r2_hidden(esk6_3(X24,X25,X26),X25)|r2_hidden(esk4_3(X24,X25,X26),X26)|X26=k2_zfmisc_1(X24,X25)))&(esk4_3(X24,X25,X26)=k4_tarski(esk5_3(X24,X25,X26),esk6_3(X24,X25,X26))|r2_hidden(esk4_3(X24,X25,X26),X26)|X26=k2_zfmisc_1(X24,X25))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_zfmisc_1])])])])])])).
% 0.21/0.52  cnf(c_0_14, negated_conjecture, (k2_zfmisc_1(k1_tarski(esk7_0),k1_tarski(esk8_0))!=k1_tarski(k4_tarski(esk7_0,esk8_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.21/0.52  cnf(c_0_15, plain, (X1=X2|~r2_hidden(X1,k2_enumset1(X2,X2,X2,X2))), inference(er,[status(thm)],[c_0_11])).
% 0.21/0.52  cnf(c_0_16, plain, (esk1_2(X1,X2)=X1|X2=k2_enumset1(X1,X1,X1,X1)|r2_hidden(esk1_2(X1,X2),X2)), inference(rw,[status(thm)],[c_0_12, c_0_9])).
% 0.21/0.52  cnf(c_0_17, plain, (X1=k4_tarski(esk2_4(X2,X3,X4,X1),esk3_4(X2,X3,X4,X1))|~r2_hidden(X1,X4)|X4!=k2_zfmisc_1(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.21/0.52  cnf(c_0_18, negated_conjecture, (k2_zfmisc_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0))!=k2_enumset1(k4_tarski(esk7_0,esk8_0),k4_tarski(esk7_0,esk8_0),k4_tarski(esk7_0,esk8_0),k4_tarski(esk7_0,esk8_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_14, c_0_9]), c_0_9]), c_0_9])).
% 0.21/0.52  cnf(c_0_19, plain, (k2_enumset1(X1,X1,X1,X1)=k2_enumset1(X2,X2,X2,X2)|esk1_2(X2,k2_enumset1(X1,X1,X1,X1))=X2|esk1_2(X2,k2_enumset1(X1,X1,X1,X1))=X1), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.21/0.52  cnf(c_0_20, plain, (k4_tarski(esk2_4(X1,X2,k2_zfmisc_1(X1,X2),X3),esk3_4(X1,X2,k2_zfmisc_1(X1,X2),X3))=X3|~r2_hidden(X3,k2_zfmisc_1(X1,X2))), inference(er,[status(thm)],[c_0_17])).
% 0.21/0.52  fof(c_0_21, plain, ![X32, X33, X34, X35]:(((X32=X34|~r2_hidden(k4_tarski(X32,X33),k2_zfmisc_1(k1_tarski(X34),k1_tarski(X35))))&(X33=X35|~r2_hidden(k4_tarski(X32,X33),k2_zfmisc_1(k1_tarski(X34),k1_tarski(X35)))))&(X32!=X34|X33!=X35|r2_hidden(k4_tarski(X32,X33),k2_zfmisc_1(k1_tarski(X34),k1_tarski(X35))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_zfmisc_1])])])).
% 0.21/0.52  cnf(c_0_22, negated_conjecture, (esk1_2(k4_tarski(esk7_0,esk8_0),k2_enumset1(X1,X1,X1,X1))=k4_tarski(esk7_0,esk8_0)|esk1_2(k4_tarski(esk7_0,esk8_0),k2_enumset1(X1,X1,X1,X1))=X1|k2_enumset1(X1,X1,X1,X1)!=k2_zfmisc_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0))), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.21/0.52  cnf(c_0_23, plain, (k4_tarski(esk2_4(X1,X2,k2_zfmisc_1(X1,X2),esk1_2(X3,k2_zfmisc_1(X1,X2))),esk3_4(X1,X2,k2_zfmisc_1(X1,X2),esk1_2(X3,k2_zfmisc_1(X1,X2))))=esk1_2(X3,k2_zfmisc_1(X1,X2))|k2_zfmisc_1(X1,X2)=k2_enumset1(X3,X3,X3,X3)|esk1_2(X3,k2_zfmisc_1(X1,X2))=X3), inference(spm,[status(thm)],[c_0_20, c_0_16])).
% 0.21/0.52  cnf(c_0_24, plain, (X1=X2|~r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(k1_tarski(X4),k1_tarski(X2)))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.21/0.52  cnf(c_0_25, negated_conjecture, (k4_tarski(esk2_4(X1,X2,k2_zfmisc_1(X1,X2),esk1_2(X3,k2_zfmisc_1(X1,X2))),esk3_4(X1,X2,k2_zfmisc_1(X1,X2),esk1_2(X3,k2_zfmisc_1(X1,X2))))=esk1_2(X3,k2_zfmisc_1(X1,X2))|esk1_2(k4_tarski(esk7_0,esk8_0),k2_zfmisc_1(X1,X2))=k4_tarski(esk7_0,esk8_0)|esk1_2(k4_tarski(esk7_0,esk8_0),k2_zfmisc_1(X1,X2))=X3|esk1_2(X3,k2_zfmisc_1(X1,X2))=X3|k2_zfmisc_1(X1,X2)!=k2_zfmisc_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0))), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.21/0.52  cnf(c_0_26, plain, (X1=X2|~r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(k2_enumset1(X4,X4,X4,X4),k2_enumset1(X2,X2,X2,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_9]), c_0_9])).
% 0.21/0.52  cnf(c_0_27, negated_conjecture, (k4_tarski(esk2_4(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0),k2_zfmisc_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0)),esk1_2(X1,k2_zfmisc_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0)))),esk3_4(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0),k2_zfmisc_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0)),esk1_2(X1,k2_zfmisc_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0)))))=esk1_2(X1,k2_zfmisc_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0)))|esk1_2(k4_tarski(esk7_0,esk8_0),k2_zfmisc_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0)))=k4_tarski(esk7_0,esk8_0)|esk1_2(k4_tarski(esk7_0,esk8_0),k2_zfmisc_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0)))=X1|esk1_2(X1,k2_zfmisc_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0)))=X1), inference(er,[status(thm)],[c_0_25])).
% 0.21/0.52  cnf(c_0_28, plain, (X1=X2|~r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X4)))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.21/0.52  cnf(c_0_29, negated_conjecture, (esk3_4(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0),k2_zfmisc_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0)),esk1_2(X1,k2_zfmisc_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0))))=X2|esk1_2(k4_tarski(esk7_0,esk8_0),k2_zfmisc_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0)))=k4_tarski(esk7_0,esk8_0)|esk1_2(k4_tarski(esk7_0,esk8_0),k2_zfmisc_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0)))=X1|esk1_2(X1,k2_zfmisc_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0)))=X1|~r2_hidden(esk1_2(X1,k2_zfmisc_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0))),k2_zfmisc_1(k2_enumset1(X3,X3,X3,X3),k2_enumset1(X2,X2,X2,X2)))), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.21/0.52  cnf(c_0_30, plain, (X1=X2|~r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(k2_enumset1(X2,X2,X2,X2),k2_enumset1(X4,X4,X4,X4)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_9]), c_0_9])).
% 0.21/0.52  cnf(c_0_31, negated_conjecture, (esk3_4(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0),k2_zfmisc_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0)),esk1_2(X1,k2_zfmisc_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0))))=esk8_0|esk1_2(k4_tarski(esk7_0,esk8_0),k2_zfmisc_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0)))=k4_tarski(esk7_0,esk8_0)|esk1_2(k4_tarski(esk7_0,esk8_0),k2_zfmisc_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0)))=X1|k2_zfmisc_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0))=k2_enumset1(X1,X1,X1,X1)|esk1_2(X1,k2_zfmisc_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0)))=X1), inference(spm,[status(thm)],[c_0_29, c_0_16])).
% 0.21/0.52  cnf(c_0_32, negated_conjecture, (esk2_4(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0),k2_zfmisc_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0)),esk1_2(X1,k2_zfmisc_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0))))=X2|esk1_2(k4_tarski(esk7_0,esk8_0),k2_zfmisc_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0)))=k4_tarski(esk7_0,esk8_0)|esk1_2(k4_tarski(esk7_0,esk8_0),k2_zfmisc_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0)))=X1|esk1_2(X1,k2_zfmisc_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0)))=X1|~r2_hidden(esk1_2(X1,k2_zfmisc_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0))),k2_zfmisc_1(k2_enumset1(X2,X2,X2,X2),k2_enumset1(X3,X3,X3,X3)))), inference(spm,[status(thm)],[c_0_30, c_0_27])).
% 0.21/0.52  cnf(c_0_33, negated_conjecture, (esk3_4(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0),k2_zfmisc_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0)),esk1_2(X1,k2_zfmisc_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0))))=esk8_0|esk1_2(k4_tarski(esk7_0,esk8_0),k2_zfmisc_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0)))=k4_tarski(esk7_0,esk8_0)|esk1_2(k4_tarski(esk7_0,esk8_0),k2_zfmisc_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0)))=X1|esk1_2(X1,k2_zfmisc_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0)))=X1), inference(spm,[status(thm)],[c_0_22, c_0_31])).
% 0.21/0.52  cnf(c_0_34, negated_conjecture, (esk2_4(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0),k2_zfmisc_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0)),esk1_2(X1,k2_zfmisc_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0))))=esk7_0|esk1_2(k4_tarski(esk7_0,esk8_0),k2_zfmisc_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0)))=k4_tarski(esk7_0,esk8_0)|esk1_2(k4_tarski(esk7_0,esk8_0),k2_zfmisc_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0)))=X1|k2_zfmisc_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0))=k2_enumset1(X1,X1,X1,X1)|esk1_2(X1,k2_zfmisc_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0)))=X1), inference(spm,[status(thm)],[c_0_32, c_0_16])).
% 0.21/0.52  cnf(c_0_35, negated_conjecture, (k4_tarski(esk2_4(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0),k2_zfmisc_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0)),esk1_2(X1,k2_zfmisc_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0)))),esk8_0)=esk1_2(X1,k2_zfmisc_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0)))|esk1_2(k4_tarski(esk7_0,esk8_0),k2_zfmisc_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0)))=k4_tarski(esk7_0,esk8_0)|esk1_2(k4_tarski(esk7_0,esk8_0),k2_zfmisc_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0)))=X1|esk1_2(X1,k2_zfmisc_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0)))=X1), inference(spm,[status(thm)],[c_0_27, c_0_33])).
% 0.21/0.52  cnf(c_0_36, negated_conjecture, (esk2_4(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0),k2_zfmisc_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0)),esk1_2(X1,k2_zfmisc_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0))))=esk7_0|esk1_2(k4_tarski(esk7_0,esk8_0),k2_zfmisc_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0)))=k4_tarski(esk7_0,esk8_0)|esk1_2(k4_tarski(esk7_0,esk8_0),k2_zfmisc_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0)))=X1|esk1_2(X1,k2_zfmisc_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0)))=X1), inference(spm,[status(thm)],[c_0_22, c_0_34])).
% 0.21/0.52  cnf(c_0_37, plain, (r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X4)))|X1!=X2|X3!=X4), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.21/0.52  cnf(c_0_38, plain, (X2=k1_tarski(X1)|~r2_hidden(esk1_2(X1,X2),X2)|esk1_2(X1,X2)!=X1), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.21/0.52  cnf(c_0_39, negated_conjecture, (esk1_2(k4_tarski(esk7_0,esk8_0),k2_zfmisc_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0)))=k4_tarski(esk7_0,esk8_0)|esk1_2(k4_tarski(esk7_0,esk8_0),k2_zfmisc_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0)))=X1|esk1_2(X1,k2_zfmisc_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0)))=k4_tarski(esk7_0,esk8_0)|esk1_2(X1,k2_zfmisc_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0)))=X1), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.21/0.52  cnf(c_0_40, plain, (r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(k2_enumset1(X2,X2,X2,X2),k2_enumset1(X4,X4,X4,X4)))|X3!=X4|X1!=X2), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37, c_0_9]), c_0_9])).
% 0.21/0.52  cnf(c_0_41, plain, (X2=k2_enumset1(X1,X1,X1,X1)|esk1_2(X1,X2)!=X1|~r2_hidden(esk1_2(X1,X2),X2)), inference(rw,[status(thm)],[c_0_38, c_0_9])).
% 0.21/0.52  cnf(c_0_42, negated_conjecture, (esk1_2(k4_tarski(esk7_0,esk8_0),k2_zfmisc_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0)))=k4_tarski(esk7_0,esk8_0)), inference(ef,[status(thm)],[c_0_39])).
% 0.21/0.52  cnf(c_0_43, plain, (r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2)))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_40])])).
% 0.21/0.52  cnf(c_0_44, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_43])]), c_0_18]), ['proof']).
% 0.21/0.52  # SZS output end CNFRefutation
% 0.21/0.52  # Proof object total steps             : 45
% 0.21/0.52  # Proof object clause steps            : 34
% 0.21/0.52  # Proof object formula steps           : 11
% 0.21/0.52  # Proof object conjectures             : 18
% 0.21/0.52  # Proof object clause conjectures      : 15
% 0.21/0.52  # Proof object formula conjectures     : 3
% 0.21/0.52  # Proof object initial clauses used    : 9
% 0.21/0.52  # Proof object initial formulas used   : 5
% 0.21/0.52  # Proof object generating inferences   : 15
% 0.21/0.52  # Proof object simplifying inferences  : 19
% 0.21/0.52  # Training examples: 0 positive, 0 negative
% 0.21/0.52  # Parsed axioms                        : 5
% 0.21/0.52  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.52  # Initial clauses                      : 17
% 0.21/0.52  # Removed in clause preprocessing      : 1
% 0.21/0.52  # Initial clauses in saturation        : 16
% 0.21/0.52  # Processed clauses                    : 249
% 0.21/0.52  # ...of these trivial                  : 0
% 0.21/0.52  # ...subsumed                          : 41
% 0.21/0.52  # ...remaining for further processing  : 208
% 0.21/0.52  # Other redundant clauses eliminated   : 19
% 0.21/0.52  # Clauses deleted for lack of memory   : 0
% 0.21/0.52  # Backward-subsumed                    : 2
% 0.21/0.52  # Backward-rewritten                   : 20
% 0.21/0.52  # Generated clauses                    : 3960
% 0.21/0.52  # ...of the previous two non-trivial   : 3925
% 0.21/0.52  # Contextual simplify-reflections      : 0
% 0.21/0.52  # Paramodulations                      : 3921
% 0.21/0.52  # Factorizations                       : 17
% 0.21/0.52  # Equation resolutions                 : 25
% 0.21/0.52  # Propositional unsat checks           : 0
% 0.21/0.52  #    Propositional check models        : 0
% 0.21/0.52  #    Propositional check unsatisfiable : 0
% 0.21/0.52  #    Propositional clauses             : 0
% 0.21/0.52  #    Propositional clauses after purity: 0
% 0.21/0.52  #    Propositional unsat core size     : 0
% 0.21/0.52  #    Propositional preprocessing time  : 0.000
% 0.21/0.52  #    Propositional encoding time       : 0.000
% 0.21/0.52  #    Propositional solver time         : 0.000
% 0.21/0.52  #    Success case prop preproc time    : 0.000
% 0.21/0.52  #    Success case prop encoding time   : 0.000
% 0.21/0.52  #    Success case prop solver time     : 0.000
% 0.21/0.52  # Current number of processed clauses  : 163
% 0.21/0.52  #    Positive orientable unit clauses  : 5
% 0.21/0.52  #    Positive unorientable unit clauses: 0
% 0.21/0.52  #    Negative unit clauses             : 1
% 0.21/0.52  #    Non-unit-clauses                  : 157
% 0.21/0.52  # Current number of unprocessed clauses: 3684
% 0.21/0.52  # ...number of literals in the above   : 19895
% 0.21/0.52  # Current number of archived formulas  : 0
% 0.21/0.52  # Current number of archived clauses   : 39
% 0.21/0.52  # Clause-clause subsumption calls (NU) : 7170
% 0.21/0.52  # Rec. Clause-clause subsumption calls : 2000
% 0.21/0.52  # Non-unit clause-clause subsumptions  : 43
% 0.21/0.52  # Unit Clause-clause subsumption calls : 20
% 0.21/0.52  # Rewrite failures with RHS unbound    : 0
% 0.21/0.52  # BW rewrite match attempts            : 7
% 0.21/0.52  # BW rewrite match successes           : 3
% 0.21/0.52  # Condensation attempts                : 0
% 0.21/0.52  # Condensation successes               : 0
% 0.21/0.52  # Termbank termtop insertions          : 138333
% 0.21/0.52  
% 0.21/0.52  # -------------------------------------------------
% 0.21/0.52  # User time                : 0.174 s
% 0.21/0.52  # System time              : 0.005 s
% 0.21/0.52  # Total time               : 0.179 s
% 0.21/0.52  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
