%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0404+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:39:35 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   22 (  38 expanded)
%              Number of clauses        :   13 (  17 expanded)
%              Number of leaves         :    4 (   9 expanded)
%              Depth                    :    7
%              Number of atoms          :   75 ( 149 expanded)
%              Number of equality atoms :   19 (  33 expanded)
%              Maximal formula depth    :   23 (   4 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t30_setfam_1,conjecture,(
    ! [X1] : r1_setfam_1(k3_setfam_1(X1,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_setfam_1)).

fof(d5_setfam_1,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_setfam_1(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ? [X5,X6] :
              ( r2_hidden(X5,X1)
              & r2_hidden(X6,X2)
              & X4 = k3_xboole_0(X5,X6) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_setfam_1)).

fof(d2_setfam_1,axiom,(
    ! [X1,X2] :
      ( r1_setfam_1(X1,X2)
    <=> ! [X3] :
          ~ ( r2_hidden(X3,X1)
            & ! [X4] :
                ~ ( r2_hidden(X4,X2)
                  & r1_tarski(X3,X4) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_setfam_1)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1] : r1_setfam_1(k3_setfam_1(X1,X1),X1) ),
    inference(assume_negation,[status(cth)],[t30_setfam_1])).

fof(c_0_5,plain,(
    ! [X15,X16,X17,X18,X21,X22,X23,X24,X25,X26,X28,X29] :
      ( ( r2_hidden(esk3_4(X15,X16,X17,X18),X15)
        | ~ r2_hidden(X18,X17)
        | X17 != k3_setfam_1(X15,X16) )
      & ( r2_hidden(esk4_4(X15,X16,X17,X18),X16)
        | ~ r2_hidden(X18,X17)
        | X17 != k3_setfam_1(X15,X16) )
      & ( X18 = k3_xboole_0(esk3_4(X15,X16,X17,X18),esk4_4(X15,X16,X17,X18))
        | ~ r2_hidden(X18,X17)
        | X17 != k3_setfam_1(X15,X16) )
      & ( ~ r2_hidden(X22,X15)
        | ~ r2_hidden(X23,X16)
        | X21 != k3_xboole_0(X22,X23)
        | r2_hidden(X21,X17)
        | X17 != k3_setfam_1(X15,X16) )
      & ( ~ r2_hidden(esk5_3(X24,X25,X26),X26)
        | ~ r2_hidden(X28,X24)
        | ~ r2_hidden(X29,X25)
        | esk5_3(X24,X25,X26) != k3_xboole_0(X28,X29)
        | X26 = k3_setfam_1(X24,X25) )
      & ( r2_hidden(esk6_3(X24,X25,X26),X24)
        | r2_hidden(esk5_3(X24,X25,X26),X26)
        | X26 = k3_setfam_1(X24,X25) )
      & ( r2_hidden(esk7_3(X24,X25,X26),X25)
        | r2_hidden(esk5_3(X24,X25,X26),X26)
        | X26 = k3_setfam_1(X24,X25) )
      & ( esk5_3(X24,X25,X26) = k3_xboole_0(esk6_3(X24,X25,X26),esk7_3(X24,X25,X26))
        | r2_hidden(esk5_3(X24,X25,X26),X26)
        | X26 = k3_setfam_1(X24,X25) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_setfam_1])])])])])])).

fof(c_0_6,negated_conjecture,(
    ~ r1_setfam_1(k3_setfam_1(esk8_0,esk8_0),esk8_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).

fof(c_0_7,plain,(
    ! [X7,X8,X9,X11,X12,X14] :
      ( ( r2_hidden(esk1_3(X7,X8,X9),X8)
        | ~ r2_hidden(X9,X7)
        | ~ r1_setfam_1(X7,X8) )
      & ( r1_tarski(X9,esk1_3(X7,X8,X9))
        | ~ r2_hidden(X9,X7)
        | ~ r1_setfam_1(X7,X8) )
      & ( r2_hidden(esk2_2(X11,X12),X11)
        | r1_setfam_1(X11,X12) )
      & ( ~ r2_hidden(X14,X12)
        | ~ r1_tarski(esk2_2(X11,X12),X14)
        | r1_setfam_1(X11,X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_setfam_1])])])])])])).

cnf(c_0_8,plain,
    ( X1 = k3_xboole_0(esk3_4(X2,X3,X4,X1),esk4_4(X2,X3,X4,X1))
    | ~ r2_hidden(X1,X4)
    | X4 != k3_setfam_1(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,negated_conjecture,
    ( ~ r1_setfam_1(k3_setfam_1(esk8_0,esk8_0),esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_setfam_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_11,plain,(
    ! [X32,X33] : r1_tarski(k3_xboole_0(X32,X33),X32) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

cnf(c_0_12,plain,
    ( k3_xboole_0(esk3_4(X1,X2,k3_setfam_1(X1,X2),X3),esk4_4(X1,X2,k3_setfam_1(X1,X2),X3)) = X3
    | ~ r2_hidden(X3,k3_setfam_1(X1,X2)) ),
    inference(er,[status(thm)],[c_0_8])).

cnf(c_0_13,negated_conjecture,
    ( r2_hidden(esk2_2(k3_setfam_1(esk8_0,esk8_0),esk8_0),k3_setfam_1(esk8_0,esk8_0)) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_14,plain,
    ( r2_hidden(esk3_4(X1,X2,X3,X4),X1)
    | ~ r2_hidden(X4,X3)
    | X3 != k3_setfam_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_15,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( k3_xboole_0(esk3_4(esk8_0,esk8_0,k3_setfam_1(esk8_0,esk8_0),esk2_2(k3_setfam_1(esk8_0,esk8_0),esk8_0)),esk4_4(esk8_0,esk8_0,k3_setfam_1(esk8_0,esk8_0),esk2_2(k3_setfam_1(esk8_0,esk8_0),esk8_0))) = esk2_2(k3_setfam_1(esk8_0,esk8_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_17,plain,
    ( r2_hidden(esk3_4(X1,X2,k3_setfam_1(X1,X2),X3),X1)
    | ~ r2_hidden(X3,k3_setfam_1(X1,X2)) ),
    inference(er,[status(thm)],[c_0_14])).

cnf(c_0_18,plain,
    ( r1_setfam_1(X3,X2)
    | ~ r2_hidden(X1,X2)
    | ~ r1_tarski(esk2_2(X3,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_19,negated_conjecture,
    ( r1_tarski(esk2_2(k3_setfam_1(esk8_0,esk8_0),esk8_0),esk3_4(esk8_0,esk8_0,k3_setfam_1(esk8_0,esk8_0),esk2_2(k3_setfam_1(esk8_0,esk8_0),esk8_0))) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( r2_hidden(esk3_4(esk8_0,esk8_0,k3_setfam_1(esk8_0,esk8_0),esk2_2(k3_setfam_1(esk8_0,esk8_0),esk8_0)),esk8_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_13])).

cnf(c_0_21,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20])]),c_0_9]),
    [proof]).

%------------------------------------------------------------------------------
