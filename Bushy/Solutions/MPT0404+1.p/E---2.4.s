%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : setfam_1__t30_setfam_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:17 EDT 2019

% Result     : Theorem 152.84s
% Output     : CNFRefutation 152.84s
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
    file('/export/starexec/sandbox/benchmark/setfam_1__t30_setfam_1.p',t30_setfam_1)).

fof(d5_setfam_1,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_setfam_1(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ? [X5,X6] :
              ( r2_hidden(X5,X1)
              & r2_hidden(X6,X2)
              & X4 = k3_xboole_0(X5,X6) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/setfam_1__t30_setfam_1.p',d5_setfam_1)).

fof(d2_setfam_1,axiom,(
    ! [X1,X2] :
      ( r1_setfam_1(X1,X2)
    <=> ! [X3] :
          ~ ( r2_hidden(X3,X1)
            & ! [X4] :
                ~ ( r2_hidden(X4,X2)
                  & r1_tarski(X3,X4) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/setfam_1__t30_setfam_1.p',d2_setfam_1)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/setfam_1__t30_setfam_1.p',t17_xboole_1)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1] : r1_setfam_1(k3_setfam_1(X1,X1),X1) ),
    inference(assume_negation,[status(cth)],[t30_setfam_1])).

fof(c_0_5,plain,(
    ! [X22,X23,X24,X25,X28,X29,X30,X31,X32,X33,X35,X36] :
      ( ( r2_hidden(esk4_4(X22,X23,X24,X25),X22)
        | ~ r2_hidden(X25,X24)
        | X24 != k3_setfam_1(X22,X23) )
      & ( r2_hidden(esk5_4(X22,X23,X24,X25),X23)
        | ~ r2_hidden(X25,X24)
        | X24 != k3_setfam_1(X22,X23) )
      & ( X25 = k3_xboole_0(esk4_4(X22,X23,X24,X25),esk5_4(X22,X23,X24,X25))
        | ~ r2_hidden(X25,X24)
        | X24 != k3_setfam_1(X22,X23) )
      & ( ~ r2_hidden(X29,X22)
        | ~ r2_hidden(X30,X23)
        | X28 != k3_xboole_0(X29,X30)
        | r2_hidden(X28,X24)
        | X24 != k3_setfam_1(X22,X23) )
      & ( ~ r2_hidden(esk6_3(X31,X32,X33),X33)
        | ~ r2_hidden(X35,X31)
        | ~ r2_hidden(X36,X32)
        | esk6_3(X31,X32,X33) != k3_xboole_0(X35,X36)
        | X33 = k3_setfam_1(X31,X32) )
      & ( r2_hidden(esk7_3(X31,X32,X33),X31)
        | r2_hidden(esk6_3(X31,X32,X33),X33)
        | X33 = k3_setfam_1(X31,X32) )
      & ( r2_hidden(esk8_3(X31,X32,X33),X32)
        | r2_hidden(esk6_3(X31,X32,X33),X33)
        | X33 = k3_setfam_1(X31,X32) )
      & ( esk6_3(X31,X32,X33) = k3_xboole_0(esk7_3(X31,X32,X33),esk8_3(X31,X32,X33))
        | r2_hidden(esk6_3(X31,X32,X33),X33)
        | X33 = k3_setfam_1(X31,X32) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_setfam_1])])])])])])).

fof(c_0_6,negated_conjecture,(
    ~ r1_setfam_1(k3_setfam_1(esk1_0,esk1_0),esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).

fof(c_0_7,plain,(
    ! [X14,X15,X16,X18,X19,X21] :
      ( ( r2_hidden(esk2_3(X14,X15,X16),X15)
        | ~ r2_hidden(X16,X14)
        | ~ r1_setfam_1(X14,X15) )
      & ( r1_tarski(X16,esk2_3(X14,X15,X16))
        | ~ r2_hidden(X16,X14)
        | ~ r1_setfam_1(X14,X15) )
      & ( r2_hidden(esk3_2(X18,X19),X18)
        | r1_setfam_1(X18,X19) )
      & ( ~ r2_hidden(X21,X19)
        | ~ r1_tarski(esk3_2(X18,X19),X21)
        | r1_setfam_1(X18,X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_setfam_1])])])])])])).

cnf(c_0_8,plain,
    ( X1 = k3_xboole_0(esk4_4(X2,X3,X4,X1),esk5_4(X2,X3,X4,X1))
    | ~ r2_hidden(X1,X4)
    | X4 != k3_setfam_1(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,negated_conjecture,
    ( ~ r1_setfam_1(k3_setfam_1(esk1_0,esk1_0),esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( r2_hidden(esk3_2(X1,X2),X1)
    | r1_setfam_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_11,plain,(
    ! [X43,X44] : r1_tarski(k3_xboole_0(X43,X44),X43) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

cnf(c_0_12,plain,
    ( k3_xboole_0(esk4_4(X1,X2,k3_setfam_1(X1,X2),X3),esk5_4(X1,X2,k3_setfam_1(X1,X2),X3)) = X3
    | ~ r2_hidden(X3,k3_setfam_1(X1,X2)) ),
    inference(er,[status(thm)],[c_0_8])).

cnf(c_0_13,negated_conjecture,
    ( r2_hidden(esk3_2(k3_setfam_1(esk1_0,esk1_0),esk1_0),k3_setfam_1(esk1_0,esk1_0)) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_14,plain,
    ( r2_hidden(esk4_4(X1,X2,X3,X4),X1)
    | ~ r2_hidden(X4,X3)
    | X3 != k3_setfam_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_15,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( k3_xboole_0(esk4_4(esk1_0,esk1_0,k3_setfam_1(esk1_0,esk1_0),esk3_2(k3_setfam_1(esk1_0,esk1_0),esk1_0)),esk5_4(esk1_0,esk1_0,k3_setfam_1(esk1_0,esk1_0),esk3_2(k3_setfam_1(esk1_0,esk1_0),esk1_0))) = esk3_2(k3_setfam_1(esk1_0,esk1_0),esk1_0) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_17,plain,
    ( r2_hidden(esk4_4(X1,X2,k3_setfam_1(X1,X2),X3),X1)
    | ~ r2_hidden(X3,k3_setfam_1(X1,X2)) ),
    inference(er,[status(thm)],[c_0_14])).

cnf(c_0_18,plain,
    ( r1_setfam_1(X3,X2)
    | ~ r2_hidden(X1,X2)
    | ~ r1_tarski(esk3_2(X3,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_19,negated_conjecture,
    ( r1_tarski(esk3_2(k3_setfam_1(esk1_0,esk1_0),esk1_0),esk4_4(esk1_0,esk1_0,k3_setfam_1(esk1_0,esk1_0),esk3_2(k3_setfam_1(esk1_0,esk1_0),esk1_0))) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( r2_hidden(esk4_4(esk1_0,esk1_0,k3_setfam_1(esk1_0,esk1_0),esk3_2(k3_setfam_1(esk1_0,esk1_0),esk1_0)),esk1_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_13])).

cnf(c_0_21,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20])]),c_0_9]),
    [proof]).
%------------------------------------------------------------------------------
