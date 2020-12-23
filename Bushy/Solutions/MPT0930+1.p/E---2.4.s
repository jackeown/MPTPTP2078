%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : mcart_1__t91_mcart_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:16 EDT 2019

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   24 (  51 expanded)
%              Number of clauses        :   15 (  22 expanded)
%              Number of leaves         :    4 (  11 expanded)
%              Depth                    :    9
%              Number of atoms          :   75 ( 163 expanded)
%              Number of equality atoms :   17 (  22 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t91_mcart_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => ( r2_hidden(k1_mcart_1(X2),k1_relat_1(X1))
            & r2_hidden(k2_mcart_1(X2),k2_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t91_mcart_1.p',t91_mcart_1)).

fof(t23_mcart_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X1,X2)
       => X1 = k4_tarski(k1_mcart_1(X1),k2_mcart_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t91_mcart_1.p',t23_mcart_1)).

fof(d5_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k2_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X4,X3),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t91_mcart_1.p',d5_relat_1)).

fof(d4_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X3,X4),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t91_mcart_1.p',d4_relat_1)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( r2_hidden(X2,X1)
           => ( r2_hidden(k1_mcart_1(X2),k1_relat_1(X1))
              & r2_hidden(k2_mcart_1(X2),k2_relat_1(X1)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t91_mcart_1])).

fof(c_0_5,plain,(
    ! [X35,X36] :
      ( ~ v1_relat_1(X36)
      | ~ r2_hidden(X35,X36)
      | X35 = k4_tarski(k1_mcart_1(X35),k2_mcart_1(X35)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_mcart_1])])).

fof(c_0_6,negated_conjecture,
    ( v1_relat_1(esk1_0)
    & r2_hidden(esk2_0,esk1_0)
    & ( ~ r2_hidden(k1_mcart_1(esk2_0),k1_relat_1(esk1_0))
      | ~ r2_hidden(k2_mcart_1(esk2_0),k2_relat_1(esk1_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).

fof(c_0_7,plain,(
    ! [X20,X21,X22,X24,X25,X26,X27,X29] :
      ( ( ~ r2_hidden(X22,X21)
        | r2_hidden(k4_tarski(esk6_3(X20,X21,X22),X22),X20)
        | X21 != k2_relat_1(X20) )
      & ( ~ r2_hidden(k4_tarski(X25,X24),X20)
        | r2_hidden(X24,X21)
        | X21 != k2_relat_1(X20) )
      & ( ~ r2_hidden(esk7_2(X26,X27),X27)
        | ~ r2_hidden(k4_tarski(X29,esk7_2(X26,X27)),X26)
        | X27 = k2_relat_1(X26) )
      & ( r2_hidden(esk7_2(X26,X27),X27)
        | r2_hidden(k4_tarski(esk8_2(X26,X27),esk7_2(X26,X27)),X26)
        | X27 = k2_relat_1(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).

cnf(c_0_8,plain,
    ( X2 = k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2))
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,negated_conjecture,
    ( v1_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( r2_hidden(X2,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,negated_conjecture,
    ( k4_tarski(k1_mcart_1(X1),k2_mcart_1(X1)) = X1
    | ~ r2_hidden(X1,esk1_0) ),
    inference(spm,[status(thm)],[c_0_8,c_0_9])).

cnf(c_0_12,negated_conjecture,
    ( r2_hidden(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_13,plain,(
    ! [X9,X10,X11,X13,X14,X15,X16,X18] :
      ( ( ~ r2_hidden(X11,X10)
        | r2_hidden(k4_tarski(X11,esk3_3(X9,X10,X11)),X9)
        | X10 != k1_relat_1(X9) )
      & ( ~ r2_hidden(k4_tarski(X13,X14),X9)
        | r2_hidden(X13,X10)
        | X10 != k1_relat_1(X9) )
      & ( ~ r2_hidden(esk4_2(X15,X16),X16)
        | ~ r2_hidden(k4_tarski(esk4_2(X15,X16),X18),X15)
        | X16 = k1_relat_1(X15) )
      & ( r2_hidden(esk4_2(X15,X16),X16)
        | r2_hidden(k4_tarski(esk4_2(X15,X16),esk5_2(X15,X16)),X15)
        | X16 = k1_relat_1(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).

cnf(c_0_14,plain,
    ( r2_hidden(X1,k2_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X3,X1),X2) ),
    inference(er,[status(thm)],[c_0_10])).

cnf(c_0_15,negated_conjecture,
    ( k4_tarski(k1_mcart_1(esk2_0),k2_mcart_1(esk2_0)) = esk2_0 ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_16,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,negated_conjecture,
    ( r2_hidden(k2_mcart_1(esk2_0),k2_relat_1(X1))
    | ~ r2_hidden(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_18,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2) ),
    inference(er,[status(thm)],[c_0_16])).

cnf(c_0_19,negated_conjecture,
    ( ~ r2_hidden(k1_mcart_1(esk2_0),k1_relat_1(esk1_0))
    | ~ r2_hidden(k2_mcart_1(esk2_0),k2_relat_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_20,negated_conjecture,
    ( r2_hidden(k2_mcart_1(esk2_0),k2_relat_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_12])).

cnf(c_0_21,negated_conjecture,
    ( r2_hidden(k1_mcart_1(esk2_0),k1_relat_1(X1))
    | ~ r2_hidden(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_15])).

cnf(c_0_22,negated_conjecture,
    ( ~ r2_hidden(k1_mcart_1(esk2_0),k1_relat_1(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_19,c_0_20])])).

cnf(c_0_23,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_12]),c_0_22]),
    [proof]).
%------------------------------------------------------------------------------
