%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : wellord1__t20_wellord1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:11 EDT 2019

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   25 ( 132 expanded)
%              Number of clauses        :   18 (  55 expanded)
%              Number of leaves         :    3 (  32 expanded)
%              Depth                    :   15
%              Number of atoms          :   60 ( 408 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t20_wellord1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k3_relat_1(k2_wellord1(X2,X1)),k3_relat_1(X2))
        & r1_tarski(k3_relat_1(k2_wellord1(X2,X1)),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t20_wellord1.p',t20_wellord1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t20_wellord1.p',d3_tarski)).

fof(t19_wellord1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k3_relat_1(k2_wellord1(X3,X2)))
       => ( r2_hidden(X1,k3_relat_1(X3))
          & r2_hidden(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t20_wellord1.p',t19_wellord1)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(k3_relat_1(k2_wellord1(X2,X1)),k3_relat_1(X2))
          & r1_tarski(k3_relat_1(k2_wellord1(X2,X1)),X1) ) ) ),
    inference(assume_negation,[status(cth)],[t20_wellord1])).

fof(c_0_4,negated_conjecture,
    ( v1_relat_1(esk2_0)
    & ( ~ r1_tarski(k3_relat_1(k2_wellord1(esk2_0,esk1_0)),k3_relat_1(esk2_0))
      | ~ r1_tarski(k3_relat_1(k2_wellord1(esk2_0,esk1_0)),esk1_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])).

fof(c_0_5,plain,(
    ! [X12,X13,X14,X15,X16] :
      ( ( ~ r1_tarski(X12,X13)
        | ~ r2_hidden(X14,X12)
        | r2_hidden(X14,X13) )
      & ( r2_hidden(esk3_2(X15,X16),X15)
        | r1_tarski(X15,X16) )
      & ( ~ r2_hidden(esk3_2(X15,X16),X16)
        | r1_tarski(X15,X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_6,negated_conjecture,
    ( ~ r1_tarski(k3_relat_1(k2_wellord1(esk2_0,esk1_0)),k3_relat_1(esk2_0))
    | ~ r1_tarski(k3_relat_1(k2_wellord1(esk2_0,esk1_0)),esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_7,plain,
    ( r2_hidden(esk3_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_8,plain,(
    ! [X24,X25,X26] :
      ( ( r2_hidden(X24,k3_relat_1(X26))
        | ~ r2_hidden(X24,k3_relat_1(k2_wellord1(X26,X25)))
        | ~ v1_relat_1(X26) )
      & ( r2_hidden(X24,X25)
        | ~ r2_hidden(X24,k3_relat_1(k2_wellord1(X26,X25)))
        | ~ v1_relat_1(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_wellord1])])])).

cnf(c_0_9,negated_conjecture,
    ( r2_hidden(esk3_2(k3_relat_1(k2_wellord1(esk2_0,esk1_0)),esk1_0),k3_relat_1(k2_wellord1(esk2_0,esk1_0)))
    | ~ r1_tarski(k3_relat_1(k2_wellord1(esk2_0,esk1_0)),k3_relat_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_6,c_0_7])).

cnf(c_0_10,plain,
    ( r2_hidden(X1,k3_relat_1(X2))
    | ~ r2_hidden(X1,k3_relat_1(k2_wellord1(X2,X3)))
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_11,negated_conjecture,
    ( r2_hidden(esk3_2(k3_relat_1(k2_wellord1(esk2_0,esk1_0)),k3_relat_1(esk2_0)),k3_relat_1(k2_wellord1(esk2_0,esk1_0)))
    | r2_hidden(esk3_2(k3_relat_1(k2_wellord1(esk2_0,esk1_0)),esk1_0),k3_relat_1(k2_wellord1(esk2_0,esk1_0))) ),
    inference(spm,[status(thm)],[c_0_9,c_0_7])).

cnf(c_0_12,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_13,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_relat_1(k2_wellord1(X3,X2)))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,negated_conjecture,
    ( r2_hidden(esk3_2(k3_relat_1(k2_wellord1(esk2_0,esk1_0)),esk1_0),k3_relat_1(k2_wellord1(esk2_0,esk1_0)))
    | r2_hidden(esk3_2(k3_relat_1(k2_wellord1(esk2_0,esk1_0)),k3_relat_1(esk2_0)),k3_relat_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_11]),c_0_12])])).

cnf(c_0_15,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk3_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_16,negated_conjecture,
    ( r2_hidden(esk3_2(k3_relat_1(k2_wellord1(esk2_0,esk1_0)),k3_relat_1(esk2_0)),k3_relat_1(esk2_0))
    | r2_hidden(esk3_2(k3_relat_1(k2_wellord1(esk2_0,esk1_0)),esk1_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_12])])).

cnf(c_0_17,negated_conjecture,
    ( r2_hidden(esk3_2(k3_relat_1(k2_wellord1(esk2_0,esk1_0)),esk1_0),esk1_0)
    | r1_tarski(k3_relat_1(k2_wellord1(esk2_0,esk1_0)),k3_relat_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_18,negated_conjecture,
    ( r2_hidden(esk3_2(k3_relat_1(k2_wellord1(esk2_0,esk1_0)),esk1_0),k3_relat_1(k2_wellord1(esk2_0,esk1_0)))
    | r2_hidden(esk3_2(k3_relat_1(k2_wellord1(esk2_0,esk1_0)),esk1_0),esk1_0) ),
    inference(spm,[status(thm)],[c_0_9,c_0_17])).

cnf(c_0_19,negated_conjecture,
    ( r2_hidden(esk3_2(k3_relat_1(k2_wellord1(esk2_0,esk1_0)),esk1_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_18]),c_0_12])])).

cnf(c_0_20,negated_conjecture,
    ( r1_tarski(k3_relat_1(k2_wellord1(esk2_0,esk1_0)),esk1_0) ),
    inference(spm,[status(thm)],[c_0_15,c_0_19])).

cnf(c_0_21,negated_conjecture,
    ( ~ r1_tarski(k3_relat_1(k2_wellord1(esk2_0,esk1_0)),k3_relat_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_6,c_0_20])])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(esk3_2(k3_relat_1(k2_wellord1(esk2_0,esk1_0)),k3_relat_1(esk2_0)),k3_relat_1(k2_wellord1(esk2_0,esk1_0))) ),
    inference(spm,[status(thm)],[c_0_21,c_0_7])).

cnf(c_0_23,negated_conjecture,
    ( r2_hidden(esk3_2(k3_relat_1(k2_wellord1(esk2_0,esk1_0)),k3_relat_1(esk2_0)),k3_relat_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_22]),c_0_12])])).

cnf(c_0_24,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_23]),c_0_21]),
    [proof]).
%------------------------------------------------------------------------------
