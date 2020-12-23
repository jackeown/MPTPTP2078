%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0771+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:10 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   19 (  36 expanded)
%              Number of clauses        :   12 (  15 expanded)
%              Number of leaves         :    3 (   9 expanded)
%              Depth                    :    6
%              Number of atoms          :   54 ( 117 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t19_wellord1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k3_relat_1(k2_wellord1(X3,X2)))
       => ( r2_hidden(X1,k3_relat_1(X3))
          & r2_hidden(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_wellord1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t20_wellord1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k3_relat_1(k2_wellord1(X2,X1)),k3_relat_1(X2))
        & r1_tarski(k3_relat_1(k2_wellord1(X2,X1)),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_wellord1)).

fof(c_0_3,plain,(
    ! [X10,X11,X12] :
      ( ( r2_hidden(X10,k3_relat_1(X12))
        | ~ r2_hidden(X10,k3_relat_1(k2_wellord1(X12,X11)))
        | ~ v1_relat_1(X12) )
      & ( r2_hidden(X10,X11)
        | ~ r2_hidden(X10,k3_relat_1(k2_wellord1(X12,X11)))
        | ~ v1_relat_1(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_wellord1])])])).

fof(c_0_4,plain,(
    ! [X4,X5,X6,X7,X8] :
      ( ( ~ r1_tarski(X4,X5)
        | ~ r2_hidden(X6,X4)
        | r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_2(X7,X8),X7)
        | r1_tarski(X7,X8) )
      & ( ~ r2_hidden(esk1_2(X7,X8),X8)
        | r1_tarski(X7,X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(k3_relat_1(k2_wellord1(X2,X1)),k3_relat_1(X2))
          & r1_tarski(k3_relat_1(k2_wellord1(X2,X1)),X1) ) ) ),
    inference(assume_negation,[status(cth)],[t20_wellord1])).

cnf(c_0_6,plain,
    ( r2_hidden(X1,k3_relat_1(X2))
    | ~ r2_hidden(X1,k3_relat_1(k2_wellord1(X2,X3)))
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_7,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

fof(c_0_8,negated_conjecture,
    ( v1_relat_1(esk3_0)
    & ( ~ r1_tarski(k3_relat_1(k2_wellord1(esk3_0,esk2_0)),k3_relat_1(esk3_0))
      | ~ r1_tarski(k3_relat_1(k2_wellord1(esk3_0,esk2_0)),esk2_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

cnf(c_0_9,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_10,plain,
    ( r2_hidden(esk1_2(k3_relat_1(k2_wellord1(X1,X2)),X3),k3_relat_1(X1))
    | r1_tarski(k3_relat_1(k2_wellord1(X1,X2)),X3)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_6,c_0_7])).

cnf(c_0_11,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_relat_1(k2_wellord1(X3,X2)))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_12,negated_conjecture,
    ( ~ r1_tarski(k3_relat_1(k2_wellord1(esk3_0,esk2_0)),k3_relat_1(esk3_0))
    | ~ r1_tarski(k3_relat_1(k2_wellord1(esk3_0,esk2_0)),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( r1_tarski(k3_relat_1(k2_wellord1(X1,X2)),k3_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_14,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,plain,
    ( r2_hidden(esk1_2(k3_relat_1(k2_wellord1(X1,X2)),X3),X2)
    | r1_tarski(k3_relat_1(k2_wellord1(X1,X2)),X3)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_11,c_0_7])).

cnf(c_0_16,negated_conjecture,
    ( ~ r1_tarski(k3_relat_1(k2_wellord1(esk3_0,esk2_0)),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_14])])).

cnf(c_0_17,plain,
    ( r1_tarski(k3_relat_1(k2_wellord1(X1,X2)),X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_9,c_0_15])).

cnf(c_0_18,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_14])]),
    [proof]).

%------------------------------------------------------------------------------
