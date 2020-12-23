%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : relat_1__t116_relat_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:48 EDT 2019

% Result     : Theorem 151.15s
% Output     : CNFRefutation 151.15s
% Verified   : 
% Statistics : Number of formulae       :   15 (  20 expanded)
%              Number of clauses        :    8 (   8 expanded)
%              Number of leaves         :    3 (   5 expanded)
%              Depth                    :    5
%              Number of atoms          :   45 (  61 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t115_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k2_relat_1(k8_relat_1(X2,X3)))
      <=> ( r2_hidden(X1,X2)
          & r2_hidden(X1,k2_relat_1(X3)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t116_relat_1.p',t115_relat_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t116_relat_1.p',d3_tarski)).

fof(t116_relat_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k2_relat_1(k8_relat_1(X1,X2)),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t116_relat_1.p',t116_relat_1)).

fof(c_0_3,plain,(
    ! [X18,X19,X20] :
      ( ( r2_hidden(X18,X19)
        | ~ r2_hidden(X18,k2_relat_1(k8_relat_1(X19,X20)))
        | ~ v1_relat_1(X20) )
      & ( r2_hidden(X18,k2_relat_1(X20))
        | ~ r2_hidden(X18,k2_relat_1(k8_relat_1(X19,X20)))
        | ~ v1_relat_1(X20) )
      & ( ~ r2_hidden(X18,X19)
        | ~ r2_hidden(X18,k2_relat_1(X20))
        | r2_hidden(X18,k2_relat_1(k8_relat_1(X19,X20)))
        | ~ v1_relat_1(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t115_relat_1])])])).

fof(c_0_4,plain,(
    ! [X8,X9,X10,X11,X12] :
      ( ( ~ r1_tarski(X8,X9)
        | ~ r2_hidden(X10,X8)
        | r2_hidden(X10,X9) )
      & ( r2_hidden(esk3_2(X11,X12),X11)
        | r1_tarski(X11,X12) )
      & ( ~ r2_hidden(esk3_2(X11,X12),X12)
        | r1_tarski(X11,X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => r1_tarski(k2_relat_1(k8_relat_1(X1,X2)),X1) ) ),
    inference(assume_negation,[status(cth)],[t116_relat_1])).

cnf(c_0_6,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k2_relat_1(k8_relat_1(X2,X3)))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_7,plain,
    ( r2_hidden(esk3_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

fof(c_0_8,negated_conjecture,
    ( v1_relat_1(esk2_0)
    & ~ r1_tarski(k2_relat_1(k8_relat_1(esk1_0,esk2_0)),esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

cnf(c_0_9,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk3_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_10,plain,
    ( r2_hidden(esk3_2(k2_relat_1(k8_relat_1(X1,X2)),X3),X1)
    | r1_tarski(k2_relat_1(k8_relat_1(X1,X2)),X3)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_6,c_0_7])).

cnf(c_0_11,negated_conjecture,
    ( ~ r1_tarski(k2_relat_1(k8_relat_1(esk1_0,esk2_0)),esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,plain,
    ( r1_tarski(k2_relat_1(k8_relat_1(X1,X2)),X1)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_13,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_12]),c_0_13])]),
    [proof]).
%------------------------------------------------------------------------------
