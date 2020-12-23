%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : relat_1__t179_relat_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:55 EDT 2019

% Result     : Theorem 181.77s
% Output     : CNFRefutation 181.77s
% Verified   : 
% Statistics : Number of formulae       :   28 (  52 expanded)
%              Number of clauses        :   21 (  23 expanded)
%              Number of leaves         :    3 (  12 expanded)
%              Depth                    :    9
%              Number of atoms          :  104 ( 247 expanded)
%              Number of equality atoms :   10 (  24 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t179_relat_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => ( r1_tarski(X2,X3)
           => r1_tarski(k10_relat_1(X2,X1),k10_relat_1(X3,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t179_relat_1.p',t179_relat_1)).

fof(d14_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2,X3] :
          ( X3 = k10_relat_1(X1,X2)
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r2_hidden(k4_tarski(X4,X5),X1)
                  & r2_hidden(X5,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t179_relat_1.p',d14_relat_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t179_relat_1.p',d3_tarski)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ! [X3] :
            ( v1_relat_1(X3)
           => ( r1_tarski(X2,X3)
             => r1_tarski(k10_relat_1(X2,X1),k10_relat_1(X3,X1)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t179_relat_1])).

fof(c_0_4,plain,(
    ! [X11,X12,X13,X14,X16,X17,X18,X19,X21] :
      ( ( r2_hidden(k4_tarski(X14,esk4_4(X11,X12,X13,X14)),X11)
        | ~ r2_hidden(X14,X13)
        | X13 != k10_relat_1(X11,X12)
        | ~ v1_relat_1(X11) )
      & ( r2_hidden(esk4_4(X11,X12,X13,X14),X12)
        | ~ r2_hidden(X14,X13)
        | X13 != k10_relat_1(X11,X12)
        | ~ v1_relat_1(X11) )
      & ( ~ r2_hidden(k4_tarski(X16,X17),X11)
        | ~ r2_hidden(X17,X12)
        | r2_hidden(X16,X13)
        | X13 != k10_relat_1(X11,X12)
        | ~ v1_relat_1(X11) )
      & ( ~ r2_hidden(esk5_3(X11,X18,X19),X19)
        | ~ r2_hidden(k4_tarski(esk5_3(X11,X18,X19),X21),X11)
        | ~ r2_hidden(X21,X18)
        | X19 = k10_relat_1(X11,X18)
        | ~ v1_relat_1(X11) )
      & ( r2_hidden(k4_tarski(esk5_3(X11,X18,X19),esk6_3(X11,X18,X19)),X11)
        | r2_hidden(esk5_3(X11,X18,X19),X19)
        | X19 = k10_relat_1(X11,X18)
        | ~ v1_relat_1(X11) )
      & ( r2_hidden(esk6_3(X11,X18,X19),X18)
        | r2_hidden(esk5_3(X11,X18,X19),X19)
        | X19 = k10_relat_1(X11,X18)
        | ~ v1_relat_1(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d14_relat_1])])])])])])).

fof(c_0_5,plain,(
    ! [X23,X24,X25,X26,X27] :
      ( ( ~ r1_tarski(X23,X24)
        | ~ r2_hidden(X25,X23)
        | r2_hidden(X25,X24) )
      & ( r2_hidden(esk7_2(X26,X27),X26)
        | r1_tarski(X26,X27) )
      & ( ~ r2_hidden(esk7_2(X26,X27),X27)
        | r1_tarski(X26,X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_6,negated_conjecture,
    ( v1_relat_1(esk2_0)
    & v1_relat_1(esk3_0)
    & r1_tarski(esk2_0,esk3_0)
    & ~ r1_tarski(k10_relat_1(esk2_0,esk1_0),k10_relat_1(esk3_0,esk1_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])).

cnf(c_0_7,plain,
    ( r2_hidden(k4_tarski(X1,esk4_4(X2,X3,X4,X1)),X2)
    | ~ r2_hidden(X1,X4)
    | X4 != k10_relat_1(X2,X3)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,negated_conjecture,
    ( r1_tarski(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( r2_hidden(k4_tarski(X1,esk4_4(X2,X3,k10_relat_1(X2,X3),X1)),X2)
    | ~ r2_hidden(X1,k10_relat_1(X2,X3))
    | ~ v1_relat_1(X2) ),
    inference(er,[status(thm)],[c_0_7])).

cnf(c_0_11,plain,
    ( r2_hidden(esk7_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_12,plain,
    ( r2_hidden(X1,X5)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(X2,X4)
    | X5 != k10_relat_1(X3,X4)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_13,negated_conjecture,
    ( r2_hidden(X1,esk3_0)
    | ~ r2_hidden(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_8,c_0_9])).

cnf(c_0_14,plain,
    ( r2_hidden(k4_tarski(esk7_2(k10_relat_1(X1,X2),X3),esk4_4(X1,X2,k10_relat_1(X1,X2),esk7_2(k10_relat_1(X1,X2),X3))),X1)
    | r1_tarski(k10_relat_1(X1,X2),X3)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_15,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_16,plain,
    ( r2_hidden(esk4_4(X1,X2,X3,X4),X2)
    | ~ r2_hidden(X4,X3)
    | X3 != k10_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_17,plain,
    ( r2_hidden(X1,k10_relat_1(X2,X3))
    | ~ r2_hidden(k4_tarski(X1,X4),X2)
    | ~ r2_hidden(X4,X3)
    | ~ v1_relat_1(X2) ),
    inference(er,[status(thm)],[c_0_12])).

cnf(c_0_18,negated_conjecture,
    ( r2_hidden(k4_tarski(esk7_2(k10_relat_1(esk2_0,X1),X2),esk4_4(esk2_0,X1,k10_relat_1(esk2_0,X1),esk7_2(k10_relat_1(esk2_0,X1),X2))),esk3_0)
    | r1_tarski(k10_relat_1(esk2_0,X1),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15])])).

cnf(c_0_19,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_20,plain,
    ( r2_hidden(esk4_4(X1,X2,k10_relat_1(X1,X2),X3),X2)
    | ~ r2_hidden(X3,k10_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( r2_hidden(esk7_2(k10_relat_1(esk2_0,X1),X2),k10_relat_1(esk3_0,X3))
    | r1_tarski(k10_relat_1(esk2_0,X1),X2)
    | ~ r2_hidden(esk4_4(esk2_0,X1,k10_relat_1(esk2_0,X1),esk7_2(k10_relat_1(esk2_0,X1),X2)),X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19])])).

cnf(c_0_22,plain,
    ( r2_hidden(esk4_4(X1,X2,k10_relat_1(X1,X2),esk7_2(k10_relat_1(X1,X2),X3)),X2)
    | r1_tarski(k10_relat_1(X1,X2),X3)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_11])).

cnf(c_0_23,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk7_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(esk7_2(k10_relat_1(esk2_0,X1),X2),k10_relat_1(esk3_0,X1))
    | r1_tarski(k10_relat_1(esk2_0,X1),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_15])])).

cnf(c_0_25,negated_conjecture,
    ( ~ r1_tarski(k10_relat_1(esk2_0,esk1_0),k10_relat_1(esk3_0,esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_26,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk2_0,X1),k10_relat_1(esk3_0,X1)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_27,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_26])]),
    [proof]).
%------------------------------------------------------------------------------
