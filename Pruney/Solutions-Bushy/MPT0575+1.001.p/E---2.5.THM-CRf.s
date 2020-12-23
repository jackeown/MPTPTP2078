%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0575+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:39:51 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   31 (  55 expanded)
%              Number of clauses        :   24 (  26 expanded)
%              Number of leaves         :    3 (  12 expanded)
%              Depth                    :    9
%              Number of atoms          :  109 ( 252 expanded)
%              Number of equality atoms :   10 (  24 expanded)
%              Maximal formula depth    :   19 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d14_relat_1)).

fof(t179_relat_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => ( r1_tarski(X2,X3)
           => r1_tarski(k10_relat_1(X2,X1),k10_relat_1(X3,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t179_relat_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(c_0_3,plain,(
    ! [X6,X7,X8,X9,X11,X12,X13,X14,X16] :
      ( ( r2_hidden(k4_tarski(X9,esk1_4(X6,X7,X8,X9)),X6)
        | ~ r2_hidden(X9,X8)
        | X8 != k10_relat_1(X6,X7)
        | ~ v1_relat_1(X6) )
      & ( r2_hidden(esk1_4(X6,X7,X8,X9),X7)
        | ~ r2_hidden(X9,X8)
        | X8 != k10_relat_1(X6,X7)
        | ~ v1_relat_1(X6) )
      & ( ~ r2_hidden(k4_tarski(X11,X12),X6)
        | ~ r2_hidden(X12,X7)
        | r2_hidden(X11,X8)
        | X8 != k10_relat_1(X6,X7)
        | ~ v1_relat_1(X6) )
      & ( ~ r2_hidden(esk2_3(X6,X13,X14),X14)
        | ~ r2_hidden(k4_tarski(esk2_3(X6,X13,X14),X16),X6)
        | ~ r2_hidden(X16,X13)
        | X14 = k10_relat_1(X6,X13)
        | ~ v1_relat_1(X6) )
      & ( r2_hidden(k4_tarski(esk2_3(X6,X13,X14),esk3_3(X6,X13,X14)),X6)
        | r2_hidden(esk2_3(X6,X13,X14),X14)
        | X14 = k10_relat_1(X6,X13)
        | ~ v1_relat_1(X6) )
      & ( r2_hidden(esk3_3(X6,X13,X14),X13)
        | r2_hidden(esk2_3(X6,X13,X14),X14)
        | X14 = k10_relat_1(X6,X13)
        | ~ v1_relat_1(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d14_relat_1])])])])])])).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ! [X3] :
            ( v1_relat_1(X3)
           => ( r1_tarski(X2,X3)
             => r1_tarski(k10_relat_1(X2,X1),k10_relat_1(X3,X1)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t179_relat_1])).

cnf(c_0_5,plain,
    ( r2_hidden(esk1_4(X1,X2,X3,X4),X2)
    | ~ r2_hidden(X4,X3)
    | X3 != k10_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

fof(c_0_6,negated_conjecture,
    ( v1_relat_1(esk6_0)
    & v1_relat_1(esk7_0)
    & r1_tarski(esk6_0,esk7_0)
    & ~ r1_tarski(k10_relat_1(esk6_0,esk5_0),k10_relat_1(esk7_0,esk5_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).

cnf(c_0_7,plain,
    ( r2_hidden(k4_tarski(X1,esk1_4(X2,X3,X4,X1)),X2)
    | ~ r2_hidden(X1,X4)
    | X4 != k10_relat_1(X2,X3)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_8,plain,
    ( r2_hidden(X1,X5)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(X2,X4)
    | X5 != k10_relat_1(X3,X4)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_9,plain,
    ( r2_hidden(esk1_4(X1,X2,k10_relat_1(X1,X2),X3),X2)
    | ~ r2_hidden(X3,k10_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_5])).

cnf(c_0_10,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_11,plain,(
    ! [X18,X19,X20,X21,X22] :
      ( ( ~ r1_tarski(X18,X19)
        | ~ r2_hidden(X20,X18)
        | r2_hidden(X20,X19) )
      & ( r2_hidden(esk4_2(X21,X22),X21)
        | r1_tarski(X21,X22) )
      & ( ~ r2_hidden(esk4_2(X21,X22),X22)
        | r1_tarski(X21,X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_12,plain,
    ( r2_hidden(k4_tarski(X1,esk1_4(X2,X3,k10_relat_1(X2,X3),X1)),X2)
    | ~ r2_hidden(X1,k10_relat_1(X2,X3))
    | ~ v1_relat_1(X2) ),
    inference(er,[status(thm)],[c_0_7])).

cnf(c_0_13,plain,
    ( r2_hidden(X1,k10_relat_1(X2,X3))
    | ~ r2_hidden(k4_tarski(X1,X4),X2)
    | ~ r2_hidden(X4,X3)
    | ~ v1_relat_1(X2) ),
    inference(er,[status(thm)],[c_0_8])).

cnf(c_0_14,negated_conjecture,
    ( v1_relat_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_15,negated_conjecture,
    ( r2_hidden(esk1_4(esk6_0,X1,k10_relat_1(esk6_0,X1),X2),X1)
    | ~ r2_hidden(X2,k10_relat_1(esk6_0,X1)) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_16,plain,
    ( r2_hidden(esk4_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,negated_conjecture,
    ( r1_tarski(esk6_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_19,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,esk1_4(esk6_0,X2,k10_relat_1(esk6_0,X2),X1)),esk6_0)
    | ~ r2_hidden(X1,k10_relat_1(esk6_0,X2)) ),
    inference(spm,[status(thm)],[c_0_12,c_0_10])).

cnf(c_0_20,negated_conjecture,
    ( r2_hidden(X1,k10_relat_1(esk7_0,X2))
    | ~ r2_hidden(k4_tarski(X1,X3),esk7_0)
    | ~ r2_hidden(X3,X2) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_21,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk6_0,X1),X2)
    | r2_hidden(esk1_4(esk6_0,X1,k10_relat_1(esk6_0,X1),esk4_2(k10_relat_1(esk6_0,X1),X2)),X1) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(X1,esk7_0)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk6_0,X1),X2)
    | r2_hidden(k4_tarski(esk4_2(k10_relat_1(esk6_0,X1),X2),esk1_4(esk6_0,X1,k10_relat_1(esk6_0,X1),esk4_2(k10_relat_1(esk6_0,X1),X2))),esk6_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_16])).

cnf(c_0_24,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk6_0,X1),X2)
    | r2_hidden(X3,k10_relat_1(esk7_0,X1))
    | ~ r2_hidden(k4_tarski(X3,esk1_4(esk6_0,X1,k10_relat_1(esk6_0,X1),esk4_2(k10_relat_1(esk6_0,X1),X2))),esk7_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_25,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk6_0,X1),X2)
    | r2_hidden(k4_tarski(esk4_2(k10_relat_1(esk6_0,X1),X2),esk1_4(esk6_0,X1,k10_relat_1(esk6_0,X1),esk4_2(k10_relat_1(esk6_0,X1),X2))),esk7_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_26,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk4_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_27,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk6_0,X1),X2)
    | r2_hidden(esk4_2(k10_relat_1(esk6_0,X1),X2),k10_relat_1(esk7_0,X1)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_28,negated_conjecture,
    ( ~ r1_tarski(k10_relat_1(esk6_0,esk5_0),k10_relat_1(esk7_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_29,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk6_0,X1),k10_relat_1(esk7_0,X1)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_30,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_29])]),
    [proof]).

%------------------------------------------------------------------------------
