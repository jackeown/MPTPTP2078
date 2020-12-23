%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0562+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:39:49 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   24 (  70 expanded)
%              Number of clauses        :   17 (  28 expanded)
%              Number of leaves         :    3 (  16 expanded)
%              Depth                    :    9
%              Number of atoms          :  120 ( 458 expanded)
%              Number of equality atoms :   23 (  54 expanded)
%              Maximal formula depth    :   19 (   6 average)
%              Maximal clause size      :   26 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t166_relat_1,conjecture,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k10_relat_1(X3,X2))
      <=> ? [X4] :
            ( r2_hidden(X4,k2_relat_1(X3))
            & r2_hidden(k4_tarski(X1,X4),X3)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

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

fof(d5_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k2_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X4,X3),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( v1_relat_1(X3)
       => ( r2_hidden(X1,k10_relat_1(X3,X2))
        <=> ? [X4] :
              ( r2_hidden(X4,k2_relat_1(X3))
              & r2_hidden(k4_tarski(X1,X4),X3)
              & r2_hidden(X4,X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t166_relat_1])).

fof(c_0_4,plain,(
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

fof(c_0_5,negated_conjecture,(
    ! [X32] :
      ( v1_relat_1(esk9_0)
      & ( ~ r2_hidden(esk7_0,k10_relat_1(esk9_0,esk8_0))
        | ~ r2_hidden(X32,k2_relat_1(esk9_0))
        | ~ r2_hidden(k4_tarski(esk7_0,X32),esk9_0)
        | ~ r2_hidden(X32,esk8_0) )
      & ( r2_hidden(esk10_0,k2_relat_1(esk9_0))
        | r2_hidden(esk7_0,k10_relat_1(esk9_0,esk8_0)) )
      & ( r2_hidden(k4_tarski(esk7_0,esk10_0),esk9_0)
        | r2_hidden(esk7_0,k10_relat_1(esk9_0,esk8_0)) )
      & ( r2_hidden(esk10_0,esk8_0)
        | r2_hidden(esk7_0,k10_relat_1(esk9_0,esk8_0)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])])])).

cnf(c_0_6,plain,
    ( r2_hidden(X1,X5)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(X2,X4)
    | X5 != k10_relat_1(X3,X4)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_7,negated_conjecture,
    ( r2_hidden(k4_tarski(esk7_0,esk10_0),esk9_0)
    | r2_hidden(esk7_0,k10_relat_1(esk9_0,esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_8,negated_conjecture,
    ( v1_relat_1(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,negated_conjecture,
    ( ~ r2_hidden(esk7_0,k10_relat_1(esk9_0,esk8_0))
    | ~ r2_hidden(X1,k2_relat_1(esk9_0))
    | ~ r2_hidden(k4_tarski(esk7_0,X1),esk9_0)
    | ~ r2_hidden(X1,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_10,plain,
    ( r2_hidden(k4_tarski(X1,esk1_4(X2,X3,X4,X1)),X2)
    | ~ r2_hidden(X1,X4)
    | X4 != k10_relat_1(X2,X3)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_11,negated_conjecture,
    ( r2_hidden(esk7_0,k10_relat_1(esk9_0,esk8_0))
    | r2_hidden(esk7_0,X1)
    | X1 != k10_relat_1(esk9_0,X2)
    | ~ r2_hidden(esk10_0,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_6,c_0_7]),c_0_8])])).

cnf(c_0_12,negated_conjecture,
    ( X1 != k10_relat_1(esk9_0,X2)
    | ~ r2_hidden(esk1_4(esk9_0,X2,X1,esk7_0),k2_relat_1(esk9_0))
    | ~ r2_hidden(esk1_4(esk9_0,X2,X1,esk7_0),esk8_0)
    | ~ r2_hidden(esk7_0,k10_relat_1(esk9_0,esk8_0))
    | ~ r2_hidden(esk7_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_10]),c_0_8])])).

cnf(c_0_13,plain,
    ( r2_hidden(esk1_4(X1,X2,X3,X4),X2)
    | ~ r2_hidden(X4,X3)
    | X3 != k10_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_14,negated_conjecture,
    ( r2_hidden(esk7_0,k10_relat_1(esk9_0,esk8_0))
    | r2_hidden(esk7_0,k10_relat_1(esk9_0,X1))
    | ~ r2_hidden(esk10_0,X1) ),
    inference(er,[status(thm)],[c_0_11])).

cnf(c_0_15,negated_conjecture,
    ( r2_hidden(esk10_0,esk8_0)
    | r2_hidden(esk7_0,k10_relat_1(esk9_0,esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_16,plain,(
    ! [X18,X19,X20,X22,X23,X24,X25,X27] :
      ( ( ~ r2_hidden(X20,X19)
        | r2_hidden(k4_tarski(esk4_3(X18,X19,X20),X20),X18)
        | X19 != k2_relat_1(X18) )
      & ( ~ r2_hidden(k4_tarski(X23,X22),X18)
        | r2_hidden(X22,X19)
        | X19 != k2_relat_1(X18) )
      & ( ~ r2_hidden(esk5_2(X24,X25),X25)
        | ~ r2_hidden(k4_tarski(X27,esk5_2(X24,X25)),X24)
        | X25 = k2_relat_1(X24) )
      & ( r2_hidden(esk5_2(X24,X25),X25)
        | r2_hidden(k4_tarski(esk6_2(X24,X25),esk5_2(X24,X25)),X24)
        | X25 = k2_relat_1(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).

cnf(c_0_17,negated_conjecture,
    ( X1 != k10_relat_1(esk9_0,esk8_0)
    | ~ r2_hidden(esk1_4(esk9_0,esk8_0,X1,esk7_0),k2_relat_1(esk9_0))
    | ~ r2_hidden(esk7_0,k10_relat_1(esk9_0,esk8_0))
    | ~ r2_hidden(esk7_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_8])])).

cnf(c_0_18,negated_conjecture,
    ( r2_hidden(esk7_0,k10_relat_1(esk9_0,esk8_0)) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_19,plain,
    ( r2_hidden(X2,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( X1 != k10_relat_1(esk9_0,esk8_0)
    | ~ r2_hidden(esk1_4(esk9_0,esk8_0,X1,esk7_0),k2_relat_1(esk9_0))
    | ~ r2_hidden(esk7_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_17,c_0_18])])).

cnf(c_0_21,plain,
    ( r2_hidden(esk1_4(X1,X2,X3,X4),X5)
    | X3 != k10_relat_1(X1,X2)
    | X5 != k2_relat_1(X1)
    | ~ r2_hidden(X4,X3)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_10])).

cnf(c_0_22,negated_conjecture,
    ( X1 != k10_relat_1(esk9_0,esk8_0)
    | ~ r2_hidden(esk7_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_8])])).

cnf(c_0_23,negated_conjecture,
    ( $false ),
    inference(spm,[status(thm)],[c_0_22,c_0_18]),
    [proof]).

%------------------------------------------------------------------------------
