%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0400+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:39:34 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   23 (  41 expanded)
%              Number of clauses        :   16 (  18 expanded)
%              Number of leaves         :    3 (  10 expanded)
%              Depth                    :   10
%              Number of atoms          :   75 ( 174 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(d2_setfam_1,axiom,(
    ! [X1,X2] :
      ( r1_setfam_1(X1,X2)
    <=> ! [X3] :
          ~ ( r2_hidden(X3,X1)
            & ! [X4] :
                ~ ( r2_hidden(X4,X2)
                  & r1_tarski(X3,X4) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_setfam_1)).

fof(t23_setfam_1,conjecture,(
    ! [X1,X2,X3] :
      ( ( r1_setfam_1(X1,X2)
        & r1_setfam_1(X2,X3) )
     => r1_setfam_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_setfam_1)).

fof(c_0_3,plain,(
    ! [X13,X14,X15] :
      ( ~ r1_tarski(X13,X14)
      | ~ r1_tarski(X14,X15)
      | r1_tarski(X13,X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

fof(c_0_4,plain,(
    ! [X5,X6,X7,X9,X10,X12] :
      ( ( r2_hidden(esk1_3(X5,X6,X7),X6)
        | ~ r2_hidden(X7,X5)
        | ~ r1_setfam_1(X5,X6) )
      & ( r1_tarski(X7,esk1_3(X5,X6,X7))
        | ~ r2_hidden(X7,X5)
        | ~ r1_setfam_1(X5,X6) )
      & ( r2_hidden(esk2_2(X9,X10),X9)
        | r1_setfam_1(X9,X10) )
      & ( ~ r2_hidden(X12,X10)
        | ~ r1_tarski(esk2_2(X9,X10),X12)
        | r1_setfam_1(X9,X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_setfam_1])])])])])])).

cnf(c_0_5,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_6,plain,
    ( r1_tarski(X1,esk1_3(X2,X3,X1))
    | ~ r2_hidden(X1,X2)
    | ~ r1_setfam_1(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_7,plain,
    ( r1_setfam_1(X3,X2)
    | ~ r2_hidden(X1,X2)
    | ~ r1_tarski(esk2_2(X3,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,plain,
    ( r1_tarski(X1,esk1_3(X2,X3,X4))
    | ~ r1_tarski(X1,X4)
    | ~ r2_hidden(X4,X2)
    | ~ r1_setfam_1(X2,X3) ),
    inference(spm,[status(thm)],[c_0_5,c_0_6])).

cnf(c_0_9,plain,
    ( r1_setfam_1(X1,X2)
    | ~ r1_tarski(esk2_2(X1,X2),X3)
    | ~ r2_hidden(esk1_3(X4,X5,X3),X2)
    | ~ r2_hidden(X3,X4)
    | ~ r1_setfam_1(X4,X5) ),
    inference(spm,[status(thm)],[c_0_7,c_0_8])).

cnf(c_0_10,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | ~ r2_hidden(X3,X1)
    | ~ r1_setfam_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_11,plain,
    ( r1_setfam_1(X1,X2)
    | ~ r1_tarski(esk2_2(X1,X2),X3)
    | ~ r2_hidden(X3,X4)
    | ~ r1_setfam_1(X4,X2) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_12,plain,
    ( r1_setfam_1(X1,X2)
    | ~ r2_hidden(esk1_3(X3,X4,esk2_2(X1,X2)),X5)
    | ~ r2_hidden(esk2_2(X1,X2),X3)
    | ~ r1_setfam_1(X5,X2)
    | ~ r1_setfam_1(X3,X4) ),
    inference(spm,[status(thm)],[c_0_11,c_0_6])).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( r1_setfam_1(X1,X2)
          & r1_setfam_1(X2,X3) )
       => r1_setfam_1(X1,X3) ) ),
    inference(assume_negation,[status(cth)],[t23_setfam_1])).

cnf(c_0_14,plain,
    ( r1_setfam_1(X1,X2)
    | ~ r2_hidden(esk2_2(X1,X2),X3)
    | ~ r1_setfam_1(X4,X2)
    | ~ r1_setfam_1(X3,X4) ),
    inference(spm,[status(thm)],[c_0_12,c_0_10])).

cnf(c_0_15,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_setfam_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

fof(c_0_16,negated_conjecture,
    ( r1_setfam_1(esk3_0,esk4_0)
    & r1_setfam_1(esk4_0,esk5_0)
    & ~ r1_setfam_1(esk3_0,esk5_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).

cnf(c_0_17,plain,
    ( r1_setfam_1(X1,X2)
    | ~ r1_setfam_1(X3,X2)
    | ~ r1_setfam_1(X1,X3) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_18,negated_conjecture,
    ( r1_setfam_1(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_19,negated_conjecture,
    ( ~ r1_setfam_1(esk3_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( r1_setfam_1(X1,esk5_0)
    | ~ r1_setfam_1(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_21,negated_conjecture,
    ( r1_setfam_1(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21])]),
    [proof]).

%------------------------------------------------------------------------------
