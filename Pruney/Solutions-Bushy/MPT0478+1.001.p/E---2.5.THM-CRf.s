%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0478+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:39:41 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   25 (  57 expanded)
%              Number of clauses        :   16 (  25 expanded)
%              Number of leaves         :    4 (  14 expanded)
%              Depth                    :    7
%              Number of atoms          :   90 ( 205 expanded)
%              Number of equality atoms :   17 (  29 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t73_relat_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( ! [X3] :
            ( r2_hidden(X3,X1)
           => r2_hidden(k4_tarski(X3,X3),X2) )
       => r1_tarski(k6_relat_1(X1),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_relat_1)).

fof(d3_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( r1_tarski(X1,X2)
        <=> ! [X3,X4] :
              ( r2_hidden(k4_tarski(X3,X4),X1)
             => r2_hidden(k4_tarski(X3,X4),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_relat_1)).

fof(dt_k6_relat_1,axiom,(
    ! [X1] : v1_relat_1(k6_relat_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(d10_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( X2 = k6_relat_1(X1)
      <=> ! [X3,X4] :
            ( r2_hidden(k4_tarski(X3,X4),X2)
          <=> ( r2_hidden(X3,X1)
              & X3 = X4 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_relat_1)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ( ! [X3] :
              ( r2_hidden(X3,X1)
             => r2_hidden(k4_tarski(X3,X3),X2) )
         => r1_tarski(k6_relat_1(X1),X2) ) ) ),
    inference(assume_negation,[status(cth)],[t73_relat_1])).

fof(c_0_5,plain,(
    ! [X13,X14,X15,X16,X17] :
      ( ( ~ r1_tarski(X13,X14)
        | ~ r2_hidden(k4_tarski(X15,X16),X13)
        | r2_hidden(k4_tarski(X15,X16),X14)
        | ~ v1_relat_1(X13) )
      & ( r2_hidden(k4_tarski(esk3_2(X13,X17),esk4_2(X13,X17)),X13)
        | r1_tarski(X13,X17)
        | ~ v1_relat_1(X13) )
      & ( ~ r2_hidden(k4_tarski(esk3_2(X13,X17),esk4_2(X13,X17)),X17)
        | r1_tarski(X13,X17)
        | ~ v1_relat_1(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_relat_1])])])])])])).

fof(c_0_6,plain,(
    ! [X20] : v1_relat_1(k6_relat_1(X20)) ),
    inference(variable_rename,[status(thm)],[dt_k6_relat_1])).

fof(c_0_7,plain,(
    ! [X5,X6,X7,X8,X9,X10] :
      ( ( r2_hidden(X7,X5)
        | ~ r2_hidden(k4_tarski(X7,X8),X6)
        | X6 != k6_relat_1(X5)
        | ~ v1_relat_1(X6) )
      & ( X7 = X8
        | ~ r2_hidden(k4_tarski(X7,X8),X6)
        | X6 != k6_relat_1(X5)
        | ~ v1_relat_1(X6) )
      & ( ~ r2_hidden(X9,X5)
        | X9 != X10
        | r2_hidden(k4_tarski(X9,X10),X6)
        | X6 != k6_relat_1(X5)
        | ~ v1_relat_1(X6) )
      & ( ~ r2_hidden(k4_tarski(esk1_2(X5,X6),esk2_2(X5,X6)),X6)
        | ~ r2_hidden(esk1_2(X5,X6),X5)
        | esk1_2(X5,X6) != esk2_2(X5,X6)
        | X6 = k6_relat_1(X5)
        | ~ v1_relat_1(X6) )
      & ( r2_hidden(esk1_2(X5,X6),X5)
        | r2_hidden(k4_tarski(esk1_2(X5,X6),esk2_2(X5,X6)),X6)
        | X6 = k6_relat_1(X5)
        | ~ v1_relat_1(X6) )
      & ( esk1_2(X5,X6) = esk2_2(X5,X6)
        | r2_hidden(k4_tarski(esk1_2(X5,X6),esk2_2(X5,X6)),X6)
        | X6 = k6_relat_1(X5)
        | ~ v1_relat_1(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_relat_1])])])])])])).

fof(c_0_8,negated_conjecture,(
    ! [X23] :
      ( v1_relat_1(esk6_0)
      & ( ~ r2_hidden(X23,esk5_0)
        | r2_hidden(k4_tarski(X23,X23),esk6_0) )
      & ~ r1_tarski(k6_relat_1(esk5_0),esk6_0) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])])).

cnf(c_0_9,plain,
    ( r2_hidden(k4_tarski(esk3_2(X1,X2),esk4_2(X1,X2)),X1)
    | r1_tarski(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_10,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( X1 = X2
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X3 != k6_relat_1(X4)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,negated_conjecture,
    ( ~ r1_tarski(k6_relat_1(esk5_0),esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( r1_tarski(k6_relat_1(X1),X2)
    | r2_hidden(k4_tarski(esk3_2(k6_relat_1(X1),X2),esk4_2(k6_relat_1(X1),X2)),k6_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_14,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),X4)
    | X4 != k6_relat_1(X2)
    | ~ v1_relat_1(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_15,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(k4_tarski(esk3_2(X1,X2),esk4_2(X1,X2)),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_16,plain,
    ( X1 = X2
    | ~ r2_hidden(k4_tarski(X1,X2),k6_relat_1(X3)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_11]),c_0_10])])).

cnf(c_0_17,negated_conjecture,
    ( r2_hidden(k4_tarski(esk3_2(k6_relat_1(esk5_0),esk6_0),esk4_2(k6_relat_1(esk5_0),esk6_0)),k6_relat_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_18,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),k6_relat_1(X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_14]),c_0_10])])).

cnf(c_0_19,plain,
    ( r1_tarski(k6_relat_1(X1),X2)
    | ~ r2_hidden(k4_tarski(esk3_2(k6_relat_1(X1),X2),esk4_2(k6_relat_1(X1),X2)),X2) ),
    inference(spm,[status(thm)],[c_0_15,c_0_10])).

cnf(c_0_20,negated_conjecture,
    ( esk4_2(k6_relat_1(esk5_0),esk6_0) = esk3_2(k6_relat_1(esk5_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_21,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,X1),esk6_0)
    | ~ r2_hidden(X1,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(esk3_2(k6_relat_1(esk5_0),esk6_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_17])).

cnf(c_0_23,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(esk3_2(k6_relat_1(esk5_0),esk6_0),esk3_2(k6_relat_1(esk5_0),esk6_0)),esk6_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_12])).

cnf(c_0_24,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23]),
    [proof]).

%------------------------------------------------------------------------------
