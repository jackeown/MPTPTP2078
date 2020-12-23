%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0496+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:39:43 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   38 ( 152 expanded)
%              Number of clauses        :   27 (  64 expanded)
%              Number of leaves         :    5 (  36 expanded)
%              Depth                    :   14
%              Number of atoms          :  151 ( 566 expanded)
%              Number of equality atoms :   30 ( 116 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal clause size      :   32 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t94_relat_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,X1) = k5_relat_1(k6_relat_1(X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(d11_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2,X3] :
          ( v1_relat_1(X3)
         => ( X3 = k7_relat_1(X1,X2)
          <=> ! [X4,X5] :
                ( r2_hidden(k4_tarski(X4,X5),X3)
              <=> ( r2_hidden(X4,X2)
                  & r2_hidden(k4_tarski(X4,X5),X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_relat_1)).

fof(dt_k5_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X2) )
     => v1_relat_1(k5_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(dt_k6_relat_1,axiom,(
    ! [X1] : v1_relat_1(k6_relat_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(t74_relat_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( v1_relat_1(X4)
     => ( r2_hidden(k4_tarski(X1,X2),k5_relat_1(k6_relat_1(X3),X4))
      <=> ( r2_hidden(X1,X3)
          & r2_hidden(k4_tarski(X1,X2),X4) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_relat_1)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => k7_relat_1(X2,X1) = k5_relat_1(k6_relat_1(X1),X2) ) ),
    inference(assume_negation,[status(cth)],[t94_relat_1])).

fof(c_0_6,plain,(
    ! [X6,X7,X8,X9,X10,X11,X12] :
      ( ( r2_hidden(X9,X7)
        | ~ r2_hidden(k4_tarski(X9,X10),X8)
        | X8 != k7_relat_1(X6,X7)
        | ~ v1_relat_1(X8)
        | ~ v1_relat_1(X6) )
      & ( r2_hidden(k4_tarski(X9,X10),X6)
        | ~ r2_hidden(k4_tarski(X9,X10),X8)
        | X8 != k7_relat_1(X6,X7)
        | ~ v1_relat_1(X8)
        | ~ v1_relat_1(X6) )
      & ( ~ r2_hidden(X11,X7)
        | ~ r2_hidden(k4_tarski(X11,X12),X6)
        | r2_hidden(k4_tarski(X11,X12),X8)
        | X8 != k7_relat_1(X6,X7)
        | ~ v1_relat_1(X8)
        | ~ v1_relat_1(X6) )
      & ( ~ r2_hidden(k4_tarski(esk1_3(X6,X7,X8),esk2_3(X6,X7,X8)),X8)
        | ~ r2_hidden(esk1_3(X6,X7,X8),X7)
        | ~ r2_hidden(k4_tarski(esk1_3(X6,X7,X8),esk2_3(X6,X7,X8)),X6)
        | X8 = k7_relat_1(X6,X7)
        | ~ v1_relat_1(X8)
        | ~ v1_relat_1(X6) )
      & ( r2_hidden(esk1_3(X6,X7,X8),X7)
        | r2_hidden(k4_tarski(esk1_3(X6,X7,X8),esk2_3(X6,X7,X8)),X8)
        | X8 = k7_relat_1(X6,X7)
        | ~ v1_relat_1(X8)
        | ~ v1_relat_1(X6) )
      & ( r2_hidden(k4_tarski(esk1_3(X6,X7,X8),esk2_3(X6,X7,X8)),X6)
        | r2_hidden(k4_tarski(esk1_3(X6,X7,X8),esk2_3(X6,X7,X8)),X8)
        | X8 = k7_relat_1(X6,X7)
        | ~ v1_relat_1(X8)
        | ~ v1_relat_1(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d11_relat_1])])])])])])).

fof(c_0_7,negated_conjecture,
    ( v1_relat_1(esk4_0)
    & k7_relat_1(esk4_0,esk3_0) != k5_relat_1(k6_relat_1(esk3_0),esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

cnf(c_0_8,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | r2_hidden(k4_tarski(esk1_3(X1,X2,X3),esk2_3(X1,X2,X3)),X3)
    | X3 = k7_relat_1(X1,X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_9,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_10,plain,(
    ! [X15,X16] :
      ( ~ v1_relat_1(X15)
      | ~ v1_relat_1(X16)
      | v1_relat_1(k5_relat_1(X15,X16)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_relat_1])])).

cnf(c_0_11,negated_conjecture,
    ( X1 = k7_relat_1(esk4_0,X2)
    | r2_hidden(k4_tarski(esk1_3(esk4_0,X2,X1),esk2_3(esk4_0,X2,X1)),X1)
    | r2_hidden(esk1_3(esk4_0,X2,X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_8,c_0_9])).

cnf(c_0_12,plain,
    ( v1_relat_1(k5_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_13,negated_conjecture,
    ( k5_relat_1(X1,X2) = k7_relat_1(esk4_0,X3)
    | r2_hidden(k4_tarski(esk1_3(esk4_0,X3,k5_relat_1(X1,X2)),esk2_3(esk4_0,X3,k5_relat_1(X1,X2))),k5_relat_1(X1,X2))
    | r2_hidden(esk1_3(esk4_0,X3,k5_relat_1(X1,X2)),X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

fof(c_0_14,plain,(
    ! [X17] : v1_relat_1(k6_relat_1(X17)) ),
    inference(variable_rename,[status(thm)],[dt_k6_relat_1])).

cnf(c_0_15,plain,
    ( r2_hidden(k4_tarski(esk1_3(X1,X2,X3),esk2_3(X1,X2,X3)),X1)
    | r2_hidden(k4_tarski(esk1_3(X1,X2,X3),esk2_3(X1,X2,X3)),X3)
    | X3 = k7_relat_1(X1,X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_16,plain,(
    ! [X18,X19,X20,X21] :
      ( ( r2_hidden(X18,X20)
        | ~ r2_hidden(k4_tarski(X18,X19),k5_relat_1(k6_relat_1(X20),X21))
        | ~ v1_relat_1(X21) )
      & ( r2_hidden(k4_tarski(X18,X19),X21)
        | ~ r2_hidden(k4_tarski(X18,X19),k5_relat_1(k6_relat_1(X20),X21))
        | ~ v1_relat_1(X21) )
      & ( ~ r2_hidden(X18,X20)
        | ~ r2_hidden(k4_tarski(X18,X19),X21)
        | r2_hidden(k4_tarski(X18,X19),k5_relat_1(k6_relat_1(X20),X21))
        | ~ v1_relat_1(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t74_relat_1])])])).

cnf(c_0_17,negated_conjecture,
    ( k5_relat_1(X1,esk4_0) = k7_relat_1(esk4_0,X2)
    | r2_hidden(k4_tarski(esk1_3(esk4_0,X2,k5_relat_1(X1,esk4_0)),esk2_3(esk4_0,X2,k5_relat_1(X1,esk4_0))),k5_relat_1(X1,esk4_0))
    | r2_hidden(esk1_3(esk4_0,X2,k5_relat_1(X1,esk4_0)),X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_13,c_0_9])).

cnf(c_0_18,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,negated_conjecture,
    ( X1 = k7_relat_1(esk4_0,X2)
    | r2_hidden(k4_tarski(esk1_3(esk4_0,X2,X1),esk2_3(esk4_0,X2,X1)),esk4_0)
    | r2_hidden(k4_tarski(esk1_3(esk4_0,X2,X1),esk2_3(esk4_0,X2,X1)),X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_15,c_0_9])).

cnf(c_0_20,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),k5_relat_1(k6_relat_1(X2),X4))
    | ~ v1_relat_1(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( k5_relat_1(k6_relat_1(X1),esk4_0) = k7_relat_1(esk4_0,X2)
    | r2_hidden(k4_tarski(esk1_3(esk4_0,X2,k5_relat_1(k6_relat_1(X1),esk4_0)),esk2_3(esk4_0,X2,k5_relat_1(k6_relat_1(X1),esk4_0))),k5_relat_1(k6_relat_1(X1),esk4_0))
    | r2_hidden(esk1_3(esk4_0,X2,k5_relat_1(k6_relat_1(X1),esk4_0)),X2) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_22,negated_conjecture,
    ( k5_relat_1(X1,X2) = k7_relat_1(esk4_0,X3)
    | r2_hidden(k4_tarski(esk1_3(esk4_0,X3,k5_relat_1(X1,X2)),esk2_3(esk4_0,X3,k5_relat_1(X1,X2))),k5_relat_1(X1,X2))
    | r2_hidden(k4_tarski(esk1_3(esk4_0,X3,k5_relat_1(X1,X2)),esk2_3(esk4_0,X3,k5_relat_1(X1,X2))),esk4_0)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_12])).

cnf(c_0_23,negated_conjecture,
    ( k5_relat_1(k6_relat_1(X1),esk4_0) = k7_relat_1(esk4_0,X2)
    | r2_hidden(esk1_3(esk4_0,X2,k5_relat_1(k6_relat_1(X1),esk4_0)),X2)
    | r2_hidden(esk1_3(esk4_0,X2,k5_relat_1(k6_relat_1(X1),esk4_0)),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_9])])).

cnf(c_0_24,negated_conjecture,
    ( k5_relat_1(X1,esk4_0) = k7_relat_1(esk4_0,X2)
    | r2_hidden(k4_tarski(esk1_3(esk4_0,X2,k5_relat_1(X1,esk4_0)),esk2_3(esk4_0,X2,k5_relat_1(X1,esk4_0))),k5_relat_1(X1,esk4_0))
    | r2_hidden(k4_tarski(esk1_3(esk4_0,X2,k5_relat_1(X1,esk4_0)),esk2_3(esk4_0,X2,k5_relat_1(X1,esk4_0))),esk4_0)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_9])).

cnf(c_0_25,plain,
    ( X3 = k7_relat_1(X1,X2)
    | ~ r2_hidden(k4_tarski(esk1_3(X1,X2,X3),esk2_3(X1,X2,X3)),X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X2)
    | ~ r2_hidden(k4_tarski(esk1_3(X1,X2,X3),esk2_3(X1,X2,X3)),X1)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_26,negated_conjecture,
    ( k5_relat_1(k6_relat_1(X1),esk4_0) = k7_relat_1(esk4_0,X1)
    | r2_hidden(esk1_3(esk4_0,X1,k5_relat_1(k6_relat_1(X1),esk4_0)),X1) ),
    inference(ef,[status(thm)],[c_0_23])).

cnf(c_0_27,plain,
    ( r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(k4_tarski(X1,X2),k5_relat_1(k6_relat_1(X4),X3))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_28,negated_conjecture,
    ( k5_relat_1(k6_relat_1(X1),esk4_0) = k7_relat_1(esk4_0,X2)
    | r2_hidden(k4_tarski(esk1_3(esk4_0,X2,k5_relat_1(k6_relat_1(X1),esk4_0)),esk2_3(esk4_0,X2,k5_relat_1(k6_relat_1(X1),esk4_0))),k5_relat_1(k6_relat_1(X1),esk4_0))
    | r2_hidden(k4_tarski(esk1_3(esk4_0,X2,k5_relat_1(k6_relat_1(X1),esk4_0)),esk2_3(esk4_0,X2,k5_relat_1(k6_relat_1(X1),esk4_0))),esk4_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_18])).

cnf(c_0_29,negated_conjecture,
    ( k5_relat_1(k6_relat_1(X1),esk4_0) = k7_relat_1(esk4_0,X1)
    | ~ r2_hidden(k4_tarski(esk1_3(esk4_0,X1,k5_relat_1(k6_relat_1(X1),esk4_0)),esk2_3(esk4_0,X1,k5_relat_1(k6_relat_1(X1),esk4_0))),k5_relat_1(k6_relat_1(X1),esk4_0))
    | ~ r2_hidden(k4_tarski(esk1_3(esk4_0,X1,k5_relat_1(k6_relat_1(X1),esk4_0)),esk2_3(esk4_0,X1,k5_relat_1(k6_relat_1(X1),esk4_0))),esk4_0)
    | ~ v1_relat_1(k5_relat_1(k6_relat_1(X1),esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_9])])).

cnf(c_0_30,plain,
    ( r2_hidden(k4_tarski(X1,X3),k5_relat_1(k6_relat_1(X2),X4))
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),X4)
    | ~ v1_relat_1(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_31,negated_conjecture,
    ( k5_relat_1(k6_relat_1(X1),esk4_0) = k7_relat_1(esk4_0,X2)
    | r2_hidden(k4_tarski(esk1_3(esk4_0,X2,k5_relat_1(k6_relat_1(X1),esk4_0)),esk2_3(esk4_0,X2,k5_relat_1(k6_relat_1(X1),esk4_0))),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_9])])).

cnf(c_0_32,negated_conjecture,
    ( k5_relat_1(k6_relat_1(X1),esk4_0) = k7_relat_1(esk4_0,X1)
    | ~ r2_hidden(k4_tarski(esk1_3(esk4_0,X1,k5_relat_1(k6_relat_1(X1),esk4_0)),esk2_3(esk4_0,X1,k5_relat_1(k6_relat_1(X1),esk4_0))),k5_relat_1(k6_relat_1(X1),esk4_0))
    | ~ r2_hidden(k4_tarski(esk1_3(esk4_0,X1,k5_relat_1(k6_relat_1(X1),esk4_0)),esk2_3(esk4_0,X1,k5_relat_1(k6_relat_1(X1),esk4_0))),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_12]),c_0_9]),c_0_18])])).

cnf(c_0_33,negated_conjecture,
    ( k5_relat_1(k6_relat_1(X1),esk4_0) = k7_relat_1(esk4_0,X2)
    | r2_hidden(k4_tarski(esk1_3(esk4_0,X2,k5_relat_1(k6_relat_1(X1),esk4_0)),esk2_3(esk4_0,X2,k5_relat_1(k6_relat_1(X1),esk4_0))),k5_relat_1(k6_relat_1(X3),esk4_0))
    | ~ r2_hidden(esk1_3(esk4_0,X2,k5_relat_1(k6_relat_1(X1),esk4_0)),X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_9])])).

cnf(c_0_34,negated_conjecture,
    ( k5_relat_1(k6_relat_1(X1),esk4_0) = k7_relat_1(esk4_0,X1)
    | ~ r2_hidden(k4_tarski(esk1_3(esk4_0,X1,k5_relat_1(k6_relat_1(X1),esk4_0)),esk2_3(esk4_0,X1,k5_relat_1(k6_relat_1(X1),esk4_0))),k5_relat_1(k6_relat_1(X1),esk4_0)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_31])).

cnf(c_0_35,negated_conjecture,
    ( k7_relat_1(esk4_0,esk3_0) != k5_relat_1(k6_relat_1(esk3_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_36,negated_conjecture,
    ( k5_relat_1(k6_relat_1(X1),esk4_0) = k7_relat_1(esk4_0,X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_26]),c_0_34])).

cnf(c_0_37,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_36])]),
    [proof]).

%------------------------------------------------------------------------------
