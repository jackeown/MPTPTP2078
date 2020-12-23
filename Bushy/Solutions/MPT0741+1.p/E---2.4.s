%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : ordinal1__t31_ordinal1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:25 EDT 2019

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   31 (  89 expanded)
%              Number of clauses        :   20 (  35 expanded)
%              Number of leaves         :    5 (  23 expanded)
%              Depth                    :    7
%              Number of atoms          :  104 ( 379 expanded)
%              Number of equality atoms :    7 (  19 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t31_ordinal1,conjecture,(
    ! [X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X1)
         => ( v3_ordinal1(X2)
            & r1_tarski(X2,X1) ) )
     => v3_ordinal1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/ordinal1__t31_ordinal1.p',t31_ordinal1)).

fof(d2_ordinal1,axiom,(
    ! [X1] :
      ( v1_ordinal1(X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
         => r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/ordinal1__t31_ordinal1.p',d2_ordinal1)).

fof(d3_ordinal1,axiom,(
    ! [X1] :
      ( v2_ordinal1(X1)
    <=> ! [X2,X3] :
          ~ ( r2_hidden(X2,X1)
            & r2_hidden(X3,X1)
            & ~ r2_hidden(X2,X3)
            & X2 != X3
            & ~ r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/ordinal1__t31_ordinal1.p',d3_ordinal1)).

fof(d4_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
    <=> ( v1_ordinal1(X1)
        & v2_ordinal1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/ordinal1__t31_ordinal1.p',d4_ordinal1)).

fof(t24_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ~ ( ~ r2_hidden(X1,X2)
              & X1 != X2
              & ~ r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/ordinal1__t31_ordinal1.p',t24_ordinal1)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1] :
        ( ! [X2] :
            ( r2_hidden(X2,X1)
           => ( v3_ordinal1(X2)
              & r1_tarski(X2,X1) ) )
       => v3_ordinal1(X1) ) ),
    inference(assume_negation,[status(cth)],[t31_ordinal1])).

fof(c_0_6,negated_conjecture,(
    ! [X5] :
      ( ( v3_ordinal1(X5)
        | ~ r2_hidden(X5,esk1_0) )
      & ( r1_tarski(X5,esk1_0)
        | ~ r2_hidden(X5,esk1_0) )
      & ~ v3_ordinal1(esk1_0) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])])])).

fof(c_0_7,plain,(
    ! [X8,X9,X10] :
      ( ( ~ v1_ordinal1(X8)
        | ~ r2_hidden(X9,X8)
        | r1_tarski(X9,X8) )
      & ( r2_hidden(esk2_1(X10),X10)
        | v1_ordinal1(X10) )
      & ( ~ r1_tarski(esk2_1(X10),X10)
        | v1_ordinal1(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_ordinal1])])])])])])).

fof(c_0_8,plain,(
    ! [X12,X13,X14,X15] :
      ( ( ~ v2_ordinal1(X12)
        | ~ r2_hidden(X13,X12)
        | ~ r2_hidden(X14,X12)
        | r2_hidden(X13,X14)
        | X13 = X14
        | r2_hidden(X14,X13) )
      & ( r2_hidden(esk3_1(X15),X15)
        | v2_ordinal1(X15) )
      & ( r2_hidden(esk4_1(X15),X15)
        | v2_ordinal1(X15) )
      & ( ~ r2_hidden(esk3_1(X15),esk4_1(X15))
        | v2_ordinal1(X15) )
      & ( esk3_1(X15) != esk4_1(X15)
        | v2_ordinal1(X15) )
      & ( ~ r2_hidden(esk4_1(X15),esk3_1(X15))
        | v2_ordinal1(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d3_ordinal1])])])])])])])).

fof(c_0_9,plain,(
    ! [X18] :
      ( ( v1_ordinal1(X18)
        | ~ v3_ordinal1(X18) )
      & ( v2_ordinal1(X18)
        | ~ v3_ordinal1(X18) )
      & ( ~ v1_ordinal1(X18)
        | ~ v2_ordinal1(X18)
        | v3_ordinal1(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_ordinal1])])])).

cnf(c_0_10,negated_conjecture,
    ( r1_tarski(X1,esk1_0)
    | ~ r2_hidden(X1,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( r2_hidden(esk2_1(X1),X1)
    | v1_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( v1_ordinal1(X1)
    | ~ r1_tarski(esk2_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_13,plain,(
    ! [X23,X24] :
      ( ~ v3_ordinal1(X23)
      | ~ v3_ordinal1(X24)
      | r2_hidden(X23,X24)
      | X23 = X24
      | r2_hidden(X24,X23) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t24_ordinal1])])])])).

cnf(c_0_14,negated_conjecture,
    ( v3_ordinal1(X1)
    | ~ r2_hidden(X1,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_15,plain,
    ( r2_hidden(esk4_1(X1),X1)
    | v2_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_16,plain,
    ( v3_ordinal1(X1)
    | ~ v1_ordinal1(X1)
    | ~ v2_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_17,negated_conjecture,
    ( v1_ordinal1(esk1_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_11]),c_0_12])).

cnf(c_0_18,negated_conjecture,
    ( ~ v3_ordinal1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_19,plain,
    ( r2_hidden(esk3_1(X1),X1)
    | v2_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_20,plain,
    ( v2_ordinal1(X1)
    | ~ r2_hidden(esk4_1(X1),esk3_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_21,plain,
    ( r2_hidden(X1,X2)
    | X1 = X2
    | r2_hidden(X2,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,plain,
    ( v2_ordinal1(X1)
    | ~ r2_hidden(esk3_1(X1),esk4_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_23,plain,
    ( v2_ordinal1(X1)
    | esk3_1(X1) != esk4_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_24,negated_conjecture,
    ( v2_ordinal1(esk1_0)
    | v3_ordinal1(esk4_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_25,negated_conjecture,
    ( ~ v2_ordinal1(esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18])).

cnf(c_0_26,negated_conjecture,
    ( v2_ordinal1(esk1_0)
    | v3_ordinal1(esk3_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_14,c_0_19])).

cnf(c_0_27,plain,
    ( v2_ordinal1(X1)
    | ~ v3_ordinal1(esk4_1(X1))
    | ~ v3_ordinal1(esk3_1(X1)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22]),c_0_23])).

cnf(c_0_28,negated_conjecture,
    ( v3_ordinal1(esk4_1(esk1_0)) ),
    inference(sr,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_29,negated_conjecture,
    ( v3_ordinal1(esk3_1(esk1_0)) ),
    inference(sr,[status(thm)],[c_0_26,c_0_25])).

cnf(c_0_30,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29])]),c_0_25]),
    [proof]).
%------------------------------------------------------------------------------
