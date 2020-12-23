%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : ordinal1__t3_ordinal1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:27 EDT 2019

% Result     : Theorem 152.43s
% Output     : CNFRefutation 152.43s
% Verified   : 
% Statistics : Number of formulae       :   30 (  66 expanded)
%              Number of clauses        :   23 (  33 expanded)
%              Number of leaves         :    3 (  15 expanded)
%              Depth                    :   13
%              Number of atoms          :  102 ( 400 expanded)
%              Number of equality atoms :   49 ( 225 expanded)
%              Maximal formula depth    :   22 (   4 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d1_enumset1,axiom,(
    ! [X1,X2,X3,X4] :
      ( X4 = k1_enumset1(X1,X2,X3)
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ~ ( X5 != X1
              & X5 != X2
              & X5 != X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/ordinal1__t3_ordinal1.p',d1_enumset1)).

fof(t7_tarski,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & ! [X3] :
            ~ ( r2_hidden(X3,X2)
              & ! [X4] :
                  ~ ( r2_hidden(X4,X2)
                    & r2_hidden(X4,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/ordinal1__t3_ordinal1.p',t7_tarski)).

fof(t3_ordinal1,conjecture,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & r2_hidden(X2,X3)
        & r2_hidden(X3,X1) ) ),
    file('/export/starexec/sandbox/benchmark/ordinal1__t3_ordinal1.p',t3_ordinal1)).

fof(c_0_3,plain,(
    ! [X11,X12,X13,X14,X15,X16,X17,X18,X19,X20] :
      ( ( ~ r2_hidden(X15,X14)
        | X15 = X11
        | X15 = X12
        | X15 = X13
        | X14 != k1_enumset1(X11,X12,X13) )
      & ( X16 != X11
        | r2_hidden(X16,X14)
        | X14 != k1_enumset1(X11,X12,X13) )
      & ( X16 != X12
        | r2_hidden(X16,X14)
        | X14 != k1_enumset1(X11,X12,X13) )
      & ( X16 != X13
        | r2_hidden(X16,X14)
        | X14 != k1_enumset1(X11,X12,X13) )
      & ( esk4_4(X17,X18,X19,X20) != X17
        | ~ r2_hidden(esk4_4(X17,X18,X19,X20),X20)
        | X20 = k1_enumset1(X17,X18,X19) )
      & ( esk4_4(X17,X18,X19,X20) != X18
        | ~ r2_hidden(esk4_4(X17,X18,X19,X20),X20)
        | X20 = k1_enumset1(X17,X18,X19) )
      & ( esk4_4(X17,X18,X19,X20) != X19
        | ~ r2_hidden(esk4_4(X17,X18,X19,X20),X20)
        | X20 = k1_enumset1(X17,X18,X19) )
      & ( r2_hidden(esk4_4(X17,X18,X19,X20),X20)
        | esk4_4(X17,X18,X19,X20) = X17
        | esk4_4(X17,X18,X19,X20) = X18
        | esk4_4(X17,X18,X19,X20) = X19
        | X20 = k1_enumset1(X17,X18,X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).

fof(c_0_4,plain,(
    ! [X31,X32,X34] :
      ( ( r2_hidden(esk6_2(X31,X32),X32)
        | ~ r2_hidden(X31,X32) )
      & ( ~ r2_hidden(X34,X32)
        | ~ r2_hidden(X34,esk6_2(X31,X32))
        | ~ r2_hidden(X31,X32) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_tarski])])])])])).

cnf(c_0_5,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X4,X5,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_6,plain,
    ( X1 = X3
    | X1 = X4
    | X1 = X5
    | ~ r2_hidden(X1,X2)
    | X2 != k1_enumset1(X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_7,plain,
    ( r2_hidden(esk6_2(X1,X2),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,plain,
    ( r2_hidden(X1,k1_enumset1(X2,X3,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_5])])).

cnf(c_0_9,plain,
    ( X1 = X2
    | X1 = X3
    | X1 = X4
    | ~ r2_hidden(X1,k1_enumset1(X4,X3,X2)) ),
    inference(er,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( r2_hidden(esk6_2(X1,k1_enumset1(X2,X3,X1)),k1_enumset1(X2,X3,X1)) ),
    inference(spm,[status(thm)],[c_0_7,c_0_8])).

cnf(c_0_11,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,esk6_2(X3,X2))
    | ~ r2_hidden(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_12,plain,
    ( esk6_2(X1,k1_enumset1(X2,X3,X1)) = X1
    | esk6_2(X1,k1_enumset1(X2,X3,X1)) = X3
    | esk6_2(X1,k1_enumset1(X2,X3,X1)) = X2 ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ~ ( r2_hidden(X1,X2)
          & r2_hidden(X2,X3)
          & r2_hidden(X3,X1) ) ),
    inference(assume_negation,[status(cth)],[t3_ordinal1])).

cnf(c_0_14,plain,
    ( esk6_2(X1,k1_enumset1(X2,X3,X1)) = X3
    | esk6_2(X1,k1_enumset1(X2,X3,X1)) = X1
    | ~ r2_hidden(X4,k1_enumset1(X2,X3,X1))
    | ~ r2_hidden(X4,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_12]),c_0_8])])).

fof(c_0_15,negated_conjecture,
    ( r2_hidden(esk1_0,esk2_0)
    & r2_hidden(esk2_0,esk3_0)
    & r2_hidden(esk3_0,esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).

cnf(c_0_16,plain,
    ( esk6_2(X1,k1_enumset1(X2,X3,X1)) = X1
    | esk6_2(X1,k1_enumset1(X2,X3,X1)) = X3
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_14,c_0_8])).

cnf(c_0_17,negated_conjecture,
    ( r2_hidden(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_18,negated_conjecture,
    ( esk6_2(esk3_0,k1_enumset1(esk1_0,X1,esk3_0)) = esk3_0
    | esk6_2(esk3_0,k1_enumset1(esk1_0,X1,esk3_0)) = X1 ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_19,negated_conjecture,
    ( esk6_2(esk3_0,k1_enumset1(esk1_0,X1,esk3_0)) = X1
    | ~ r2_hidden(X2,k1_enumset1(esk1_0,X1,esk3_0))
    | ~ r2_hidden(X2,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_18]),c_0_8])])).

cnf(c_0_20,negated_conjecture,
    ( r2_hidden(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X4,X2,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_22,negated_conjecture,
    ( esk6_2(esk3_0,k1_enumset1(esk1_0,X1,esk3_0)) = X1
    | ~ r2_hidden(esk2_0,k1_enumset1(esk1_0,X1,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_23,plain,
    ( r2_hidden(X1,k1_enumset1(X2,X1,X3)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_21])])).

cnf(c_0_24,negated_conjecture,
    ( esk6_2(esk3_0,k1_enumset1(esk1_0,esk2_0,esk3_0)) = esk2_0 ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_25,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X2,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_26,negated_conjecture,
    ( ~ r2_hidden(X1,k1_enumset1(esk1_0,esk2_0,esk3_0))
    | ~ r2_hidden(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_24]),c_0_8])])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_28,plain,
    ( r2_hidden(X1,k1_enumset1(X1,X2,X3)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_25])])).

cnf(c_0_29,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28])]),
    [proof]).
%------------------------------------------------------------------------------
