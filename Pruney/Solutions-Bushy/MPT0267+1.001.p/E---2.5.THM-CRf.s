%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0267+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:39:19 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   27 (  81 expanded)
%              Number of clauses        :   20 (  40 expanded)
%              Number of leaves         :    3 (  17 expanded)
%              Depth                    :    8
%              Number of atoms          :   95 ( 391 expanded)
%              Number of equality atoms :   34 ( 130 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(t64_zfmisc_1,conjecture,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))
    <=> ( r2_hidden(X1,X2)
        & X1 != X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(c_0_3,plain,(
    ! [X12,X13,X14,X15,X16,X17,X18,X19] :
      ( ( r2_hidden(X15,X12)
        | ~ r2_hidden(X15,X14)
        | X14 != k4_xboole_0(X12,X13) )
      & ( ~ r2_hidden(X15,X13)
        | ~ r2_hidden(X15,X14)
        | X14 != k4_xboole_0(X12,X13) )
      & ( ~ r2_hidden(X16,X12)
        | r2_hidden(X16,X13)
        | r2_hidden(X16,X14)
        | X14 != k4_xboole_0(X12,X13) )
      & ( ~ r2_hidden(esk2_3(X17,X18,X19),X19)
        | ~ r2_hidden(esk2_3(X17,X18,X19),X17)
        | r2_hidden(esk2_3(X17,X18,X19),X18)
        | X19 = k4_xboole_0(X17,X18) )
      & ( r2_hidden(esk2_3(X17,X18,X19),X17)
        | r2_hidden(esk2_3(X17,X18,X19),X19)
        | X19 = k4_xboole_0(X17,X18) )
      & ( ~ r2_hidden(esk2_3(X17,X18,X19),X18)
        | r2_hidden(esk2_3(X17,X18,X19),X19)
        | X19 = k4_xboole_0(X17,X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))
      <=> ( r2_hidden(X1,X2)
          & X1 != X3 ) ) ),
    inference(assume_negation,[status(cth)],[t64_zfmisc_1])).

cnf(c_0_5,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

fof(c_0_6,negated_conjecture,
    ( ( ~ r2_hidden(esk3_0,k4_xboole_0(esk4_0,k1_tarski(esk5_0)))
      | ~ r2_hidden(esk3_0,esk4_0)
      | esk3_0 = esk5_0 )
    & ( r2_hidden(esk3_0,esk4_0)
      | r2_hidden(esk3_0,k4_xboole_0(esk4_0,k1_tarski(esk5_0))) )
    & ( esk3_0 != esk5_0
      | r2_hidden(esk3_0,k4_xboole_0(esk4_0,k1_tarski(esk5_0))) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])])).

cnf(c_0_7,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k4_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_5])).

cnf(c_0_8,negated_conjecture,
    ( r2_hidden(esk3_0,esk4_0)
    | r2_hidden(esk3_0,k4_xboole_0(esk4_0,k1_tarski(esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_9,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | X4 != k4_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

fof(c_0_10,plain,(
    ! [X5,X6,X7,X8,X9,X10] :
      ( ( ~ r2_hidden(X7,X6)
        | X7 = X5
        | X6 != k1_tarski(X5) )
      & ( X8 != X5
        | r2_hidden(X8,X6)
        | X6 != k1_tarski(X5) )
      & ( ~ r2_hidden(esk1_2(X9,X10),X10)
        | esk1_2(X9,X10) != X9
        | X10 = k1_tarski(X9) )
      & ( r2_hidden(esk1_2(X9,X10),X10)
        | esk1_2(X9,X10) = X9
        | X10 = k1_tarski(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

cnf(c_0_11,negated_conjecture,
    ( esk3_0 = esk5_0
    | ~ r2_hidden(esk3_0,k4_xboole_0(esk4_0,k1_tarski(esk5_0)))
    | ~ r2_hidden(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_12,negated_conjecture,
    ( r2_hidden(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_7,c_0_8])).

cnf(c_0_13,plain,
    ( r2_hidden(X1,k4_xboole_0(X2,X3))
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,negated_conjecture,
    ( esk5_0 = esk3_0
    | ~ r2_hidden(esk3_0,k4_xboole_0(esk4_0,k1_tarski(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_11,c_0_12])])).

cnf(c_0_16,negated_conjecture,
    ( r2_hidden(esk3_0,k4_xboole_0(esk4_0,X1))
    | r2_hidden(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_13,c_0_12])).

cnf(c_0_17,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k1_tarski(X2)) ),
    inference(er,[status(thm)],[c_0_14])).

cnf(c_0_18,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_19,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_20,negated_conjecture,
    ( r2_hidden(esk3_0,k4_xboole_0(esk4_0,k1_tarski(esk5_0)))
    | esk3_0 != esk5_0 ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_21,negated_conjecture,
    ( esk5_0 = esk3_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17])).

cnf(c_0_22,plain,
    ( r2_hidden(X1,X2)
    | X2 != k1_tarski(X1) ),
    inference(er,[status(thm)],[c_0_18])).

cnf(c_0_23,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_19])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(esk3_0,k4_xboole_0(esk4_0,k1_tarski(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20,c_0_21]),c_0_21])])).

cnf(c_0_25,plain,
    ( r2_hidden(X1,k1_tarski(X1)) ),
    inference(er,[status(thm)],[c_0_22])).

cnf(c_0_26,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25])]),
    [proof]).

%------------------------------------------------------------------------------
