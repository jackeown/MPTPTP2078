%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0402+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:39:34 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   30 (  72 expanded)
%              Number of clauses        :   19 (  30 expanded)
%              Number of leaves         :    5 (  17 expanded)
%              Depth                    :   11
%              Number of atoms          :  103 ( 252 expanded)
%              Number of equality atoms :   28 (  47 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t25_setfam_1,conjecture,(
    ! [X1,X2,X3] :
      ( r1_setfam_1(X3,k2_tarski(X1,X2))
     => ! [X4] :
          ~ ( r2_hidden(X4,X3)
            & ~ r1_tarski(X4,X1)
            & ~ r1_tarski(X4,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_setfam_1)).

fof(t41_enumset1,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

fof(d2_setfam_1,axiom,(
    ! [X1,X2] :
      ( r1_setfam_1(X1,X2)
    <=> ! [X3] :
          ~ ( r2_hidden(X3,X1)
            & ! [X4] :
                ~ ( r2_hidden(X4,X2)
                  & r1_tarski(X3,X4) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_setfam_1)).

fof(d3_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            | r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( r1_setfam_1(X3,k2_tarski(X1,X2))
       => ! [X4] :
            ~ ( r2_hidden(X4,X3)
              & ~ r1_tarski(X4,X1)
              & ~ r1_tarski(X4,X2) ) ) ),
    inference(assume_negation,[status(cth)],[t25_setfam_1])).

fof(c_0_6,negated_conjecture,
    ( r1_setfam_1(esk7_0,k2_tarski(esk5_0,esk6_0))
    & r2_hidden(esk8_0,esk7_0)
    & ~ r1_tarski(esk8_0,esk5_0)
    & ~ r1_tarski(esk8_0,esk6_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_5])])])])).

fof(c_0_7,plain,(
    ! [X29,X30] : k2_tarski(X29,X30) = k2_xboole_0(k1_tarski(X29),k1_tarski(X30)) ),
    inference(variable_rename,[status(thm)],[t41_enumset1])).

fof(c_0_8,plain,(
    ! [X12,X13,X14,X16,X17,X19] :
      ( ( r2_hidden(esk2_3(X12,X13,X14),X13)
        | ~ r2_hidden(X14,X12)
        | ~ r1_setfam_1(X12,X13) )
      & ( r1_tarski(X14,esk2_3(X12,X13,X14))
        | ~ r2_hidden(X14,X12)
        | ~ r1_setfam_1(X12,X13) )
      & ( r2_hidden(esk3_2(X16,X17),X16)
        | r1_setfam_1(X16,X17) )
      & ( ~ r2_hidden(X19,X17)
        | ~ r1_tarski(esk3_2(X16,X17),X19)
        | r1_setfam_1(X16,X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_setfam_1])])])])])])).

cnf(c_0_9,negated_conjecture,
    ( r1_setfam_1(esk7_0,k2_tarski(esk5_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_11,plain,(
    ! [X20,X21,X22,X23,X24,X25,X26,X27] :
      ( ( ~ r2_hidden(X23,X22)
        | r2_hidden(X23,X20)
        | r2_hidden(X23,X21)
        | X22 != k2_xboole_0(X20,X21) )
      & ( ~ r2_hidden(X24,X20)
        | r2_hidden(X24,X22)
        | X22 != k2_xboole_0(X20,X21) )
      & ( ~ r2_hidden(X24,X21)
        | r2_hidden(X24,X22)
        | X22 != k2_xboole_0(X20,X21) )
      & ( ~ r2_hidden(esk4_3(X25,X26,X27),X25)
        | ~ r2_hidden(esk4_3(X25,X26,X27),X27)
        | X27 = k2_xboole_0(X25,X26) )
      & ( ~ r2_hidden(esk4_3(X25,X26,X27),X26)
        | ~ r2_hidden(esk4_3(X25,X26,X27),X27)
        | X27 = k2_xboole_0(X25,X26) )
      & ( r2_hidden(esk4_3(X25,X26,X27),X27)
        | r2_hidden(esk4_3(X25,X26,X27),X25)
        | r2_hidden(esk4_3(X25,X26,X27),X26)
        | X27 = k2_xboole_0(X25,X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).

cnf(c_0_12,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X2)
    | ~ r2_hidden(X3,X1)
    | ~ r1_setfam_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,negated_conjecture,
    ( r1_setfam_1(esk7_0,k2_xboole_0(k1_tarski(esk5_0),k1_tarski(esk6_0))) ),
    inference(rw,[status(thm)],[c_0_9,c_0_10])).

fof(c_0_14,plain,(
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

cnf(c_0_15,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_xboole_0(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( r2_hidden(esk2_3(esk7_0,k2_xboole_0(k1_tarski(esk5_0),k1_tarski(esk6_0)),X1),k2_xboole_0(k1_tarski(esk5_0),k1_tarski(esk6_0)))
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_17,negated_conjecture,
    ( r2_hidden(esk8_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_18,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,plain,
    ( r2_hidden(X1,X2)
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,k2_xboole_0(X3,X2)) ),
    inference(er,[status(thm)],[c_0_15])).

cnf(c_0_20,negated_conjecture,
    ( r2_hidden(esk2_3(esk7_0,k2_xboole_0(k1_tarski(esk5_0),k1_tarski(esk6_0)),esk8_0),k2_xboole_0(k1_tarski(esk5_0),k1_tarski(esk6_0))) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_21,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k1_tarski(X2)) ),
    inference(er,[status(thm)],[c_0_18])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(esk2_3(esk7_0,k2_xboole_0(k1_tarski(esk5_0),k1_tarski(esk6_0)),esk8_0),k1_tarski(esk6_0))
    | r2_hidden(esk2_3(esk7_0,k2_xboole_0(k1_tarski(esk5_0),k1_tarski(esk6_0)),esk8_0),k1_tarski(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_23,negated_conjecture,
    ( esk2_3(esk7_0,k2_xboole_0(k1_tarski(esk5_0),k1_tarski(esk6_0)),esk8_0) = esk6_0
    | r2_hidden(esk2_3(esk7_0,k2_xboole_0(k1_tarski(esk5_0),k1_tarski(esk6_0)),esk8_0),k1_tarski(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_24,plain,
    ( r1_tarski(X1,esk2_3(X2,X3,X1))
    | ~ r2_hidden(X1,X2)
    | ~ r1_setfam_1(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_25,negated_conjecture,
    ( esk2_3(esk7_0,k2_xboole_0(k1_tarski(esk5_0),k1_tarski(esk6_0)),esk8_0) = esk6_0
    | esk2_3(esk7_0,k2_xboole_0(k1_tarski(esk5_0),k1_tarski(esk6_0)),esk8_0) = esk5_0 ),
    inference(spm,[status(thm)],[c_0_21,c_0_23])).

cnf(c_0_26,negated_conjecture,
    ( ~ r1_tarski(esk8_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_27,negated_conjecture,
    ( esk2_3(esk7_0,k2_xboole_0(k1_tarski(esk5_0),k1_tarski(esk6_0)),esk8_0) = esk5_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_13]),c_0_17])]),c_0_26])).

cnf(c_0_28,negated_conjecture,
    ( ~ r1_tarski(esk8_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_29,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_27]),c_0_13]),c_0_17])]),c_0_28]),
    [proof]).

%------------------------------------------------------------------------------
