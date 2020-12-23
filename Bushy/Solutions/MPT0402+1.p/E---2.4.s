%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : setfam_1__t25_setfam_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:16 EDT 2019

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   32 (  76 expanded)
%              Number of clauses        :   21 (  34 expanded)
%              Number of leaves         :    5 (  17 expanded)
%              Depth                    :   10
%              Number of atoms          :  106 ( 258 expanded)
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
    file('/export/starexec/sandbox/benchmark/setfam_1__t25_setfam_1.p',t25_setfam_1)).

fof(d2_setfam_1,axiom,(
    ! [X1,X2] :
      ( r1_setfam_1(X1,X2)
    <=> ! [X3] :
          ~ ( r2_hidden(X3,X1)
            & ! [X4] :
                ~ ( r2_hidden(X4,X2)
                  & r1_tarski(X3,X4) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/setfam_1__t25_setfam_1.p',d2_setfam_1)).

fof(t41_enumset1,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox/benchmark/setfam_1__t25_setfam_1.p',t41_enumset1)).

fof(d3_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            | r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/setfam_1__t25_setfam_1.p',d3_xboole_0)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/setfam_1__t25_setfam_1.p',d1_tarski)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( r1_setfam_1(X3,k2_tarski(X1,X2))
       => ! [X4] :
            ~ ( r2_hidden(X4,X3)
              & ~ r1_tarski(X4,X1)
              & ~ r1_tarski(X4,X2) ) ) ),
    inference(assume_negation,[status(cth)],[t25_setfam_1])).

fof(c_0_6,plain,(
    ! [X22,X23,X24,X26,X27,X29] :
      ( ( r2_hidden(esk6_3(X22,X23,X24),X23)
        | ~ r2_hidden(X24,X22)
        | ~ r1_setfam_1(X22,X23) )
      & ( r1_tarski(X24,esk6_3(X22,X23,X24))
        | ~ r2_hidden(X24,X22)
        | ~ r1_setfam_1(X22,X23) )
      & ( r2_hidden(esk7_2(X26,X27),X26)
        | r1_setfam_1(X26,X27) )
      & ( ~ r2_hidden(X29,X27)
        | ~ r1_tarski(esk7_2(X26,X27),X29)
        | r1_setfam_1(X26,X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_setfam_1])])])])])])).

fof(c_0_7,negated_conjecture,
    ( r1_setfam_1(esk3_0,k2_tarski(esk1_0,esk2_0))
    & r2_hidden(esk4_0,esk3_0)
    & ~ r1_tarski(esk4_0,esk1_0)
    & ~ r1_tarski(esk4_0,esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_5])])])])).

fof(c_0_8,plain,(
    ! [X50,X51] : k2_tarski(X50,X51) = k2_xboole_0(k1_tarski(X50),k1_tarski(X51)) ),
    inference(variable_rename,[status(thm)],[t41_enumset1])).

fof(c_0_9,plain,(
    ! [X30,X31,X32,X33,X34,X35,X36,X37] :
      ( ( ~ r2_hidden(X33,X32)
        | r2_hidden(X33,X30)
        | r2_hidden(X33,X31)
        | X32 != k2_xboole_0(X30,X31) )
      & ( ~ r2_hidden(X34,X30)
        | r2_hidden(X34,X32)
        | X32 != k2_xboole_0(X30,X31) )
      & ( ~ r2_hidden(X34,X31)
        | r2_hidden(X34,X32)
        | X32 != k2_xboole_0(X30,X31) )
      & ( ~ r2_hidden(esk8_3(X35,X36,X37),X35)
        | ~ r2_hidden(esk8_3(X35,X36,X37),X37)
        | X37 = k2_xboole_0(X35,X36) )
      & ( ~ r2_hidden(esk8_3(X35,X36,X37),X36)
        | ~ r2_hidden(esk8_3(X35,X36,X37),X37)
        | X37 = k2_xboole_0(X35,X36) )
      & ( r2_hidden(esk8_3(X35,X36,X37),X37)
        | r2_hidden(esk8_3(X35,X36,X37),X35)
        | r2_hidden(esk8_3(X35,X36,X37),X36)
        | X37 = k2_xboole_0(X35,X36) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).

cnf(c_0_10,plain,
    ( r2_hidden(esk6_3(X1,X2,X3),X2)
    | ~ r2_hidden(X3,X1)
    | ~ r1_setfam_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,negated_conjecture,
    ( r2_hidden(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,negated_conjecture,
    ( r1_setfam_1(esk3_0,k2_tarski(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,plain,
    ( k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_14,plain,(
    ! [X15,X16,X17,X18,X19,X20] :
      ( ( ~ r2_hidden(X17,X16)
        | X17 = X15
        | X16 != k1_tarski(X15) )
      & ( X18 != X15
        | r2_hidden(X18,X16)
        | X16 != k1_tarski(X15) )
      & ( ~ r2_hidden(esk5_2(X19,X20),X20)
        | esk5_2(X19,X20) != X19
        | X20 = k1_tarski(X19) )
      & ( r2_hidden(esk5_2(X19,X20),X20)
        | esk5_2(X19,X20) = X19
        | X20 = k1_tarski(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

cnf(c_0_15,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_xboole_0(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,negated_conjecture,
    ( r2_hidden(esk6_3(esk3_0,X1,esk4_0),X1)
    | ~ r1_setfam_1(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_17,negated_conjecture,
    ( r1_setfam_1(esk3_0,k2_xboole_0(k1_tarski(esk1_0),k1_tarski(esk2_0))) ),
    inference(rw,[status(thm)],[c_0_12,c_0_13])).

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
    ( r2_hidden(esk6_3(esk3_0,k2_xboole_0(k1_tarski(esk1_0),k1_tarski(esk2_0)),esk4_0),k2_xboole_0(k1_tarski(esk1_0),k1_tarski(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_21,plain,
    ( r1_tarski(X1,esk6_3(X2,X3,X1))
    | ~ r2_hidden(X1,X2)
    | ~ r1_setfam_1(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_22,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k1_tarski(X2)) ),
    inference(er,[status(thm)],[c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( r2_hidden(esk6_3(esk3_0,k2_xboole_0(k1_tarski(esk1_0),k1_tarski(esk2_0)),esk4_0),k1_tarski(esk2_0))
    | r2_hidden(esk6_3(esk3_0,k2_xboole_0(k1_tarski(esk1_0),k1_tarski(esk2_0)),esk4_0),k1_tarski(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_24,negated_conjecture,
    ( r1_tarski(esk4_0,esk6_3(esk3_0,X1,esk4_0))
    | ~ r1_setfam_1(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_11])).

cnf(c_0_25,negated_conjecture,
    ( esk6_3(esk3_0,k2_xboole_0(k1_tarski(esk1_0),k1_tarski(esk2_0)),esk4_0) = esk2_0
    | r2_hidden(esk6_3(esk3_0,k2_xboole_0(k1_tarski(esk1_0),k1_tarski(esk2_0)),esk4_0),k1_tarski(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_26,negated_conjecture,
    ( r1_tarski(esk4_0,esk6_3(esk3_0,k2_xboole_0(k1_tarski(esk1_0),k1_tarski(esk2_0)),esk4_0)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_17])).

cnf(c_0_27,negated_conjecture,
    ( esk6_3(esk3_0,k2_xboole_0(k1_tarski(esk1_0),k1_tarski(esk2_0)),esk4_0) = esk2_0
    | esk6_3(esk3_0,k2_xboole_0(k1_tarski(esk1_0),k1_tarski(esk2_0)),esk4_0) = esk1_0 ),
    inference(spm,[status(thm)],[c_0_22,c_0_25])).

cnf(c_0_28,negated_conjecture,
    ( ~ r1_tarski(esk4_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_29,negated_conjecture,
    ( esk6_3(esk3_0,k2_xboole_0(k1_tarski(esk1_0),k1_tarski(esk2_0)),esk4_0) = esk1_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28])).

cnf(c_0_30,negated_conjecture,
    ( ~ r1_tarski(esk4_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_31,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_29]),c_0_30]),
    [proof]).
%------------------------------------------------------------------------------
