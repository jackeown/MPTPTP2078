%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : xboole_1__t51_xboole_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:28 EDT 2019

% Result     : Theorem 155.46s
% Output     : CNFRefutation 155.46s
% Verified   : 
% Statistics : Number of formulae       :   33 (  79 expanded)
%              Number of clauses        :   22 (  36 expanded)
%              Number of leaves         :    5 (  19 expanded)
%              Depth                    :    7
%              Number of atoms          :  139 ( 388 expanded)
%              Number of equality atoms :   38 ( 123 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t51_xboole_1,conjecture,(
    ! [X1,X2] : k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t51_xboole_1.p',t51_xboole_1)).

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t51_xboole_1.p',d4_xboole_0)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t51_xboole_1.p',d5_xboole_0)).

fof(d3_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            | r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t51_xboole_1.p',d3_xboole_0)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t51_xboole_1.p',d10_xboole_0)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1,X2] : k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    inference(assume_negation,[status(cth)],[t51_xboole_1])).

fof(c_0_6,plain,(
    ! [X30,X31,X32,X33,X34,X35,X36,X37] :
      ( ( r2_hidden(X33,X30)
        | ~ r2_hidden(X33,X32)
        | X32 != k3_xboole_0(X30,X31) )
      & ( r2_hidden(X33,X31)
        | ~ r2_hidden(X33,X32)
        | X32 != k3_xboole_0(X30,X31) )
      & ( ~ r2_hidden(X34,X30)
        | ~ r2_hidden(X34,X31)
        | r2_hidden(X34,X32)
        | X32 != k3_xboole_0(X30,X31) )
      & ( ~ r2_hidden(esk5_3(X35,X36,X37),X37)
        | ~ r2_hidden(esk5_3(X35,X36,X37),X35)
        | ~ r2_hidden(esk5_3(X35,X36,X37),X36)
        | X37 = k3_xboole_0(X35,X36) )
      & ( r2_hidden(esk5_3(X35,X36,X37),X35)
        | r2_hidden(esk5_3(X35,X36,X37),X37)
        | X37 = k3_xboole_0(X35,X36) )
      & ( r2_hidden(esk5_3(X35,X36,X37),X36)
        | r2_hidden(esk5_3(X35,X36,X37),X37)
        | X37 = k3_xboole_0(X35,X36) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

fof(c_0_7,plain,(
    ! [X39,X40,X41,X42,X43,X44,X45,X46] :
      ( ( r2_hidden(X42,X39)
        | ~ r2_hidden(X42,X41)
        | X41 != k4_xboole_0(X39,X40) )
      & ( ~ r2_hidden(X42,X40)
        | ~ r2_hidden(X42,X41)
        | X41 != k4_xboole_0(X39,X40) )
      & ( ~ r2_hidden(X43,X39)
        | r2_hidden(X43,X40)
        | r2_hidden(X43,X41)
        | X41 != k4_xboole_0(X39,X40) )
      & ( ~ r2_hidden(esk6_3(X44,X45,X46),X46)
        | ~ r2_hidden(esk6_3(X44,X45,X46),X44)
        | r2_hidden(esk6_3(X44,X45,X46),X45)
        | X46 = k4_xboole_0(X44,X45) )
      & ( r2_hidden(esk6_3(X44,X45,X46),X44)
        | r2_hidden(esk6_3(X44,X45,X46),X46)
        | X46 = k4_xboole_0(X44,X45) )
      & ( ~ r2_hidden(esk6_3(X44,X45,X46),X45)
        | r2_hidden(esk6_3(X44,X45,X46),X46)
        | X46 = k4_xboole_0(X44,X45) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

fof(c_0_8,negated_conjecture,(
    k2_xboole_0(k3_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk1_0,esk2_0)) != esk1_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

fof(c_0_9,plain,(
    ! [X21,X22,X23,X24,X25,X26,X27,X28] :
      ( ( ~ r2_hidden(X24,X23)
        | r2_hidden(X24,X21)
        | r2_hidden(X24,X22)
        | X23 != k2_xboole_0(X21,X22) )
      & ( ~ r2_hidden(X25,X21)
        | r2_hidden(X25,X23)
        | X23 != k2_xboole_0(X21,X22) )
      & ( ~ r2_hidden(X25,X22)
        | r2_hidden(X25,X23)
        | X23 != k2_xboole_0(X21,X22) )
      & ( ~ r2_hidden(esk4_3(X26,X27,X28),X26)
        | ~ r2_hidden(esk4_3(X26,X27,X28),X28)
        | X28 = k2_xboole_0(X26,X27) )
      & ( ~ r2_hidden(esk4_3(X26,X27,X28),X27)
        | ~ r2_hidden(esk4_3(X26,X27,X28),X28)
        | X28 = k2_xboole_0(X26,X27) )
      & ( r2_hidden(esk4_3(X26,X27,X28),X28)
        | r2_hidden(esk4_3(X26,X27,X28),X26)
        | r2_hidden(esk4_3(X26,X27,X28),X27)
        | X28 = k2_xboole_0(X26,X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).

cnf(c_0_10,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_11,plain,(
    ! [X13,X14] :
      ( ( r1_tarski(X13,X14)
        | X13 != X14 )
      & ( r1_tarski(X14,X13)
        | X13 != X14 )
      & ( ~ r1_tarski(X13,X14)
        | ~ r1_tarski(X14,X13)
        | X13 = X14 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_12,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,negated_conjecture,
    ( k2_xboole_0(k3_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk1_0,esk2_0)) != esk1_0 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,plain,
    ( X3 = k2_xboole_0(X1,X2)
    | ~ r2_hidden(esk4_3(X1,X2,X3),X1)
    | ~ r2_hidden(esk4_3(X1,X2,X3),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X4 != k3_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_17,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( X3 = k2_xboole_0(X1,X2)
    | ~ r2_hidden(esk4_3(X1,X2,X3),X2)
    | ~ r2_hidden(esk4_3(X1,X2,X3),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_19,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k4_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_12])).

cnf(c_0_20,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | X4 != k4_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_21,negated_conjecture,
    ( ~ r2_hidden(esk4_3(k3_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk1_0,esk2_0),esk1_0),k3_xboole_0(esk1_0,esk2_0)) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14])]),c_0_15])).

cnf(c_0_22,plain,
    ( r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_16])).

cnf(c_0_23,negated_conjecture,
    ( ~ r1_tarski(k2_xboole_0(k3_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk1_0,esk2_0)),esk1_0)
    | ~ r1_tarski(esk1_0,k2_xboole_0(k3_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk1_0,esk2_0))) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_17])])).

cnf(c_0_24,plain,
    ( r2_hidden(esk4_3(X1,X2,X3),X3)
    | r2_hidden(esk4_3(X1,X2,X3),X1)
    | r2_hidden(esk4_3(X1,X2,X3),X2)
    | X3 = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_25,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_26,negated_conjecture,
    ( ~ r2_hidden(esk4_3(k3_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk1_0,esk2_0),esk1_0),k4_xboole_0(esk1_0,esk2_0)) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_18])]),c_0_19])).

cnf(c_0_27,plain,
    ( r2_hidden(X1,k4_xboole_0(X2,X3))
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_20])).

cnf(c_0_28,negated_conjecture,
    ( ~ r2_hidden(esk4_3(k3_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk1_0,esk2_0),esk1_0),esk2_0)
    | ~ r2_hidden(esk4_3(k3_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk1_0,esk2_0),esk1_0),esk1_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(esk4_3(k3_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk1_0,esk2_0),X1),k3_xboole_0(esk1_0,esk2_0))
    | r2_hidden(esk4_3(k3_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk1_0,esk2_0),X1),k4_xboole_0(esk1_0,esk2_0))
    | r2_hidden(esk4_3(k3_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk1_0,esk2_0),X1),X1)
    | ~ r1_tarski(X1,esk1_0)
    | ~ r1_tarski(esk1_0,X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_30,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_25])).

cnf(c_0_31,negated_conjecture,
    ( ~ r2_hidden(esk4_3(k3_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk1_0,esk2_0),esk1_0),esk1_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28])).

cnf(c_0_32,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_30])]),c_0_21]),c_0_26]),c_0_31]),
    [proof]).
%------------------------------------------------------------------------------
