%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : xboole_1__t21_xboole_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:23 EDT 2019

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   16 (  36 expanded)
%              Number of clauses        :    9 (  14 expanded)
%              Number of leaves         :    3 (   9 expanded)
%              Depth                    :    5
%              Number of atoms          :   70 ( 158 expanded)
%              Number of equality atoms :   22 (  56 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t21_xboole_1,conjecture,(
    ! [X1,X2] : k3_xboole_0(X1,k2_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t21_xboole_1.p',t21_xboole_1)).

fof(d3_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            | r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t21_xboole_1.p',d3_xboole_0)).

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t21_xboole_1.p',d4_xboole_0)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1,X2] : k3_xboole_0(X1,k2_xboole_0(X1,X2)) = X1 ),
    inference(assume_negation,[status(cth)],[t21_xboole_1])).

fof(c_0_4,plain,(
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

fof(c_0_5,negated_conjecture,(
    k3_xboole_0(esk1_0,k2_xboole_0(esk1_0,esk2_0)) != esk1_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])).

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

cnf(c_0_7,plain,
    ( r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X3 != k2_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,negated_conjecture,
    ( k3_xboole_0(esk1_0,k2_xboole_0(esk1_0,esk2_0)) != esk1_0 ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( r2_hidden(esk5_3(X1,X2,X3),X1)
    | r2_hidden(esk5_3(X1,X2,X3),X3)
    | X3 = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( r2_hidden(esk5_3(X1,X2,X3),X2)
    | r2_hidden(esk5_3(X1,X2,X3),X3)
    | X3 = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( X3 = k3_xboole_0(X1,X2)
    | ~ r2_hidden(esk5_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk5_3(X1,X2,X3),X1)
    | ~ r2_hidden(esk5_3(X1,X2,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_13,negated_conjecture,
    ( r2_hidden(esk5_3(esk1_0,k2_xboole_0(esk1_0,esk2_0),esk1_0),esk1_0) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_8,c_0_9])])).

cnf(c_0_14,negated_conjecture,
    ( r2_hidden(esk5_3(esk1_0,k2_xboole_0(esk1_0,esk2_0),esk1_0),k2_xboole_0(esk1_0,esk2_0)) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_8,c_0_10])]),c_0_11])).

cnf(c_0_15,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_14]),c_0_13])]),c_0_8]),
    [proof]).
%------------------------------------------------------------------------------
