%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : xboole_1__t31_xboole_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:25 EDT 2019

% Result     : Theorem 172.07s
% Output     : CNFRefutation 172.07s
% Verified   : 
% Statistics : Number of formulae       :   27 (  49 expanded)
%              Number of clauses        :   18 (  24 expanded)
%              Number of leaves         :    4 (  11 expanded)
%              Depth                    :    7
%              Number of atoms          :   96 ( 204 expanded)
%              Number of equality atoms :   18 (  40 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t31_xboole_1,conjecture,(
    ! [X1,X2,X3] : r1_tarski(k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)),k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t31_xboole_1.p',t31_xboole_1)).

fof(d3_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            | r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t31_xboole_1.p',d3_xboole_0)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t31_xboole_1.p',d3_tarski)).

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t31_xboole_1.p',d4_xboole_0)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1,X2,X3] : r1_tarski(k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)),k2_xboole_0(X2,X3)) ),
    inference(assume_negation,[status(cth)],[t31_xboole_1])).

fof(c_0_5,plain,(
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
      & ( ~ r2_hidden(esk5_3(X25,X26,X27),X25)
        | ~ r2_hidden(esk5_3(X25,X26,X27),X27)
        | X27 = k2_xboole_0(X25,X26) )
      & ( ~ r2_hidden(esk5_3(X25,X26,X27),X26)
        | ~ r2_hidden(esk5_3(X25,X26,X27),X27)
        | X27 = k2_xboole_0(X25,X26) )
      & ( r2_hidden(esk5_3(X25,X26,X27),X27)
        | r2_hidden(esk5_3(X25,X26,X27),X25)
        | r2_hidden(esk5_3(X25,X26,X27),X26)
        | X27 = k2_xboole_0(X25,X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).

fof(c_0_6,negated_conjecture,(
    ~ r1_tarski(k2_xboole_0(k3_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,esk3_0)),k2_xboole_0(esk2_0,esk3_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).

fof(c_0_7,plain,(
    ! [X14,X15,X16,X17,X18] :
      ( ( ~ r1_tarski(X14,X15)
        | ~ r2_hidden(X16,X14)
        | r2_hidden(X16,X15) )
      & ( r2_hidden(esk4_2(X17,X18),X17)
        | r1_tarski(X17,X18) )
      & ( ~ r2_hidden(esk4_2(X17,X18),X18)
        | r1_tarski(X17,X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_8,plain,(
    ! [X29,X30,X31,X32,X33,X34,X35,X36] :
      ( ( r2_hidden(X32,X29)
        | ~ r2_hidden(X32,X31)
        | X31 != k3_xboole_0(X29,X30) )
      & ( r2_hidden(X32,X30)
        | ~ r2_hidden(X32,X31)
        | X31 != k3_xboole_0(X29,X30) )
      & ( ~ r2_hidden(X33,X29)
        | ~ r2_hidden(X33,X30)
        | r2_hidden(X33,X31)
        | X31 != k3_xboole_0(X29,X30) )
      & ( ~ r2_hidden(esk6_3(X34,X35,X36),X36)
        | ~ r2_hidden(esk6_3(X34,X35,X36),X34)
        | ~ r2_hidden(esk6_3(X34,X35,X36),X35)
        | X36 = k3_xboole_0(X34,X35) )
      & ( r2_hidden(esk6_3(X34,X35,X36),X34)
        | r2_hidden(esk6_3(X34,X35,X36),X36)
        | X36 = k3_xboole_0(X34,X35) )
      & ( r2_hidden(esk6_3(X34,X35,X36),X35)
        | r2_hidden(esk6_3(X34,X35,X36),X36)
        | X36 = k3_xboole_0(X34,X35) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

cnf(c_0_9,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_xboole_0(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_10,negated_conjecture,
    ( ~ r1_tarski(k2_xboole_0(k3_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,esk3_0)),k2_xboole_0(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( r2_hidden(esk4_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk4_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,plain,
    ( r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X3 != k2_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_14,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,plain,
    ( r2_hidden(X1,X2)
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,k2_xboole_0(X3,X2)) ),
    inference(er,[status(thm)],[c_0_9])).

cnf(c_0_16,negated_conjecture,
    ( r2_hidden(esk4_2(k2_xboole_0(k3_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,esk3_0)),k2_xboole_0(esk2_0,esk3_0)),k2_xboole_0(k3_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_17,negated_conjecture,
    ( ~ r2_hidden(esk4_2(k2_xboole_0(k3_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,esk3_0)),k2_xboole_0(esk2_0,esk3_0)),k2_xboole_0(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_10,c_0_12])).

cnf(c_0_18,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X3 != k2_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_20,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X3,X2)) ),
    inference(er,[status(thm)],[c_0_14])).

cnf(c_0_21,negated_conjecture,
    ( r2_hidden(esk4_2(k2_xboole_0(k3_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,esk3_0)),k2_xboole_0(esk2_0,esk3_0)),k3_xboole_0(esk1_0,esk3_0))
    | r2_hidden(esk4_2(k2_xboole_0(k3_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,esk3_0)),k2_xboole_0(esk2_0,esk3_0)),k3_xboole_0(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( ~ r2_hidden(esk4_2(k2_xboole_0(k3_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,esk3_0)),k2_xboole_0(esk2_0,esk3_0)),esk3_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_23,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_19])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(esk4_2(k2_xboole_0(k3_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,esk3_0)),k2_xboole_0(esk2_0,esk3_0)),k3_xboole_0(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22])).

cnf(c_0_25,negated_conjecture,
    ( ~ r2_hidden(esk4_2(k2_xboole_0(k3_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,esk3_0)),k2_xboole_0(esk2_0,esk3_0)),esk2_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_23])).

cnf(c_0_26,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_24]),c_0_25]),
    [proof]).
%------------------------------------------------------------------------------
