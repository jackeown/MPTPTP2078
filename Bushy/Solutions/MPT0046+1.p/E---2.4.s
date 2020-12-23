%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : xboole_1__t39_xboole_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:26 EDT 2019

% Result     : Theorem 8.25s
% Output     : CNFRefutation 8.25s
% Verified   : 
% Statistics : Number of formulae       :   28 ( 119 expanded)
%              Number of clauses        :   21 (  56 expanded)
%              Number of leaves         :    3 (  28 expanded)
%              Depth                    :    9
%              Number of atoms          :  100 ( 650 expanded)
%              Number of equality atoms :   26 ( 196 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t39_xboole_1,conjecture,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t39_xboole_1.p',t39_xboole_1)).

fof(d3_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            | r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t39_xboole_1.p',d3_xboole_0)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t39_xboole_1.p',d5_xboole_0)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(assume_negation,[status(cth)],[t39_xboole_1])).

fof(c_0_4,plain,(
    ! [X19,X20,X21,X22,X23,X24,X25,X26] :
      ( ( ~ r2_hidden(X22,X21)
        | r2_hidden(X22,X19)
        | r2_hidden(X22,X20)
        | X21 != k2_xboole_0(X19,X20) )
      & ( ~ r2_hidden(X23,X19)
        | r2_hidden(X23,X21)
        | X21 != k2_xboole_0(X19,X20) )
      & ( ~ r2_hidden(X23,X20)
        | r2_hidden(X23,X21)
        | X21 != k2_xboole_0(X19,X20) )
      & ( ~ r2_hidden(esk4_3(X24,X25,X26),X24)
        | ~ r2_hidden(esk4_3(X24,X25,X26),X26)
        | X26 = k2_xboole_0(X24,X25) )
      & ( ~ r2_hidden(esk4_3(X24,X25,X26),X25)
        | ~ r2_hidden(esk4_3(X24,X25,X26),X26)
        | X26 = k2_xboole_0(X24,X25) )
      & ( r2_hidden(esk4_3(X24,X25,X26),X26)
        | r2_hidden(esk4_3(X24,X25,X26),X24)
        | r2_hidden(esk4_3(X24,X25,X26),X25)
        | X26 = k2_xboole_0(X24,X25) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).

fof(c_0_5,plain,(
    ! [X28,X29,X30,X31,X32,X33,X34,X35] :
      ( ( r2_hidden(X31,X28)
        | ~ r2_hidden(X31,X30)
        | X30 != k4_xboole_0(X28,X29) )
      & ( ~ r2_hidden(X31,X29)
        | ~ r2_hidden(X31,X30)
        | X30 != k4_xboole_0(X28,X29) )
      & ( ~ r2_hidden(X32,X28)
        | r2_hidden(X32,X29)
        | r2_hidden(X32,X30)
        | X30 != k4_xboole_0(X28,X29) )
      & ( ~ r2_hidden(esk5_3(X33,X34,X35),X35)
        | ~ r2_hidden(esk5_3(X33,X34,X35),X33)
        | r2_hidden(esk5_3(X33,X34,X35),X34)
        | X35 = k4_xboole_0(X33,X34) )
      & ( r2_hidden(esk5_3(X33,X34,X35),X33)
        | r2_hidden(esk5_3(X33,X34,X35),X35)
        | X35 = k4_xboole_0(X33,X34) )
      & ( ~ r2_hidden(esk5_3(X33,X34,X35),X34)
        | r2_hidden(esk5_3(X33,X34,X35),X35)
        | X35 = k4_xboole_0(X33,X34) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

fof(c_0_6,negated_conjecture,(
    k2_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk1_0)) != k2_xboole_0(esk1_0,esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])).

cnf(c_0_7,plain,
    ( r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X3 != k2_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,negated_conjecture,
    ( k2_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk1_0)) != k2_xboole_0(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( r2_hidden(esk4_3(X1,X2,X3),X3)
    | r2_hidden(esk4_3(X1,X2,X3),X1)
    | r2_hidden(esk4_3(X1,X2,X3),X2)
    | X3 = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_11,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X3 != k2_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_13,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k4_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_8])).

cnf(c_0_14,negated_conjecture,
    ( r2_hidden(esk4_3(esk1_0,k4_xboole_0(esk2_0,esk1_0),k2_xboole_0(esk1_0,esk2_0)),k4_xboole_0(esk2_0,esk1_0))
    | r2_hidden(esk4_3(esk1_0,k4_xboole_0(esk2_0,esk1_0),k2_xboole_0(esk1_0,esk2_0)),k2_xboole_0(esk1_0,esk2_0)) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_10])]),c_0_11])).

cnf(c_0_15,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_12])).

cnf(c_0_16,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_xboole_0(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_17,plain,
    ( X3 = k2_xboole_0(X1,X2)
    | ~ r2_hidden(esk4_3(X1,X2,X3),X1)
    | ~ r2_hidden(esk4_3(X1,X2,X3),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_18,negated_conjecture,
    ( r2_hidden(esk4_3(esk1_0,k4_xboole_0(esk2_0,esk1_0),k2_xboole_0(esk1_0,esk2_0)),k2_xboole_0(esk1_0,esk2_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15])).

cnf(c_0_19,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | X4 != k4_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_20,plain,
    ( r2_hidden(X1,X2)
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,k2_xboole_0(X3,X2)) ),
    inference(er,[status(thm)],[c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( ~ r2_hidden(esk4_3(esk1_0,k4_xboole_0(esk2_0,esk1_0),k2_xboole_0(esk1_0,esk2_0)),esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_9])).

cnf(c_0_22,plain,
    ( X3 = k2_xboole_0(X1,X2)
    | ~ r2_hidden(esk4_3(X1,X2,X3),X2)
    | ~ r2_hidden(esk4_3(X1,X2,X3),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_23,plain,
    ( r2_hidden(X1,k4_xboole_0(X2,X3))
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_19])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(esk4_3(esk1_0,k4_xboole_0(esk2_0,esk1_0),k2_xboole_0(esk1_0,esk2_0)),esk2_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_18]),c_0_21])).

cnf(c_0_25,negated_conjecture,
    ( ~ r2_hidden(esk4_3(esk1_0,k4_xboole_0(esk2_0,esk1_0),k2_xboole_0(esk1_0,esk2_0)),k4_xboole_0(esk2_0,esk1_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_18]),c_0_9])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(esk4_3(esk1_0,k4_xboole_0(esk2_0,esk1_0),k2_xboole_0(esk1_0,esk2_0)),k4_xboole_0(esk2_0,X1))
    | r2_hidden(esk4_3(esk1_0,k4_xboole_0(esk2_0,esk1_0),k2_xboole_0(esk1_0,esk2_0)),X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_27,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_21]),
    [proof]).
%------------------------------------------------------------------------------
