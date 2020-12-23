%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : xboole_1__t28_xboole_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:24 EDT 2019

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   16 (  41 expanded)
%              Number of clauses        :    9 (  16 expanded)
%              Number of leaves         :    3 (  10 expanded)
%              Depth                    :    7
%              Number of atoms          :   57 ( 164 expanded)
%              Number of equality atoms :   13 (  51 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t28_xboole_1,conjecture,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t28_xboole_1.p',t28_xboole_1)).

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t28_xboole_1.p',d4_xboole_0)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t28_xboole_1.p',d3_tarski)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1,X2] :
        ( r1_tarski(X1,X2)
       => k3_xboole_0(X1,X2) = X1 ) ),
    inference(assume_negation,[status(cth)],[t28_xboole_1])).

fof(c_0_4,negated_conjecture,
    ( r1_tarski(esk1_0,esk2_0)
    & k3_xboole_0(esk1_0,esk2_0) != esk1_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])).

fof(c_0_5,plain,(
    ! [X19,X20,X21,X22,X23,X24,X25,X26] :
      ( ( r2_hidden(X22,X19)
        | ~ r2_hidden(X22,X21)
        | X21 != k3_xboole_0(X19,X20) )
      & ( r2_hidden(X22,X20)
        | ~ r2_hidden(X22,X21)
        | X21 != k3_xboole_0(X19,X20) )
      & ( ~ r2_hidden(X23,X19)
        | ~ r2_hidden(X23,X20)
        | r2_hidden(X23,X21)
        | X21 != k3_xboole_0(X19,X20) )
      & ( ~ r2_hidden(esk4_3(X24,X25,X26),X26)
        | ~ r2_hidden(esk4_3(X24,X25,X26),X24)
        | ~ r2_hidden(esk4_3(X24,X25,X26),X25)
        | X26 = k3_xboole_0(X24,X25) )
      & ( r2_hidden(esk4_3(X24,X25,X26),X24)
        | r2_hidden(esk4_3(X24,X25,X26),X26)
        | X26 = k3_xboole_0(X24,X25) )
      & ( r2_hidden(esk4_3(X24,X25,X26),X25)
        | r2_hidden(esk4_3(X24,X25,X26),X26)
        | X26 = k3_xboole_0(X24,X25) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

fof(c_0_6,plain,(
    ! [X13,X14,X15,X16,X17] :
      ( ( ~ r1_tarski(X13,X14)
        | ~ r2_hidden(X15,X13)
        | r2_hidden(X15,X14) )
      & ( r2_hidden(esk3_2(X16,X17),X16)
        | r1_tarski(X16,X17) )
      & ( ~ r2_hidden(esk3_2(X16,X17),X17)
        | r1_tarski(X16,X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_7,negated_conjecture,
    ( k3_xboole_0(esk1_0,esk2_0) != esk1_0 ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,plain,
    ( r2_hidden(esk4_3(X1,X2,X3),X1)
    | r2_hidden(esk4_3(X1,X2,X3),X3)
    | X3 = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,negated_conjecture,
    ( r2_hidden(esk4_3(esk1_0,esk2_0,esk1_0),esk1_0) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_7,c_0_8])])).

cnf(c_0_11,negated_conjecture,
    ( r2_hidden(esk4_3(esk1_0,esk2_0,esk1_0),X1)
    | ~ r1_tarski(esk1_0,X1) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_12,negated_conjecture,
    ( r1_tarski(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_13,plain,
    ( X3 = k3_xboole_0(X1,X2)
    | ~ r2_hidden(esk4_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk4_3(X1,X2,X3),X1)
    | ~ r2_hidden(esk4_3(X1,X2,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_14,negated_conjecture,
    ( r2_hidden(esk4_3(esk1_0,esk2_0,esk1_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_15,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_10]),c_0_14]),c_0_10])]),c_0_7]),
    [proof]).
%------------------------------------------------------------------------------
