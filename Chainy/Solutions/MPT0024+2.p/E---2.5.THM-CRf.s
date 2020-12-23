%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0024+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:32 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   15 (  21 expanded)
%              Number of clauses        :    8 (   9 expanded)
%              Number of leaves         :    3 (   5 expanded)
%              Depth                    :    6
%              Number of atoms          :   50 (  64 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t17_xboole_1,conjecture,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',d4_xboole_0)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',d3_tarski)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(assume_negation,[status(cth)],[t17_xboole_1])).

fof(c_0_4,plain,(
    ! [X34,X35,X36,X37,X38,X39,X40,X41] :
      ( ( r2_hidden(X37,X34)
        | ~ r2_hidden(X37,X36)
        | X36 != k3_xboole_0(X34,X35) )
      & ( r2_hidden(X37,X35)
        | ~ r2_hidden(X37,X36)
        | X36 != k3_xboole_0(X34,X35) )
      & ( ~ r2_hidden(X38,X34)
        | ~ r2_hidden(X38,X35)
        | r2_hidden(X38,X36)
        | X36 != k3_xboole_0(X34,X35) )
      & ( ~ r2_hidden(esk4_3(X39,X40,X41),X41)
        | ~ r2_hidden(esk4_3(X39,X40,X41),X39)
        | ~ r2_hidden(esk4_3(X39,X40,X41),X40)
        | X41 = k3_xboole_0(X39,X40) )
      & ( r2_hidden(esk4_3(X39,X40,X41),X39)
        | r2_hidden(esk4_3(X39,X40,X41),X41)
        | X41 = k3_xboole_0(X39,X40) )
      & ( r2_hidden(esk4_3(X39,X40,X41),X40)
        | r2_hidden(esk4_3(X39,X40,X41),X41)
        | X41 = k3_xboole_0(X39,X40) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

fof(c_0_5,negated_conjecture,(
    ~ r1_tarski(k3_xboole_0(esk15_0,esk16_0),esk15_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])).

fof(c_0_6,plain,(
    ! [X19,X20,X21,X22,X23] :
      ( ( ~ r1_tarski(X19,X20)
        | ~ r2_hidden(X21,X19)
        | r2_hidden(X21,X20) )
      & ( r2_hidden(esk2_2(X22,X23),X22)
        | r1_tarski(X22,X23) )
      & ( ~ r2_hidden(esk2_2(X22,X23),X23)
        | r1_tarski(X22,X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_7,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,negated_conjecture,
    ( ~ r1_tarski(k3_xboole_0(esk15_0,esk16_0),esk15_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_7])).

cnf(c_0_11,negated_conjecture,
    ( r2_hidden(esk2_2(k3_xboole_0(esk15_0,esk16_0),esk15_0),k3_xboole_0(esk15_0,esk16_0)) ),
    inference(spm,[status(thm)],[c_0_8,c_0_9])).

cnf(c_0_12,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk2_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_13,negated_conjecture,
    ( r2_hidden(esk2_2(k3_xboole_0(esk15_0,esk16_0),esk15_0),esk15_0) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_14,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_8]),
    [proof]).
%------------------------------------------------------------------------------
