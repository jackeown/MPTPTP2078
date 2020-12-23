%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : xboole_1__t38_xboole_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n030.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:26 EDT 2019

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   23 (  28 expanded)
%              Number of clauses        :   12 (  12 expanded)
%              Number of leaves         :    5 (   7 expanded)
%              Depth                    :    6
%              Number of atoms          :   73 (  89 expanded)
%              Number of equality atoms :   18 (  21 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t38_xboole_1,conjecture,(
    ! [X1,X2] :
      ( r1_tarski(X1,k4_xboole_0(X2,X1))
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t38_xboole_1.p',t38_xboole_1)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t38_xboole_1.p',d5_xboole_0)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t38_xboole_1.p',d3_tarski)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t38_xboole_1.p',d10_xboole_0)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t38_xboole_1.p',t2_xboole_1)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1,X2] :
        ( r1_tarski(X1,k4_xboole_0(X2,X1))
       => X1 = k1_xboole_0 ) ),
    inference(assume_negation,[status(cth)],[t38_xboole_1])).

fof(c_0_6,plain,(
    ! [X17,X18,X19,X20,X21,X22,X23,X24] :
      ( ( r2_hidden(X20,X17)
        | ~ r2_hidden(X20,X19)
        | X19 != k4_xboole_0(X17,X18) )
      & ( ~ r2_hidden(X20,X18)
        | ~ r2_hidden(X20,X19)
        | X19 != k4_xboole_0(X17,X18) )
      & ( ~ r2_hidden(X21,X17)
        | r2_hidden(X21,X18)
        | r2_hidden(X21,X19)
        | X19 != k4_xboole_0(X17,X18) )
      & ( ~ r2_hidden(esk4_3(X22,X23,X24),X24)
        | ~ r2_hidden(esk4_3(X22,X23,X24),X22)
        | r2_hidden(esk4_3(X22,X23,X24),X23)
        | X24 = k4_xboole_0(X22,X23) )
      & ( r2_hidden(esk4_3(X22,X23,X24),X22)
        | r2_hidden(esk4_3(X22,X23,X24),X24)
        | X24 = k4_xboole_0(X22,X23) )
      & ( ~ r2_hidden(esk4_3(X22,X23,X24),X23)
        | r2_hidden(esk4_3(X22,X23,X24),X24)
        | X24 = k4_xboole_0(X22,X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

fof(c_0_7,plain,(
    ! [X11,X12,X13,X14,X15] :
      ( ( ~ r1_tarski(X11,X12)
        | ~ r2_hidden(X13,X11)
        | r2_hidden(X13,X12) )
      & ( r2_hidden(esk3_2(X14,X15),X14)
        | r1_tarski(X14,X15) )
      & ( ~ r2_hidden(esk3_2(X14,X15),X15)
        | r1_tarski(X14,X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_8,negated_conjecture,
    ( r1_tarski(esk1_0,k4_xboole_0(esk2_0,esk1_0))
    & esk1_0 != k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

cnf(c_0_9,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_10,plain,(
    ! [X9,X10] :
      ( ( r1_tarski(X9,X10)
        | X9 != X10 )
      & ( r1_tarski(X10,X9)
        | X9 != X10 )
      & ( ~ r1_tarski(X9,X10)
        | ~ r1_tarski(X10,X9)
        | X9 = X10 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_11,plain,(
    ! [X26] : r1_tarski(k1_xboole_0,X26) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_12,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,negated_conjecture,
    ( r1_tarski(esk1_0,k4_xboole_0(esk2_0,esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,negated_conjecture,
    ( ~ r2_hidden(X1,esk1_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_14])).

cnf(c_0_18,plain,
    ( r2_hidden(esk3_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_19,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( r1_tarski(esk1_0,X1) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_21,negated_conjecture,
    ( esk1_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_22,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21]),
    [proof]).
%------------------------------------------------------------------------------
