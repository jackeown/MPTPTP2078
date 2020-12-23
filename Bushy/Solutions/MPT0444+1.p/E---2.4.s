%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : relat_1__t27_relat_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:00 EDT 2019

% Result     : Theorem 264.45s
% Output     : CNFRefutation 264.45s
% Verified   : 
% Statistics : Number of formulae       :   32 (  64 expanded)
%              Number of clauses        :   21 (  33 expanded)
%              Number of leaves         :    5 (  14 expanded)
%              Depth                    :    9
%              Number of atoms          :  103 ( 260 expanded)
%              Number of equality atoms :   21 (  55 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t27_relat_1.p',d4_xboole_0)).

fof(d5_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k2_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X4,X3),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t27_relat_1.p',d5_relat_1)).

fof(t27_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => r1_tarski(k2_relat_1(k3_xboole_0(X1,X2)),k3_xboole_0(k2_relat_1(X1),k2_relat_1(X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t27_relat_1.p',t27_relat_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t27_relat_1.p',d3_tarski)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t27_relat_1.p',commutativity_k3_xboole_0)).

fof(c_0_5,plain,(
    ! [X17,X18,X19,X20,X21,X22,X23,X24] :
      ( ( r2_hidden(X20,X17)
        | ~ r2_hidden(X20,X19)
        | X19 != k3_xboole_0(X17,X18) )
      & ( r2_hidden(X20,X18)
        | ~ r2_hidden(X20,X19)
        | X19 != k3_xboole_0(X17,X18) )
      & ( ~ r2_hidden(X21,X17)
        | ~ r2_hidden(X21,X18)
        | r2_hidden(X21,X19)
        | X19 != k3_xboole_0(X17,X18) )
      & ( ~ r2_hidden(esk4_3(X22,X23,X24),X24)
        | ~ r2_hidden(esk4_3(X22,X23,X24),X22)
        | ~ r2_hidden(esk4_3(X22,X23,X24),X23)
        | X24 = k3_xboole_0(X22,X23) )
      & ( r2_hidden(esk4_3(X22,X23,X24),X22)
        | r2_hidden(esk4_3(X22,X23,X24),X24)
        | X24 = k3_xboole_0(X22,X23) )
      & ( r2_hidden(esk4_3(X22,X23,X24),X23)
        | r2_hidden(esk4_3(X22,X23,X24),X24)
        | X24 = k3_xboole_0(X22,X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

fof(c_0_6,plain,(
    ! [X26,X27,X28,X30,X31,X32,X33,X35] :
      ( ( ~ r2_hidden(X28,X27)
        | r2_hidden(k4_tarski(esk5_3(X26,X27,X28),X28),X26)
        | X27 != k2_relat_1(X26) )
      & ( ~ r2_hidden(k4_tarski(X31,X30),X26)
        | r2_hidden(X30,X27)
        | X27 != k2_relat_1(X26) )
      & ( ~ r2_hidden(esk6_2(X32,X33),X33)
        | ~ r2_hidden(k4_tarski(X35,esk6_2(X32,X33)),X32)
        | X33 = k2_relat_1(X32) )
      & ( r2_hidden(esk6_2(X32,X33),X33)
        | r2_hidden(k4_tarski(esk7_2(X32,X33),esk6_2(X32,X33)),X32)
        | X33 = k2_relat_1(X32) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).

cnf(c_0_7,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_8,plain,
    ( r2_hidden(X2,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_9,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X3,X2)) ),
    inference(er,[status(thm)],[c_0_7])).

cnf(c_0_10,plain,
    ( r2_hidden(k4_tarski(esk5_3(X3,X2,X1),X1),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => r1_tarski(k2_relat_1(k3_xboole_0(X1,X2)),k3_xboole_0(k2_relat_1(X1),k2_relat_1(X2))) ) ) ),
    inference(assume_negation,[status(cth)],[t27_relat_1])).

cnf(c_0_12,plain,
    ( r2_hidden(X1,k2_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X3,X1),X2) ),
    inference(er,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( r2_hidden(k4_tarski(esk5_3(k3_xboole_0(X1,X2),X3,X4),X4),X2)
    | X3 != k2_relat_1(k3_xboole_0(X1,X2))
    | ~ r2_hidden(X4,X3) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

fof(c_0_14,negated_conjecture,
    ( v1_relat_1(esk1_0)
    & v1_relat_1(esk2_0)
    & ~ r1_tarski(k2_relat_1(k3_xboole_0(esk1_0,esk2_0)),k3_xboole_0(k2_relat_1(esk1_0),k2_relat_1(esk2_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).

fof(c_0_15,plain,(
    ! [X11,X12,X13,X14,X15] :
      ( ( ~ r1_tarski(X11,X12)
        | ~ r2_hidden(X13,X11)
        | r2_hidden(X13,X12) )
      & ( r2_hidden(esk3_2(X14,X15),X14)
        | r1_tarski(X14,X15) )
      & ( ~ r2_hidden(esk3_2(X14,X15),X15)
        | r1_tarski(X14,X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_16,plain,
    ( r2_hidden(X1,k2_relat_1(X2))
    | X3 != k2_relat_1(k3_xboole_0(X4,X2))
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

fof(c_0_17,plain,(
    ! [X9,X10] : k3_xboole_0(X9,X10) = k3_xboole_0(X10,X9) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_18,negated_conjecture,
    ( ~ r1_tarski(k2_relat_1(k3_xboole_0(esk1_0,esk2_0)),k3_xboole_0(k2_relat_1(esk1_0),k2_relat_1(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk3_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X4 != k3_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_21,plain,
    ( r2_hidden(esk3_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( r2_hidden(X1,k2_relat_1(X2))
    | ~ r2_hidden(X1,k2_relat_1(k3_xboole_0(X3,X2))) ),
    inference(er,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,negated_conjecture,
    ( ~ r2_hidden(esk3_2(k2_relat_1(k3_xboole_0(esk1_0,esk2_0)),k3_xboole_0(k2_relat_1(esk1_0),k2_relat_1(esk2_0))),k3_xboole_0(k2_relat_1(esk1_0),k2_relat_1(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_25,plain,
    ( r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_20])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(esk3_2(k2_relat_1(k3_xboole_0(esk1_0,esk2_0)),k3_xboole_0(k2_relat_1(esk1_0),k2_relat_1(esk2_0))),k2_relat_1(k3_xboole_0(esk1_0,esk2_0))) ),
    inference(spm,[status(thm)],[c_0_18,c_0_21])).

cnf(c_0_27,plain,
    ( r2_hidden(X1,k2_relat_1(X2))
    | ~ r2_hidden(X1,k2_relat_1(k3_xboole_0(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_28,negated_conjecture,
    ( ~ r2_hidden(esk3_2(k2_relat_1(k3_xboole_0(esk1_0,esk2_0)),k3_xboole_0(k2_relat_1(esk1_0),k2_relat_1(esk2_0))),k2_relat_1(esk2_0))
    | ~ r2_hidden(esk3_2(k2_relat_1(k3_xboole_0(esk1_0,esk2_0)),k3_xboole_0(k2_relat_1(esk1_0),k2_relat_1(esk2_0))),k2_relat_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(esk3_2(k2_relat_1(k3_xboole_0(esk1_0,esk2_0)),k3_xboole_0(k2_relat_1(esk1_0),k2_relat_1(esk2_0))),k2_relat_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_26])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(esk3_2(k2_relat_1(k3_xboole_0(esk1_0,esk2_0)),k3_xboole_0(k2_relat_1(esk1_0),k2_relat_1(esk2_0))),k2_relat_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_26])).

cnf(c_0_31,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_29])]),c_0_30])]),
    [proof]).
%------------------------------------------------------------------------------
