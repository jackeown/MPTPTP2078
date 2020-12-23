%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0930+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:26 EST 2020

% Result     : Theorem 0.15s
% Output     : CNFRefutation 0.15s
% Verified   : 
% Statistics : Number of formulae       :   22 (  48 expanded)
%              Number of clauses        :   13 (  19 expanded)
%              Number of leaves         :    4 (  11 expanded)
%              Depth                    :    7
%              Number of atoms          :   72 ( 158 expanded)
%              Number of equality atoms :   16 (  20 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t91_mcart_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => ( r2_hidden(k1_mcart_1(X2),k1_relat_1(X1))
            & r2_hidden(k2_mcart_1(X2),k2_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_mcart_1)).

fof(d5_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k2_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X4,X3),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

fof(t23_mcart_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X1,X2)
       => X1 = k4_tarski(k1_mcart_1(X1),k2_mcart_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_mcart_1)).

fof(d4_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X3,X4),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( r2_hidden(X2,X1)
           => ( r2_hidden(k1_mcart_1(X2),k1_relat_1(X1))
              & r2_hidden(k2_mcart_1(X2),k2_relat_1(X1)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t91_mcart_1])).

fof(c_0_5,plain,(
    ! [X16,X17,X18,X20,X21,X22,X23,X25] :
      ( ( ~ r2_hidden(X18,X17)
        | r2_hidden(k4_tarski(esk4_3(X16,X17,X18),X18),X16)
        | X17 != k2_relat_1(X16) )
      & ( ~ r2_hidden(k4_tarski(X21,X20),X16)
        | r2_hidden(X20,X17)
        | X17 != k2_relat_1(X16) )
      & ( ~ r2_hidden(esk5_2(X22,X23),X23)
        | ~ r2_hidden(k4_tarski(X25,esk5_2(X22,X23)),X22)
        | X23 = k2_relat_1(X22) )
      & ( r2_hidden(esk5_2(X22,X23),X23)
        | r2_hidden(k4_tarski(esk6_2(X22,X23),esk5_2(X22,X23)),X22)
        | X23 = k2_relat_1(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).

fof(c_0_6,plain,(
    ! [X27,X28] :
      ( ~ v1_relat_1(X28)
      | ~ r2_hidden(X27,X28)
      | X27 = k4_tarski(k1_mcart_1(X27),k2_mcart_1(X27)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_mcart_1])])).

fof(c_0_7,negated_conjecture,
    ( v1_relat_1(esk7_0)
    & r2_hidden(esk8_0,esk7_0)
    & ( ~ r2_hidden(k1_mcart_1(esk8_0),k1_relat_1(esk7_0))
      | ~ r2_hidden(k2_mcart_1(esk8_0),k2_relat_1(esk7_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).

cnf(c_0_8,plain,
    ( r2_hidden(X2,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( X2 = k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2))
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,negated_conjecture,
    ( r2_hidden(esk8_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,negated_conjecture,
    ( v1_relat_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_12,plain,(
    ! [X5,X6,X7,X9,X10,X11,X12,X14] :
      ( ( ~ r2_hidden(X7,X6)
        | r2_hidden(k4_tarski(X7,esk1_3(X5,X6,X7)),X5)
        | X6 != k1_relat_1(X5) )
      & ( ~ r2_hidden(k4_tarski(X9,X10),X5)
        | r2_hidden(X9,X6)
        | X6 != k1_relat_1(X5) )
      & ( ~ r2_hidden(esk2_2(X11,X12),X12)
        | ~ r2_hidden(k4_tarski(esk2_2(X11,X12),X14),X11)
        | X12 = k1_relat_1(X11) )
      & ( r2_hidden(esk2_2(X11,X12),X12)
        | r2_hidden(k4_tarski(esk2_2(X11,X12),esk3_2(X11,X12)),X11)
        | X12 = k1_relat_1(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).

cnf(c_0_13,plain,
    ( r2_hidden(X1,k2_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X3,X1),X2) ),
    inference(er,[status(thm)],[c_0_8])).

cnf(c_0_14,negated_conjecture,
    ( k4_tarski(k1_mcart_1(esk8_0),k2_mcart_1(esk8_0)) = esk8_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_10]),c_0_11])])).

cnf(c_0_15,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,negated_conjecture,
    ( ~ r2_hidden(k1_mcart_1(esk8_0),k1_relat_1(esk7_0))
    | ~ r2_hidden(k2_mcart_1(esk8_0),k2_relat_1(esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_17,negated_conjecture,
    ( r2_hidden(k2_mcart_1(esk8_0),k2_relat_1(X1))
    | ~ r2_hidden(esk8_0,X1) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_18,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2) ),
    inference(er,[status(thm)],[c_0_15])).

cnf(c_0_19,negated_conjecture,
    ( ~ r2_hidden(k1_mcart_1(esk8_0),k1_relat_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_10])])).

cnf(c_0_20,negated_conjecture,
    ( r2_hidden(k1_mcart_1(esk8_0),k1_relat_1(X1))
    | ~ r2_hidden(esk8_0,X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_14])).

cnf(c_0_21,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_10])]),
    [proof]).

%------------------------------------------------------------------------------
