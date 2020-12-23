%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : mcart_1__t17_mcart_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:05 EDT 2019

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   24 (  49 expanded)
%              Number of clauses        :   15 (  22 expanded)
%              Number of leaves         :    4 (  11 expanded)
%              Depth                    :    7
%              Number of atoms          :   86 ( 178 expanded)
%              Number of equality atoms :   52 ( 106 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t17_mcart_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(X1,k2_zfmisc_1(k2_tarski(X2,X3),k1_tarski(X4)))
     => ( ( k1_mcart_1(X1) = X2
          | k1_mcart_1(X1) = X3 )
        & k2_mcart_1(X1) = X4 ) ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t17_mcart_1.p',t17_mcart_1)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t17_mcart_1.p',d1_tarski)).

fof(t10_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k2_zfmisc_1(X2,X3))
     => ( r2_hidden(k1_mcart_1(X1),X2)
        & r2_hidden(k2_mcart_1(X1),X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t17_mcart_1.p',t10_mcart_1)).

fof(d2_tarski,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_tarski(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X4 = X1
            | X4 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t17_mcart_1.p',d2_tarski)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( r2_hidden(X1,k2_zfmisc_1(k2_tarski(X2,X3),k1_tarski(X4)))
       => ( ( k1_mcart_1(X1) = X2
            | k1_mcart_1(X1) = X3 )
          & k2_mcart_1(X1) = X4 ) ) ),
    inference(assume_negation,[status(cth)],[t17_mcart_1])).

fof(c_0_5,plain,(
    ! [X13,X14,X15,X16,X17,X18] :
      ( ( ~ r2_hidden(X15,X14)
        | X15 = X13
        | X14 != k1_tarski(X13) )
      & ( X16 != X13
        | r2_hidden(X16,X14)
        | X14 != k1_tarski(X13) )
      & ( ~ r2_hidden(esk5_2(X17,X18),X18)
        | esk5_2(X17,X18) != X17
        | X18 = k1_tarski(X17) )
      & ( r2_hidden(esk5_2(X17,X18),X18)
        | esk5_2(X17,X18) = X17
        | X18 = k1_tarski(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

fof(c_0_6,plain,(
    ! [X31,X32,X33] :
      ( ( r2_hidden(k1_mcart_1(X31),X32)
        | ~ r2_hidden(X31,k2_zfmisc_1(X32,X33)) )
      & ( r2_hidden(k2_mcart_1(X31),X33)
        | ~ r2_hidden(X31,k2_zfmisc_1(X32,X33)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_mcart_1])])])).

fof(c_0_7,negated_conjecture,
    ( r2_hidden(esk1_0,k2_zfmisc_1(k2_tarski(esk2_0,esk3_0),k1_tarski(esk4_0)))
    & ( k1_mcart_1(esk1_0) != esk2_0
      | k2_mcart_1(esk1_0) != esk4_0 )
    & ( k1_mcart_1(esk1_0) != esk3_0
      | k2_mcart_1(esk1_0) != esk4_0 ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])])).

cnf(c_0_8,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( r2_hidden(k2_mcart_1(X1),X2)
    | ~ r2_hidden(X1,k2_zfmisc_1(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,negated_conjecture,
    ( r2_hidden(esk1_0,k2_zfmisc_1(k2_tarski(esk2_0,esk3_0),k1_tarski(esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_11,plain,(
    ! [X20,X21,X22,X23,X24,X25,X26,X27] :
      ( ( ~ r2_hidden(X23,X22)
        | X23 = X20
        | X23 = X21
        | X22 != k2_tarski(X20,X21) )
      & ( X24 != X20
        | r2_hidden(X24,X22)
        | X22 != k2_tarski(X20,X21) )
      & ( X24 != X21
        | r2_hidden(X24,X22)
        | X22 != k2_tarski(X20,X21) )
      & ( esk6_3(X25,X26,X27) != X25
        | ~ r2_hidden(esk6_3(X25,X26,X27),X27)
        | X27 = k2_tarski(X25,X26) )
      & ( esk6_3(X25,X26,X27) != X26
        | ~ r2_hidden(esk6_3(X25,X26,X27),X27)
        | X27 = k2_tarski(X25,X26) )
      & ( r2_hidden(esk6_3(X25,X26,X27),X27)
        | esk6_3(X25,X26,X27) = X25
        | esk6_3(X25,X26,X27) = X26
        | X27 = k2_tarski(X25,X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).

cnf(c_0_12,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k1_tarski(X2)) ),
    inference(er,[status(thm)],[c_0_8])).

cnf(c_0_13,negated_conjecture,
    ( r2_hidden(k2_mcart_1(esk1_0),k1_tarski(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_14,plain,
    ( X1 = X3
    | X1 = X4
    | ~ r2_hidden(X1,X2)
    | X2 != k2_tarski(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,plain,
    ( r2_hidden(k1_mcart_1(X1),X2)
    | ~ r2_hidden(X1,k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_16,negated_conjecture,
    ( k1_mcart_1(esk1_0) != esk2_0
    | k2_mcart_1(esk1_0) != esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_17,negated_conjecture,
    ( k2_mcart_1(esk1_0) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( k1_mcart_1(esk1_0) != esk3_0
    | k2_mcart_1(esk1_0) != esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_19,plain,
    ( X1 = X2
    | X1 = X3
    | ~ r2_hidden(X1,k2_tarski(X3,X2)) ),
    inference(er,[status(thm)],[c_0_14])).

cnf(c_0_20,negated_conjecture,
    ( r2_hidden(k1_mcart_1(esk1_0),k2_tarski(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_15,c_0_10])).

cnf(c_0_21,negated_conjecture,
    ( k1_mcart_1(esk1_0) != esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_16,c_0_17])])).

cnf(c_0_22,negated_conjecture,
    ( k1_mcart_1(esk1_0) != esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_18,c_0_17])])).

cnf(c_0_23,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21]),c_0_22]),
    [proof]).
%------------------------------------------------------------------------------
