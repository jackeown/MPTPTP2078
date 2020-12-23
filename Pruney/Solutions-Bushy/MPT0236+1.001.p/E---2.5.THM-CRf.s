%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0236+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:39:16 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   20 (  56 expanded)
%              Number of clauses        :   13 (  25 expanded)
%              Number of leaves         :    3 (  13 expanded)
%              Depth                    :    7
%              Number of atoms          :   70 ( 230 expanded)
%              Number of equality atoms :   30 ( 100 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t31_zfmisc_1,conjecture,(
    ! [X1] : k3_tarski(k1_tarski(X1)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_zfmisc_1)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(d4_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k3_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] :
              ( r2_hidden(X3,X4)
              & r2_hidden(X4,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1] : k3_tarski(k1_tarski(X1)) = X1 ),
    inference(assume_negation,[status(cth)],[t31_zfmisc_1])).

fof(c_0_4,plain,(
    ! [X5,X6,X7,X8,X9,X10] :
      ( ( ~ r2_hidden(X7,X6)
        | X7 = X5
        | X6 != k1_tarski(X5) )
      & ( X8 != X5
        | r2_hidden(X8,X6)
        | X6 != k1_tarski(X5) )
      & ( ~ r2_hidden(esk1_2(X9,X10),X10)
        | esk1_2(X9,X10) != X9
        | X10 = k1_tarski(X9) )
      & ( r2_hidden(esk1_2(X9,X10),X10)
        | esk1_2(X9,X10) = X9
        | X10 = k1_tarski(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

fof(c_0_5,negated_conjecture,(
    k3_tarski(k1_tarski(esk5_0)) != esk5_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])).

fof(c_0_6,plain,(
    ! [X12,X13,X14,X16,X17,X18,X19,X21] :
      ( ( r2_hidden(X14,esk2_3(X12,X13,X14))
        | ~ r2_hidden(X14,X13)
        | X13 != k3_tarski(X12) )
      & ( r2_hidden(esk2_3(X12,X13,X14),X12)
        | ~ r2_hidden(X14,X13)
        | X13 != k3_tarski(X12) )
      & ( ~ r2_hidden(X16,X17)
        | ~ r2_hidden(X17,X12)
        | r2_hidden(X16,X13)
        | X13 != k3_tarski(X12) )
      & ( ~ r2_hidden(esk3_2(X18,X19),X19)
        | ~ r2_hidden(esk3_2(X18,X19),X21)
        | ~ r2_hidden(X21,X18)
        | X19 = k3_tarski(X18) )
      & ( r2_hidden(esk3_2(X18,X19),esk4_2(X18,X19))
        | r2_hidden(esk3_2(X18,X19),X19)
        | X19 = k3_tarski(X18) )
      & ( r2_hidden(esk4_2(X18,X19),X18)
        | r2_hidden(esk3_2(X18,X19),X19)
        | X19 = k3_tarski(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tarski])])])])])])).

cnf(c_0_7,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,negated_conjecture,
    ( k3_tarski(k1_tarski(esk5_0)) != esk5_0 ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( r2_hidden(esk4_2(X1,X2),X1)
    | r2_hidden(esk3_2(X1,X2),X2)
    | X2 = k3_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( r2_hidden(esk3_2(X1,X2),esk4_2(X1,X2))
    | r2_hidden(esk3_2(X1,X2),X2)
    | X2 = k3_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k1_tarski(X2)) ),
    inference(er,[status(thm)],[c_0_7])).

cnf(c_0_12,negated_conjecture,
    ( r2_hidden(esk4_2(k1_tarski(esk5_0),esk5_0),k1_tarski(esk5_0))
    | r2_hidden(esk3_2(k1_tarski(esk5_0),esk5_0),esk5_0) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_8,c_0_9])])).

cnf(c_0_13,negated_conjecture,
    ( r2_hidden(esk3_2(k1_tarski(esk5_0),esk5_0),esk4_2(k1_tarski(esk5_0),esk5_0))
    | r2_hidden(esk3_2(k1_tarski(esk5_0),esk5_0),esk5_0) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_8,c_0_10])])).

cnf(c_0_14,negated_conjecture,
    ( esk4_2(k1_tarski(esk5_0),esk5_0) = esk5_0
    | r2_hidden(esk3_2(k1_tarski(esk5_0),esk5_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_15,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_16,plain,
    ( X2 = k3_tarski(X1)
    | ~ r2_hidden(esk3_2(X1,X2),X2)
    | ~ r2_hidden(esk3_2(X1,X2),X3)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_17,negated_conjecture,
    ( r2_hidden(esk3_2(k1_tarski(esk5_0),esk5_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_18,plain,
    ( r2_hidden(X1,k1_tarski(X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_15])])).

cnf(c_0_19,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_17]),c_0_18])]),c_0_8]),
    [proof]).

%------------------------------------------------------------------------------
