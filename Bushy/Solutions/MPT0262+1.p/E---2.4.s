%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : zfmisc_1__t57_zfmisc_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:42:09 EDT 2019

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   28 (  63 expanded)
%              Number of clauses        :   17 (  28 expanded)
%              Number of leaves         :    5 (  15 expanded)
%              Depth                    :    8
%              Number of atoms          :   97 ( 217 expanded)
%              Number of equality atoms :   37 (  58 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t57_zfmisc_1,conjecture,(
    ! [X1,X2,X3] :
      ~ ( ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X3,X2)
        & ~ r1_xboole_0(k2_tarski(X1,X3),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t57_zfmisc_1.p',t57_zfmisc_1)).

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t57_zfmisc_1.p',d4_xboole_0)).

fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t57_zfmisc_1.p',t4_xboole_0)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t57_zfmisc_1.p',commutativity_k3_xboole_0)).

fof(d2_tarski,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_tarski(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X4 = X1
            | X4 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t57_zfmisc_1.p',d2_tarski)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ~ ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X3,X2)
          & ~ r1_xboole_0(k2_tarski(X1,X3),X2) ) ),
    inference(assume_negation,[status(cth)],[t57_zfmisc_1])).

fof(c_0_6,plain,(
    ! [X23,X24,X25,X26,X27,X28,X29,X30] :
      ( ( r2_hidden(X26,X23)
        | ~ r2_hidden(X26,X25)
        | X25 != k3_xboole_0(X23,X24) )
      & ( r2_hidden(X26,X24)
        | ~ r2_hidden(X26,X25)
        | X25 != k3_xboole_0(X23,X24) )
      & ( ~ r2_hidden(X27,X23)
        | ~ r2_hidden(X27,X24)
        | r2_hidden(X27,X25)
        | X25 != k3_xboole_0(X23,X24) )
      & ( ~ r2_hidden(esk5_3(X28,X29,X30),X30)
        | ~ r2_hidden(esk5_3(X28,X29,X30),X28)
        | ~ r2_hidden(esk5_3(X28,X29,X30),X29)
        | X30 = k3_xboole_0(X28,X29) )
      & ( r2_hidden(esk5_3(X28,X29,X30),X28)
        | r2_hidden(esk5_3(X28,X29,X30),X30)
        | X30 = k3_xboole_0(X28,X29) )
      & ( r2_hidden(esk5_3(X28,X29,X30),X29)
        | r2_hidden(esk5_3(X28,X29,X30),X30)
        | X30 = k3_xboole_0(X28,X29) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

fof(c_0_7,negated_conjecture,
    ( ~ r2_hidden(esk1_0,esk2_0)
    & ~ r2_hidden(esk3_0,esk2_0)
    & ~ r1_xboole_0(k2_tarski(esk1_0,esk3_0),esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_5])])])])).

fof(c_0_8,plain,(
    ! [X36,X37,X39,X40,X41] :
      ( ( r1_xboole_0(X36,X37)
        | r2_hidden(esk6_2(X36,X37),k3_xboole_0(X36,X37)) )
      & ( ~ r2_hidden(X41,k3_xboole_0(X39,X40))
        | ~ r1_xboole_0(X39,X40) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

fof(c_0_9,plain,(
    ! [X12,X13] : k3_xboole_0(X12,X13) = k3_xboole_0(X13,X12) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_10,plain,(
    ! [X14,X15,X16,X17,X18,X19,X20,X21] :
      ( ( ~ r2_hidden(X17,X16)
        | X17 = X14
        | X17 = X15
        | X16 != k2_tarski(X14,X15) )
      & ( X18 != X14
        | r2_hidden(X18,X16)
        | X16 != k2_tarski(X14,X15) )
      & ( X18 != X15
        | r2_hidden(X18,X16)
        | X16 != k2_tarski(X14,X15) )
      & ( esk4_3(X19,X20,X21) != X19
        | ~ r2_hidden(esk4_3(X19,X20,X21),X21)
        | X21 = k2_tarski(X19,X20) )
      & ( esk4_3(X19,X20,X21) != X20
        | ~ r2_hidden(esk4_3(X19,X20,X21),X21)
        | X21 = k2_tarski(X19,X20) )
      & ( r2_hidden(esk4_3(X19,X20,X21),X21)
        | esk4_3(X19,X20,X21) = X19
        | esk4_3(X19,X20,X21) = X20
        | X21 = k2_tarski(X19,X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).

cnf(c_0_11,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_12,negated_conjecture,
    ( ~ r1_xboole_0(k2_tarski(esk1_0,esk3_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk6_2(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_16,plain,
    ( X1 = X3
    | X1 = X4
    | ~ r2_hidden(X1,X2)
    | X2 != k2_tarski(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X3,X2)) ),
    inference(er,[status(thm)],[c_0_11])).

cnf(c_0_18,negated_conjecture,
    ( r2_hidden(esk6_2(k2_tarski(esk1_0,esk3_0),esk2_0),k3_xboole_0(esk2_0,k2_tarski(esk1_0,esk3_0))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_14])).

cnf(c_0_19,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_15])).

cnf(c_0_20,plain,
    ( X1 = X2
    | X1 = X3
    | ~ r2_hidden(X1,k2_tarski(X3,X2)) ),
    inference(er,[status(thm)],[c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( r2_hidden(esk6_2(k2_tarski(esk1_0,esk3_0),esk2_0),k2_tarski(esk1_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(esk6_2(k2_tarski(esk1_0,esk3_0),esk2_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( esk6_2(k2_tarski(esk1_0,esk3_0),esk2_0) = esk3_0
    | esk6_2(k2_tarski(esk1_0,esk3_0),esk2_0) = esk1_0 ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_24,negated_conjecture,
    ( ~ r2_hidden(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_25,negated_conjecture,
    ( esk6_2(k2_tarski(esk1_0,esk3_0),esk2_0) = esk1_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24])).

cnf(c_0_26,negated_conjecture,
    ( ~ r2_hidden(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_27,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_22,c_0_25]),c_0_26]),
    [proof]).
%------------------------------------------------------------------------------
