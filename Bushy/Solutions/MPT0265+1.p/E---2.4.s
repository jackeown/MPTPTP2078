%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : zfmisc_1__t60_zfmisc_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:42:09 EDT 2019

% Result     : Theorem 7.44s
% Output     : CNFRefutation 7.44s
% Verified   : 
% Statistics : Number of formulae       :   40 ( 272 expanded)
%              Number of clauses        :   29 ( 130 expanded)
%              Number of leaves         :    5 (  63 expanded)
%              Depth                    :   11
%              Number of atoms          :  133 (1101 expanded)
%              Number of equality atoms :   65 ( 588 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t60_zfmisc_1.p',d4_xboole_0)).

fof(t60_zfmisc_1,conjecture,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,X2)
     => ( ( r2_hidden(X3,X2)
          & X1 != X3 )
        | k3_xboole_0(k2_tarski(X1,X3),X2) = k1_tarski(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t60_zfmisc_1.p',t60_zfmisc_1)).

fof(d2_tarski,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_tarski(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X4 = X1
            | X4 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t60_zfmisc_1.p',d2_tarski)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t60_zfmisc_1.p',d1_tarski)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t60_zfmisc_1.p',commutativity_k3_xboole_0)).

fof(c_0_5,plain,(
    ! [X30,X31,X32,X33,X34,X35,X36,X37] :
      ( ( r2_hidden(X33,X30)
        | ~ r2_hidden(X33,X32)
        | X32 != k3_xboole_0(X30,X31) )
      & ( r2_hidden(X33,X31)
        | ~ r2_hidden(X33,X32)
        | X32 != k3_xboole_0(X30,X31) )
      & ( ~ r2_hidden(X34,X30)
        | ~ r2_hidden(X34,X31)
        | r2_hidden(X34,X32)
        | X32 != k3_xboole_0(X30,X31) )
      & ( ~ r2_hidden(esk6_3(X35,X36,X37),X37)
        | ~ r2_hidden(esk6_3(X35,X36,X37),X35)
        | ~ r2_hidden(esk6_3(X35,X36,X37),X36)
        | X37 = k3_xboole_0(X35,X36) )
      & ( r2_hidden(esk6_3(X35,X36,X37),X35)
        | r2_hidden(esk6_3(X35,X36,X37),X37)
        | X37 = k3_xboole_0(X35,X36) )
      & ( r2_hidden(esk6_3(X35,X36,X37),X36)
        | r2_hidden(esk6_3(X35,X36,X37),X37)
        | X37 = k3_xboole_0(X35,X36) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( r2_hidden(X1,X2)
       => ( ( r2_hidden(X3,X2)
            & X1 != X3 )
          | k3_xboole_0(k2_tarski(X1,X3),X2) = k1_tarski(X1) ) ) ),
    inference(assume_negation,[status(cth)],[t60_zfmisc_1])).

cnf(c_0_7,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X4 != k3_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_8,negated_conjecture,
    ( r2_hidden(esk1_0,esk2_0)
    & ( ~ r2_hidden(esk3_0,esk2_0)
      | esk1_0 = esk3_0 )
    & k3_xboole_0(k2_tarski(esk1_0,esk3_0),esk2_0) != k1_tarski(esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).

fof(c_0_9,plain,(
    ! [X21,X22,X23,X24,X25,X26,X27,X28] :
      ( ( ~ r2_hidden(X24,X23)
        | X24 = X21
        | X24 = X22
        | X23 != k2_tarski(X21,X22) )
      & ( X25 != X21
        | r2_hidden(X25,X23)
        | X23 != k2_tarski(X21,X22) )
      & ( X25 != X22
        | r2_hidden(X25,X23)
        | X23 != k2_tarski(X21,X22) )
      & ( esk5_3(X26,X27,X28) != X26
        | ~ r2_hidden(esk5_3(X26,X27,X28),X28)
        | X28 = k2_tarski(X26,X27) )
      & ( esk5_3(X26,X27,X28) != X27
        | ~ r2_hidden(esk5_3(X26,X27,X28),X28)
        | X28 = k2_tarski(X26,X27) )
      & ( r2_hidden(esk5_3(X26,X27,X28),X28)
        | esk5_3(X26,X27,X28) = X26
        | esk5_3(X26,X27,X28) = X27
        | X28 = k2_tarski(X26,X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).

fof(c_0_10,plain,(
    ! [X14,X15,X16,X17,X18,X19] :
      ( ( ~ r2_hidden(X16,X15)
        | X16 = X14
        | X15 != k1_tarski(X14) )
      & ( X17 != X14
        | r2_hidden(X17,X15)
        | X15 != k1_tarski(X14) )
      & ( ~ r2_hidden(esk4_2(X18,X19),X19)
        | esk4_2(X18,X19) != X18
        | X19 = k1_tarski(X18) )
      & ( r2_hidden(esk4_2(X18,X19),X19)
        | esk4_2(X18,X19) = X18
        | X19 = k1_tarski(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

cnf(c_0_11,plain,
    ( r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_7])).

cnf(c_0_12,negated_conjecture,
    ( r2_hidden(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_14,plain,(
    ! [X12,X13] : k3_xboole_0(X12,X13) = k3_xboole_0(X13,X12) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_15,plain,
    ( X2 = k1_tarski(X1)
    | ~ r2_hidden(esk4_2(X1,X2),X2)
    | esk4_2(X1,X2) != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( r2_hidden(esk4_2(X1,X2),X2)
    | esk4_2(X1,X2) = X1
    | X2 = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,negated_conjecture,
    ( r2_hidden(esk1_0,k3_xboole_0(X1,esk2_0))
    | ~ r2_hidden(esk1_0,X1) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_18,plain,
    ( r2_hidden(X1,k2_tarski(X1,X2)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_13])])).

cnf(c_0_19,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,negated_conjecture,
    ( k3_xboole_0(k2_tarski(esk1_0,esk3_0),esk2_0) != k1_tarski(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_21,plain,
    ( X1 = k1_tarski(X2)
    | r2_hidden(esk4_2(X2,X1),X1)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(esk1_0,k3_xboole_0(esk2_0,k2_tarski(esk1_0,X1))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19])).

cnf(c_0_23,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_24,negated_conjecture,
    ( k3_xboole_0(esk2_0,k2_tarski(esk1_0,esk3_0)) != k1_tarski(esk1_0) ),
    inference(rw,[status(thm)],[c_0_20,c_0_19])).

cnf(c_0_25,negated_conjecture,
    ( k3_xboole_0(esk2_0,k2_tarski(esk1_0,X1)) = k1_tarski(esk1_0)
    | r2_hidden(esk4_2(esk1_0,k3_xboole_0(esk2_0,k2_tarski(esk1_0,X1))),k3_xboole_0(esk2_0,k2_tarski(esk1_0,X1))) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_26,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_27,plain,
    ( X1 = X3
    | X1 = X4
    | ~ r2_hidden(X1,X2)
    | X2 != k2_tarski(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_28,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X3,X2)) ),
    inference(er,[status(thm)],[c_0_23])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(esk4_2(esk1_0,k3_xboole_0(esk2_0,k2_tarski(esk1_0,esk3_0))),k3_xboole_0(esk2_0,k2_tarski(esk1_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_30,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_26])).

cnf(c_0_31,plain,
    ( X1 = X2
    | X1 = X3
    | ~ r2_hidden(X1,k2_tarski(X3,X2)) ),
    inference(er,[status(thm)],[c_0_27])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(esk4_2(esk1_0,k3_xboole_0(esk2_0,k2_tarski(esk1_0,esk3_0))),k2_tarski(esk1_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_33,negated_conjecture,
    ( esk4_2(esk1_0,k3_xboole_0(esk2_0,k2_tarski(esk1_0,esk3_0))) != esk1_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_29]),c_0_24])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(esk4_2(esk1_0,k3_xboole_0(esk2_0,k2_tarski(esk1_0,esk3_0))),esk2_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_29])).

cnf(c_0_35,negated_conjecture,
    ( esk4_2(esk1_0,k3_xboole_0(esk2_0,k2_tarski(esk1_0,esk3_0))) = esk3_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33])).

cnf(c_0_36,negated_conjecture,
    ( esk1_0 = esk3_0
    | ~ r2_hidden(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(esk3_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_38,negated_conjecture,
    ( esk3_0 != esk1_0 ),
    inference(rw,[status(thm)],[c_0_33,c_0_35])).

cnf(c_0_39,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_37])]),c_0_38]),
    [proof]).
%------------------------------------------------------------------------------
