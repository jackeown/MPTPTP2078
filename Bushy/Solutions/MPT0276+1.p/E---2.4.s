%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : zfmisc_1__t74_zfmisc_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:42:11 EDT 2019

% Result     : Theorem 151.26s
% Output     : CNFRefutation 151.26s
% Verified   : 
% Statistics : Number of formulae       :   36 (  90 expanded)
%              Number of clauses        :   23 (  40 expanded)
%              Number of leaves         :    6 (  22 expanded)
%              Depth                    :   10
%              Number of atoms          :   90 ( 278 expanded)
%              Number of equality atoms :   51 ( 178 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   11 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t74_zfmisc_1,conjecture,(
    ! [X1,X2,X3] :
      ~ ( k4_xboole_0(k2_tarski(X1,X2),X3) != k1_xboole_0
        & k4_xboole_0(k2_tarski(X1,X2),X3) != k1_tarski(X1)
        & k4_xboole_0(k2_tarski(X1,X2),X3) != k1_tarski(X2)
        & k4_xboole_0(k2_tarski(X1,X2),X3) != k2_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t74_zfmisc_1.p',t74_zfmisc_1)).

fof(t72_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( k4_xboole_0(k2_tarski(X1,X2),X3) = k2_tarski(X1,X2)
    <=> ( ~ r2_hidden(X1,X3)
        & ~ r2_hidden(X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t74_zfmisc_1.p',t72_zfmisc_1)).

fof(l38_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( k4_xboole_0(k2_tarski(X1,X2),X3) = k1_tarski(X1)
    <=> ( ~ r2_hidden(X1,X3)
        & ( r2_hidden(X2,X3)
          | X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t74_zfmisc_1.p',l38_zfmisc_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t74_zfmisc_1.p',t3_boole)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t74_zfmisc_1.p',commutativity_k2_tarski)).

fof(t73_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( k4_xboole_0(k2_tarski(X1,X2),X3) = k1_xboole_0
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t74_zfmisc_1.p',t73_zfmisc_1)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ~ ( k4_xboole_0(k2_tarski(X1,X2),X3) != k1_xboole_0
          & k4_xboole_0(k2_tarski(X1,X2),X3) != k1_tarski(X1)
          & k4_xboole_0(k2_tarski(X1,X2),X3) != k1_tarski(X2)
          & k4_xboole_0(k2_tarski(X1,X2),X3) != k2_tarski(X1,X2) ) ),
    inference(assume_negation,[status(cth)],[t74_zfmisc_1])).

fof(c_0_7,negated_conjecture,
    ( k4_xboole_0(k2_tarski(esk1_0,esk2_0),esk3_0) != k1_xboole_0
    & k4_xboole_0(k2_tarski(esk1_0,esk2_0),esk3_0) != k1_tarski(esk1_0)
    & k4_xboole_0(k2_tarski(esk1_0,esk2_0),esk3_0) != k1_tarski(esk2_0)
    & k4_xboole_0(k2_tarski(esk1_0,esk2_0),esk3_0) != k2_tarski(esk1_0,esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).

fof(c_0_8,plain,(
    ! [X17,X18,X19] :
      ( ( ~ r2_hidden(X17,X19)
        | k4_xboole_0(k2_tarski(X17,X18),X19) != k2_tarski(X17,X18) )
      & ( ~ r2_hidden(X18,X19)
        | k4_xboole_0(k2_tarski(X17,X18),X19) != k2_tarski(X17,X18) )
      & ( r2_hidden(X17,X19)
        | r2_hidden(X18,X19)
        | k4_xboole_0(k2_tarski(X17,X18),X19) = k2_tarski(X17,X18) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t72_zfmisc_1])])])])).

fof(c_0_9,plain,(
    ! [X11,X12,X13] :
      ( ( ~ r2_hidden(X11,X13)
        | k4_xboole_0(k2_tarski(X11,X12),X13) != k1_tarski(X11) )
      & ( r2_hidden(X12,X13)
        | X11 = X12
        | k4_xboole_0(k2_tarski(X11,X12),X13) != k1_tarski(X11) )
      & ( ~ r2_hidden(X12,X13)
        | r2_hidden(X11,X13)
        | k4_xboole_0(k2_tarski(X11,X12),X13) = k1_tarski(X11) )
      & ( X11 != X12
        | r2_hidden(X11,X13)
        | k4_xboole_0(k2_tarski(X11,X12),X13) = k1_tarski(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l38_zfmisc_1])])])])).

cnf(c_0_10,negated_conjecture,
    ( k4_xboole_0(k2_tarski(esk1_0,esk2_0),esk3_0) != k2_tarski(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,plain,
    ( r2_hidden(X1,X2)
    | r2_hidden(X3,X2)
    | k4_xboole_0(k2_tarski(X1,X3),X2) = k2_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_12,plain,(
    ! [X14] : k4_xboole_0(X14,k1_xboole_0) = X14 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

cnf(c_0_13,plain,
    ( r2_hidden(X3,X2)
    | k4_xboole_0(k2_tarski(X3,X1),X2) = k1_tarski(X3)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,negated_conjecture,
    ( r2_hidden(esk1_0,esk3_0)
    | r2_hidden(esk2_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_15,plain,
    ( r2_hidden(X1,X3)
    | k4_xboole_0(k2_tarski(X1,X2),X3) = k1_tarski(X1)
    | X1 != X2 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,plain,
    ( ~ r2_hidden(X1,X2)
    | k4_xboole_0(k2_tarski(X3,X1),X2) != k2_tarski(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_17,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,negated_conjecture,
    ( k4_xboole_0(k2_tarski(esk1_0,esk2_0),esk3_0) != k1_tarski(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_19,negated_conjecture,
    ( k4_xboole_0(k2_tarski(X1,esk2_0),esk3_0) = k1_tarski(X1)
    | r2_hidden(esk1_0,esk3_0)
    | r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_20,plain,
    ( k4_xboole_0(k2_tarski(X1,X1),X2) = k1_tarski(X1)
    | r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(esk1_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

fof(c_0_23,plain,(
    ! [X9,X10] : k2_tarski(X9,X10) = k2_tarski(X10,X9) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

fof(c_0_24,plain,(
    ! [X20,X21,X22] :
      ( ( r2_hidden(X20,X22)
        | k4_xboole_0(k2_tarski(X20,X21),X22) != k1_xboole_0 )
      & ( r2_hidden(X21,X22)
        | k4_xboole_0(k2_tarski(X20,X21),X22) != k1_xboole_0 )
      & ( ~ r2_hidden(X20,X22)
        | ~ r2_hidden(X21,X22)
        | k4_xboole_0(k2_tarski(X20,X21),X22) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t73_zfmisc_1])])])).

cnf(c_0_25,negated_conjecture,
    ( k4_xboole_0(k2_tarski(esk1_0,esk2_0),esk3_0) != k1_tarski(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_26,plain,
    ( k1_tarski(X1) = k2_tarski(X1,X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_20]),c_0_21])).

cnf(c_0_27,negated_conjecture,
    ( k4_xboole_0(k2_tarski(X1,esk1_0),esk3_0) = k1_tarski(X1)
    | r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_13,c_0_22])).

cnf(c_0_28,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,plain,
    ( k4_xboole_0(k2_tarski(X1,X3),X2) = k1_xboole_0
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_30,negated_conjecture,
    ( k4_xboole_0(k2_tarski(esk1_0,esk2_0),esk3_0) != k2_tarski(esk2_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_31,negated_conjecture,
    ( k4_xboole_0(k2_tarski(esk1_0,X1),esk3_0) = k1_tarski(X1)
    | r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_32,negated_conjecture,
    ( k4_xboole_0(k2_tarski(X1,esk1_0),esk3_0) = k1_xboole_0
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_22])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_26])])).

cnf(c_0_34,negated_conjecture,
    ( k4_xboole_0(k2_tarski(esk1_0,esk2_0),esk3_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_35,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_28]),c_0_34]),
    [proof]).
%------------------------------------------------------------------------------
