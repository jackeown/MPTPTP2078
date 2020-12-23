%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : zfmisc_1__t27_zfmisc_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:42:04 EDT 2019

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   23 (  63 expanded)
%              Number of clauses        :   14 (  29 expanded)
%              Number of leaves         :    4 (  15 expanded)
%              Depth                    :    8
%              Number of atoms          :   31 (  88 expanded)
%              Number of equality atoms :   19 (  55 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t27_zfmisc_1,conjecture,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_tarski(X1,X2),k1_tarski(X3))
     => k2_tarski(X1,X2) = k1_tarski(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t27_zfmisc_1.p',t27_zfmisc_1)).

fof(t26_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_tarski(X1,X2),k1_tarski(X3))
     => X1 = X3 ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t27_zfmisc_1.p',t26_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t27_zfmisc_1.p',t69_enumset1)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t27_zfmisc_1.p',commutativity_k2_tarski)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( r1_tarski(k2_tarski(X1,X2),k1_tarski(X3))
       => k2_tarski(X1,X2) = k1_tarski(X3) ) ),
    inference(assume_negation,[status(cth)],[t27_zfmisc_1])).

fof(c_0_5,plain,(
    ! [X11,X12,X13] :
      ( ~ r1_tarski(k2_tarski(X11,X12),k1_tarski(X13))
      | X11 = X13 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_zfmisc_1])])).

fof(c_0_6,plain,(
    ! [X14] : k2_tarski(X14,X14) = k1_tarski(X14) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_7,negated_conjecture,
    ( r1_tarski(k2_tarski(esk1_0,esk2_0),k1_tarski(esk3_0))
    & k2_tarski(esk1_0,esk2_0) != k1_tarski(esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).

cnf(c_0_8,plain,
    ( X1 = X3
    | ~ r1_tarski(k2_tarski(X1,X2),k1_tarski(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,negated_conjecture,
    ( r1_tarski(k2_tarski(esk1_0,esk2_0),k1_tarski(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_11,plain,(
    ! [X9,X10] : k2_tarski(X9,X10) = k2_tarski(X10,X9) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

cnf(c_0_12,plain,
    ( X1 = X3
    | ~ r1_tarski(k2_tarski(X1,X2),k2_tarski(X3,X3)) ),
    inference(rw,[status(thm)],[c_0_8,c_0_9])).

cnf(c_0_13,negated_conjecture,
    ( r1_tarski(k2_tarski(esk1_0,esk2_0),k2_tarski(esk3_0,esk3_0)) ),
    inference(rw,[status(thm)],[c_0_10,c_0_9])).

cnf(c_0_14,negated_conjecture,
    ( k2_tarski(esk1_0,esk2_0) != k1_tarski(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_15,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( esk1_0 = esk3_0 ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_17,negated_conjecture,
    ( k2_tarski(esk3_0,esk3_0) != k2_tarski(esk1_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_14,c_0_9])).

cnf(c_0_18,plain,
    ( X1 = X2
    | ~ r1_tarski(k2_tarski(X3,X1),k2_tarski(X2,X2)) ),
    inference(spm,[status(thm)],[c_0_12,c_0_15])).

cnf(c_0_19,negated_conjecture,
    ( r1_tarski(k2_tarski(esk3_0,esk2_0),k2_tarski(esk3_0,esk3_0)) ),
    inference(rw,[status(thm)],[c_0_13,c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( k2_tarski(esk3_0,esk2_0) != k2_tarski(esk3_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_17,c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( esk2_0 = esk3_0 ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_22,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_20,c_0_21])]),
    [proof]).
%------------------------------------------------------------------------------
