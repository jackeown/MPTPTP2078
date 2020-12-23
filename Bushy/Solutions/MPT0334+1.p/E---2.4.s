%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : zfmisc_1__t147_zfmisc_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:42:02 EDT 2019

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   17 (  23 expanded)
%              Number of clauses        :    8 (   9 expanded)
%              Number of leaves         :    4 (   6 expanded)
%              Depth                    :    5
%              Number of atoms          :   27 (  36 expanded)
%              Number of equality atoms :   20 (  29 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t147_zfmisc_1,conjecture,(
    ! [X1,X2,X3] :
      ( X1 != X2
     => k4_xboole_0(k2_xboole_0(X3,k1_tarski(X1)),k1_tarski(X2)) = k2_xboole_0(k4_xboole_0(X3,k1_tarski(X2)),k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t147_zfmisc_1.p',t147_zfmisc_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t147_zfmisc_1.p',commutativity_k2_xboole_0)).

fof(t87_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_xboole_0(X1,X2)
     => k2_xboole_0(k4_xboole_0(X3,X1),X2) = k4_xboole_0(k2_xboole_0(X3,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t147_zfmisc_1.p',t87_xboole_1)).

fof(t17_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X1 != X2
     => r1_xboole_0(k1_tarski(X1),k1_tarski(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t147_zfmisc_1.p',t17_zfmisc_1)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( X1 != X2
       => k4_xboole_0(k2_xboole_0(X3,k1_tarski(X1)),k1_tarski(X2)) = k2_xboole_0(k4_xboole_0(X3,k1_tarski(X2)),k1_tarski(X1)) ) ),
    inference(assume_negation,[status(cth)],[t147_zfmisc_1])).

fof(c_0_5,negated_conjecture,
    ( esk1_0 != esk2_0
    & k4_xboole_0(k2_xboole_0(esk3_0,k1_tarski(esk1_0)),k1_tarski(esk2_0)) != k2_xboole_0(k4_xboole_0(esk3_0,k1_tarski(esk2_0)),k1_tarski(esk1_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).

fof(c_0_6,plain,(
    ! [X17,X18] : k2_xboole_0(X17,X18) = k2_xboole_0(X18,X17) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_7,plain,(
    ! [X24,X25,X26] :
      ( ~ r1_xboole_0(X24,X25)
      | k2_xboole_0(k4_xboole_0(X26,X24),X25) = k4_xboole_0(k2_xboole_0(X26,X25),X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t87_xboole_1])])).

fof(c_0_8,plain,(
    ! [X22,X23] :
      ( X22 = X23
      | r1_xboole_0(k1_tarski(X22),k1_tarski(X23)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t17_zfmisc_1])])).

cnf(c_0_9,negated_conjecture,
    ( k4_xboole_0(k2_xboole_0(esk3_0,k1_tarski(esk1_0)),k1_tarski(esk2_0)) != k2_xboole_0(k4_xboole_0(esk3_0,k1_tarski(esk2_0)),k1_tarski(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_10,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( k2_xboole_0(k4_xboole_0(X3,X1),X2) = k4_xboole_0(k2_xboole_0(X3,X2),X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( X1 = X2
    | r1_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,negated_conjecture,
    ( k4_xboole_0(k2_xboole_0(esk3_0,k1_tarski(esk1_0)),k1_tarski(esk2_0)) != k2_xboole_0(k1_tarski(esk1_0),k4_xboole_0(esk3_0,k1_tarski(esk2_0))) ),
    inference(rw,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_14,plain,
    ( k4_xboole_0(k2_xboole_0(X1,k1_tarski(X2)),k1_tarski(X3)) = k2_xboole_0(k4_xboole_0(X1,k1_tarski(X3)),k1_tarski(X2))
    | X3 = X2 ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_15,negated_conjecture,
    ( esk1_0 != esk2_0 ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_16,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_10])]),c_0_15]),
    [proof]).
%------------------------------------------------------------------------------
