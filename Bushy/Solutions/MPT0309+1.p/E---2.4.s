%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : zfmisc_1__t121_zfmisc_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:59 EDT 2019

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   17 (  31 expanded)
%              Number of clauses        :    8 (  12 expanded)
%              Number of leaves         :    4 (   9 expanded)
%              Depth                    :    5
%              Number of atoms          :   19 (  37 expanded)
%              Number of equality atoms :   18 (  36 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t121_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4] : k2_zfmisc_1(k2_xboole_0(X1,X2),k2_xboole_0(X3,X4)) = k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X1,X4)),k2_zfmisc_1(X2,X3)),k2_zfmisc_1(X2,X4)) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t121_zfmisc_1.p',t121_zfmisc_1)).

fof(t120_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( k2_zfmisc_1(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))
      & k2_zfmisc_1(X3,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t121_zfmisc_1.p',t120_zfmisc_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t121_zfmisc_1.p',commutativity_k2_xboole_0)).

fof(t4_xboole_1,axiom,(
    ! [X1,X2,X3] : k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t121_zfmisc_1.p',t4_xboole_1)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] : k2_zfmisc_1(k2_xboole_0(X1,X2),k2_xboole_0(X3,X4)) = k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X1,X4)),k2_zfmisc_1(X2,X3)),k2_zfmisc_1(X2,X4)) ),
    inference(assume_negation,[status(cth)],[t121_zfmisc_1])).

fof(c_0_5,negated_conjecture,(
    k2_zfmisc_1(k2_xboole_0(esk1_0,esk2_0),k2_xboole_0(esk3_0,esk4_0)) != k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_zfmisc_1(esk1_0,esk3_0),k2_zfmisc_1(esk1_0,esk4_0)),k2_zfmisc_1(esk2_0,esk3_0)),k2_zfmisc_1(esk2_0,esk4_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).

fof(c_0_6,plain,(
    ! [X12,X13,X14] :
      ( k2_zfmisc_1(k2_xboole_0(X12,X13),X14) = k2_xboole_0(k2_zfmisc_1(X12,X14),k2_zfmisc_1(X13,X14))
      & k2_zfmisc_1(X14,k2_xboole_0(X12,X13)) = k2_xboole_0(k2_zfmisc_1(X14,X12),k2_zfmisc_1(X14,X13)) ) ),
    inference(variable_rename,[status(thm)],[t120_zfmisc_1])).

fof(c_0_7,plain,(
    ! [X9,X10] : k2_xboole_0(X9,X10) = k2_xboole_0(X10,X9) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_8,plain,(
    ! [X15,X16,X17] : k2_xboole_0(k2_xboole_0(X15,X16),X17) = k2_xboole_0(X15,k2_xboole_0(X16,X17)) ),
    inference(variable_rename,[status(thm)],[t4_xboole_1])).

cnf(c_0_9,negated_conjecture,
    ( k2_zfmisc_1(k2_xboole_0(esk1_0,esk2_0),k2_xboole_0(esk3_0,esk4_0)) != k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_zfmisc_1(esk1_0,esk3_0),k2_zfmisc_1(esk1_0,esk4_0)),k2_zfmisc_1(esk2_0,esk3_0)),k2_zfmisc_1(esk2_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_10,plain,
    ( k2_zfmisc_1(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,negated_conjecture,
    ( k2_xboole_0(k2_zfmisc_1(esk2_0,esk3_0),k2_xboole_0(k2_zfmisc_1(esk2_0,esk4_0),k2_zfmisc_1(esk1_0,k2_xboole_0(esk3_0,esk4_0)))) != k2_zfmisc_1(k2_xboole_0(esk1_0,esk2_0),k2_xboole_0(esk3_0,esk4_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_9,c_0_10]),c_0_11]),c_0_12]),c_0_11])).

cnf(c_0_14,plain,
    ( k2_xboole_0(k2_zfmisc_1(X1,X2),k2_xboole_0(k2_zfmisc_1(X1,X3),X4)) = k2_xboole_0(k2_zfmisc_1(X1,k2_xboole_0(X2,X3)),X4) ),
    inference(spm,[status(thm)],[c_0_12,c_0_10])).

cnf(c_0_15,plain,
    ( k2_zfmisc_1(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_16,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_13,c_0_14]),c_0_15]),c_0_11])]),
    [proof]).
%------------------------------------------------------------------------------
