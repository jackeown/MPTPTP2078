%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : zfmisc_1__t145_zfmisc_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:42:02 EDT 2019

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   14 (  20 expanded)
%              Number of clauses        :    7 (   7 expanded)
%              Number of leaves         :    3 (   5 expanded)
%              Depth                    :    5
%              Number of atoms          :   26 (  44 expanded)
%              Number of equality atoms :   11 (  17 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t145_zfmisc_1,conjecture,(
    ! [X1,X2,X3] :
      ~ ( ~ r2_hidden(X1,X3)
        & ~ r2_hidden(X2,X3)
        & X3 != k4_xboole_0(k2_xboole_0(X3,k2_tarski(X1,X2)),k2_tarski(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t145_zfmisc_1.p',t145_zfmisc_1)).

fof(t40_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t145_zfmisc_1.p',t40_xboole_1)).

fof(t144_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( ~ r2_hidden(X1,X3)
        & ~ r2_hidden(X2,X3)
        & X3 != k4_xboole_0(X3,k2_tarski(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t145_zfmisc_1.p',t144_zfmisc_1)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ~ ( ~ r2_hidden(X1,X3)
          & ~ r2_hidden(X2,X3)
          & X3 != k4_xboole_0(k2_xboole_0(X3,k2_tarski(X1,X2)),k2_tarski(X1,X2)) ) ),
    inference(assume_negation,[status(cth)],[t145_zfmisc_1])).

fof(c_0_4,negated_conjecture,
    ( ~ r2_hidden(esk1_0,esk3_0)
    & ~ r2_hidden(esk2_0,esk3_0)
    & esk3_0 != k4_xboole_0(k2_xboole_0(esk3_0,k2_tarski(esk1_0,esk2_0)),k2_tarski(esk1_0,esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_3])])])])).

fof(c_0_5,plain,(
    ! [X19,X20] : k4_xboole_0(k2_xboole_0(X19,X20),X20) = k4_xboole_0(X19,X20) ),
    inference(variable_rename,[status(thm)],[t40_xboole_1])).

cnf(c_0_6,negated_conjecture,
    ( esk3_0 != k4_xboole_0(k2_xboole_0(esk3_0,k2_tarski(esk1_0,esk2_0)),k2_tarski(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_7,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_8,plain,(
    ! [X14,X15,X16] :
      ( r2_hidden(X14,X16)
      | r2_hidden(X15,X16)
      | X16 = k4_xboole_0(X16,k2_tarski(X14,X15)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t144_zfmisc_1])])])).

cnf(c_0_9,negated_conjecture,
    ( k4_xboole_0(esk3_0,k2_tarski(esk1_0,esk2_0)) != esk3_0 ),
    inference(rw,[status(thm)],[c_0_6,c_0_7])).

cnf(c_0_10,plain,
    ( r2_hidden(X1,X2)
    | r2_hidden(X3,X2)
    | X2 = k4_xboole_0(X2,k2_tarski(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_11,negated_conjecture,
    ( ~ r2_hidden(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_12,negated_conjecture,
    ( ~ r2_hidden(esk1_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_13,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_10]),c_0_11]),c_0_12]),
    [proof]).
%------------------------------------------------------------------------------
