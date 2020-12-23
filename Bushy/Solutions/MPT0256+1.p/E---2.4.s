%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : zfmisc_1__t51_zfmisc_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:42:08 EDT 2019

% Result     : Theorem 0.22s
% Output     : CNFRefutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :    9 (  12 expanded)
%              Number of clauses        :    4 (   4 expanded)
%              Number of leaves         :    2 (   3 expanded)
%              Depth                    :    4
%              Number of atoms          :   15 (  21 expanded)
%              Number of equality atoms :    7 (  10 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t51_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( k3_xboole_0(X1,k1_tarski(X2)) = k1_tarski(X2)
     => r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t51_zfmisc_1.p',t51_zfmisc_1)).

fof(l29_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k3_xboole_0(X1,k1_tarski(X2)) = k1_tarski(X2)
     => r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t51_zfmisc_1.p',l29_zfmisc_1)).

fof(c_0_2,negated_conjecture,(
    ~ ! [X1,X2] :
        ( k3_xboole_0(X1,k1_tarski(X2)) = k1_tarski(X2)
       => r2_hidden(X2,X1) ) ),
    inference(assume_negation,[status(cth)],[t51_zfmisc_1])).

fof(c_0_3,plain,(
    ! [X16,X17] :
      ( k3_xboole_0(X16,k1_tarski(X17)) != k1_tarski(X17)
      | r2_hidden(X17,X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l29_zfmisc_1])])).

fof(c_0_4,negated_conjecture,
    ( k3_xboole_0(esk1_0,k1_tarski(esk2_0)) = k1_tarski(esk2_0)
    & ~ r2_hidden(esk2_0,esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_2])])])).

cnf(c_0_5,plain,
    ( r2_hidden(X2,X1)
    | k3_xboole_0(X1,k1_tarski(X2)) != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_6,negated_conjecture,
    ( k3_xboole_0(esk1_0,k1_tarski(esk2_0)) = k1_tarski(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_7,negated_conjecture,
    ( ~ r2_hidden(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_5,c_0_6]),c_0_7]),
    [proof]).
%------------------------------------------------------------------------------
