%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : zfmisc_1__t67_zfmisc_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:42:10 EDT 2019

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   11 (  16 expanded)
%              Number of clauses        :    6 (   6 expanded)
%              Number of leaves         :    2 (   4 expanded)
%              Depth                    :    5
%              Number of atoms          :   24 (  38 expanded)
%              Number of equality atoms :   11 (  18 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t67_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( k4_xboole_0(k1_tarski(X1),X2) = k1_tarski(X1)
    <=> ~ r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t67_zfmisc_1.p',t67_zfmisc_1)).

fof(l33_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(k1_tarski(X1),X2) = k1_tarski(X1)
    <=> ~ r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t67_zfmisc_1.p',l33_zfmisc_1)).

fof(c_0_2,negated_conjecture,(
    ~ ! [X1,X2] :
        ( k4_xboole_0(k1_tarski(X1),X2) = k1_tarski(X1)
      <=> ~ r2_hidden(X1,X2) ) ),
    inference(assume_negation,[status(cth)],[t67_zfmisc_1])).

fof(c_0_3,plain,(
    ! [X14,X15] :
      ( ( k4_xboole_0(k1_tarski(X14),X15) != k1_tarski(X14)
        | ~ r2_hidden(X14,X15) )
      & ( r2_hidden(X14,X15)
        | k4_xboole_0(k1_tarski(X14),X15) = k1_tarski(X14) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l33_zfmisc_1])])])).

fof(c_0_4,negated_conjecture,
    ( ( k4_xboole_0(k1_tarski(esk1_0),esk2_0) != k1_tarski(esk1_0)
      | r2_hidden(esk1_0,esk2_0) )
    & ( k4_xboole_0(k1_tarski(esk1_0),esk2_0) = k1_tarski(esk1_0)
      | ~ r2_hidden(esk1_0,esk2_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_2])])])])).

cnf(c_0_5,plain,
    ( k4_xboole_0(k1_tarski(X1),X2) != k1_tarski(X1)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_6,negated_conjecture,
    ( k4_xboole_0(k1_tarski(esk1_0),esk2_0) = k1_tarski(esk1_0)
    | ~ r2_hidden(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_7,negated_conjecture,
    ( r2_hidden(esk1_0,esk2_0)
    | k4_xboole_0(k1_tarski(esk1_0),esk2_0) != k1_tarski(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,plain,
    ( r2_hidden(X1,X2)
    | k4_xboole_0(k1_tarski(X1),X2) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_9,negated_conjecture,
    ( ~ r2_hidden(esk1_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_5,c_0_6])).

cnf(c_0_10,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_7,c_0_8]),c_0_9]),
    [proof]).
%------------------------------------------------------------------------------
