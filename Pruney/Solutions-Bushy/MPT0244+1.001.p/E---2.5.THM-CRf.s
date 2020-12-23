%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0244+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:39:17 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   17 (  61 expanded)
%              Number of clauses        :   12 (  26 expanded)
%              Number of leaves         :    2 (  14 expanded)
%              Depth                    :    7
%              Number of atoms          :   45 ( 215 expanded)
%              Number of equality atoms :   26 ( 132 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t39_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( r1_tarski(X1,k1_tarski(X2))
    <=> ( X1 = k1_xboole_0
        | X1 = k1_tarski(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_zfmisc_1)).

fof(l3_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,k1_tarski(X2))
    <=> ( X1 = k1_xboole_0
        | X1 = k1_tarski(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(c_0_2,negated_conjecture,(
    ~ ! [X1,X2] :
        ( r1_tarski(X1,k1_tarski(X2))
      <=> ( X1 = k1_xboole_0
          | X1 = k1_tarski(X2) ) ) ),
    inference(assume_negation,[status(cth)],[t39_zfmisc_1])).

fof(c_0_3,plain,(
    ! [X3,X4] :
      ( ( ~ r1_tarski(X3,k1_tarski(X4))
        | X3 = k1_xboole_0
        | X3 = k1_tarski(X4) )
      & ( X3 != k1_xboole_0
        | r1_tarski(X3,k1_tarski(X4)) )
      & ( X3 != k1_tarski(X4)
        | r1_tarski(X3,k1_tarski(X4)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_zfmisc_1])])])).

fof(c_0_4,negated_conjecture,
    ( ( esk1_0 != k1_xboole_0
      | ~ r1_tarski(esk1_0,k1_tarski(esk2_0)) )
    & ( esk1_0 != k1_tarski(esk2_0)
      | ~ r1_tarski(esk1_0,k1_tarski(esk2_0)) )
    & ( r1_tarski(esk1_0,k1_tarski(esk2_0))
      | esk1_0 = k1_xboole_0
      | esk1_0 = k1_tarski(esk2_0) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_2])])])])).

cnf(c_0_5,plain,
    ( r1_tarski(X1,k1_tarski(X2))
    | X1 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_6,plain,
    ( X1 = k1_xboole_0
    | X1 = k1_tarski(X2)
    | ~ r1_tarski(X1,k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_7,negated_conjecture,
    ( r1_tarski(esk1_0,k1_tarski(esk2_0))
    | esk1_0 = k1_xboole_0
    | esk1_0 = k1_tarski(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,plain,
    ( r1_tarski(k1_tarski(X1),k1_tarski(X1)) ),
    inference(er,[status(thm)],[c_0_5])).

cnf(c_0_9,negated_conjecture,
    ( k1_tarski(esk2_0) = esk1_0
    | esk1_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_6,c_0_7])).

cnf(c_0_10,negated_conjecture,
    ( esk1_0 != k1_tarski(esk2_0)
    | ~ r1_tarski(esk1_0,k1_tarski(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_11,negated_conjecture,
    ( esk1_0 = k1_xboole_0
    | r1_tarski(esk1_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_8,c_0_9])).

cnf(c_0_12,plain,
    ( r1_tarski(X1,k1_tarski(X2))
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_13,negated_conjecture,
    ( esk1_0 != k1_xboole_0
    | ~ r1_tarski(esk1_0,k1_tarski(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_14,negated_conjecture,
    ( esk1_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_9]),c_0_11])).

cnf(c_0_15,plain,
    ( r1_tarski(k1_xboole_0,k1_tarski(X1)) ),
    inference(er,[status(thm)],[c_0_12])).

cnf(c_0_16,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_13,c_0_14]),c_0_14]),c_0_15])]),
    [proof]).

%------------------------------------------------------------------------------
