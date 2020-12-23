%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0012+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:31 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   18 (  36 expanded)
%              Number of clauses        :    9 (  15 expanded)
%              Number of leaves         :    4 (  10 expanded)
%              Depth                    :    6
%              Number of atoms          :   18 (  36 expanded)
%              Number of equality atoms :   17 (  35 expanded)
%              Maximal formula depth    :    5 (   2 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t5_xboole_1,conjecture,(
    ! [X1,X2,X3] : k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k2_xboole_0(X1,X3),k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',commutativity_k2_xboole_0)).

fof(t4_xboole_1,axiom,(
    ! [X1,X2,X3] : k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

fof(idempotence_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',idempotence_k2_xboole_0)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1,X2,X3] : k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k2_xboole_0(X1,X3),k2_xboole_0(X2,X3)) ),
    inference(assume_negation,[status(cth)],[t5_xboole_1])).

fof(c_0_5,negated_conjecture,(
    k2_xboole_0(k2_xboole_0(esk14_0,esk15_0),esk16_0) != k2_xboole_0(k2_xboole_0(esk14_0,esk16_0),k2_xboole_0(esk15_0,esk16_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).

fof(c_0_6,plain,(
    ! [X9,X10] : k2_xboole_0(X9,X10) = k2_xboole_0(X10,X9) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_7,negated_conjecture,
    ( k2_xboole_0(k2_xboole_0(esk14_0,esk15_0),esk16_0) != k2_xboole_0(k2_xboole_0(esk14_0,esk16_0),k2_xboole_0(esk15_0,esk16_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_8,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_9,plain,(
    ! [X108,X109,X110] : k2_xboole_0(k2_xboole_0(X108,X109),X110) = k2_xboole_0(X108,k2_xboole_0(X109,X110)) ),
    inference(variable_rename,[status(thm)],[t4_xboole_1])).

fof(c_0_10,plain,(
    ! [X58] : k2_xboole_0(X58,X58) = X58 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).

cnf(c_0_11,negated_conjecture,
    ( k2_xboole_0(k2_xboole_0(esk16_0,esk14_0),k2_xboole_0(esk16_0,esk15_0)) != k2_xboole_0(esk16_0,k2_xboole_0(esk14_0,esk15_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_7,c_0_8]),c_0_8]),c_0_8])).

cnf(c_0_12,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,negated_conjecture,
    ( k2_xboole_0(esk16_0,k2_xboole_0(esk14_0,k2_xboole_0(esk16_0,esk15_0))) != k2_xboole_0(esk16_0,k2_xboole_0(esk14_0,esk15_0)) ),
    inference(rw,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_15,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(X2,k2_xboole_0(X3,X1)) ),
    inference(spm,[status(thm)],[c_0_12,c_0_8])).

cnf(c_0_16,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_17,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_14,c_0_15]),c_0_8]),c_0_16])]),
    [proof]).
%------------------------------------------------------------------------------
