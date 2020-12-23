%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0022+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:32 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   12 (  15 expanded)
%              Number of clauses        :    5 (   5 expanded)
%              Number of leaves         :    3 (   4 expanded)
%              Depth                    :    4
%              Number of atoms          :   15 (  21 expanded)
%              Number of equality atoms :   14 (  20 expanded)
%              Maximal formula depth    :    5 (   2 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t15_xboole_1,conjecture,(
    ! [X1,X2] :
      ( k2_xboole_0(X1,X2) = k1_xboole_0
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_xboole_1)).

fof(t6_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_1)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1,X2] :
        ( k2_xboole_0(X1,X2) = k1_xboole_0
       => X1 = k1_xboole_0 ) ),
    inference(assume_negation,[status(cth)],[t15_xboole_1])).

fof(c_0_4,plain,(
    ! [X133,X134] : k2_xboole_0(X133,k2_xboole_0(X133,X134)) = k2_xboole_0(X133,X134) ),
    inference(variable_rename,[status(thm)],[t6_xboole_1])).

fof(c_0_5,negated_conjecture,
    ( k2_xboole_0(esk15_0,esk16_0) = k1_xboole_0
    & esk15_0 != k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])).

fof(c_0_6,plain,(
    ! [X120] : k2_xboole_0(X120,k1_xboole_0) = X120 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

cnf(c_0_7,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,negated_conjecture,
    ( k2_xboole_0(esk15_0,esk16_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,negated_conjecture,
    ( esk15_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_11,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7,c_0_8]),c_0_9]),c_0_10]),
    [proof]).
%------------------------------------------------------------------------------
