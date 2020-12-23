%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0448+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:39:39 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   22 (  30 expanded)
%              Number of clauses        :   11 (  13 expanded)
%              Number of leaves         :    5 (   8 expanded)
%              Depth                    :    5
%              Number of atoms          :   37 (  53 expanded)
%              Number of equality atoms :   25 (  32 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t32_relat_1,conjecture,(
    ! [X1,X2] : k3_relat_1(k1_tarski(k4_tarski(X1,X2))) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_relat_1)).

fof(t23_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( X3 = k1_tarski(k4_tarski(X1,X2))
       => ( k1_relat_1(X3) = k1_tarski(X1)
          & k2_relat_1(X3) = k1_tarski(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_relat_1)).

fof(fc5_relat_1,axiom,(
    ! [X1,X2] : v1_relat_1(k1_tarski(k4_tarski(X1,X2))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_relat_1)).

fof(t41_enumset1,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

fof(d6_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k3_relat_1(X1) = k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1,X2] : k3_relat_1(k1_tarski(k4_tarski(X1,X2))) = k2_tarski(X1,X2) ),
    inference(assume_negation,[status(cth)],[t32_relat_1])).

fof(c_0_6,plain,(
    ! [X7,X8,X9] :
      ( ( k1_relat_1(X9) = k1_tarski(X7)
        | X9 != k1_tarski(k4_tarski(X7,X8))
        | ~ v1_relat_1(X9) )
      & ( k2_relat_1(X9) = k1_tarski(X8)
        | X9 != k1_tarski(k4_tarski(X7,X8))
        | ~ v1_relat_1(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_relat_1])])])).

fof(c_0_7,plain,(
    ! [X5,X6] : v1_relat_1(k1_tarski(k4_tarski(X5,X6))) ),
    inference(variable_rename,[status(thm)],[fc5_relat_1])).

fof(c_0_8,negated_conjecture,(
    k3_relat_1(k1_tarski(k4_tarski(esk1_0,esk2_0))) != k2_tarski(esk1_0,esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

fof(c_0_9,plain,(
    ! [X10,X11] : k2_tarski(X10,X11) = k2_xboole_0(k1_tarski(X10),k1_tarski(X11)) ),
    inference(variable_rename,[status(thm)],[t41_enumset1])).

fof(c_0_10,plain,(
    ! [X4] :
      ( ~ v1_relat_1(X4)
      | k3_relat_1(X4) = k2_xboole_0(k1_relat_1(X4),k2_relat_1(X4)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_relat_1])])).

cnf(c_0_11,plain,
    ( k1_relat_1(X1) = k1_tarski(X2)
    | X1 != k1_tarski(k4_tarski(X2,X3))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_12,plain,
    ( v1_relat_1(k1_tarski(k4_tarski(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,plain,
    ( k2_relat_1(X1) = k1_tarski(X2)
    | X1 != k1_tarski(k4_tarski(X3,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_14,negated_conjecture,
    ( k3_relat_1(k1_tarski(k4_tarski(esk1_0,esk2_0))) != k2_tarski(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,plain,
    ( k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,plain,
    ( k3_relat_1(X1) = k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,plain,
    ( k1_relat_1(k1_tarski(k4_tarski(X1,X2))) = k1_tarski(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_11]),c_0_12])])).

cnf(c_0_18,plain,
    ( k2_relat_1(k1_tarski(k4_tarski(X1,X2))) = k1_tarski(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_13]),c_0_12])])).

cnf(c_0_19,negated_conjecture,
    ( k3_relat_1(k1_tarski(k4_tarski(esk1_0,esk2_0))) != k2_xboole_0(k1_tarski(esk1_0),k1_tarski(esk2_0)) ),
    inference(rw,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_20,plain,
    ( k3_relat_1(k1_tarski(k4_tarski(X1,X2))) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_12]),c_0_17]),c_0_18])).

cnf(c_0_21,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_19,c_0_20])]),
    [proof]).

%------------------------------------------------------------------------------
