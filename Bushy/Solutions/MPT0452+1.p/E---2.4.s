%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : relat_1__t38_relat_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:02 EDT 2019

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   24 (  44 expanded)
%              Number of clauses        :   13 (  17 expanded)
%              Number of leaves         :    5 (  11 expanded)
%              Depth                    :    6
%              Number of atoms          :   40 (  80 expanded)
%              Number of equality atoms :   20 (  39 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t38_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k3_relat_1(X1) = k3_relat_1(k4_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t38_relat_1.p',t38_relat_1)).

fof(d6_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k3_relat_1(X1) = k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t38_relat_1.p',d6_relat_1)).

fof(dt_k4_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k4_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t38_relat_1.p',dt_k4_relat_1)).

fof(t37_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( k2_relat_1(X1) = k1_relat_1(k4_relat_1(X1))
        & k1_relat_1(X1) = k2_relat_1(k4_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t38_relat_1.p',t37_relat_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t38_relat_1.p',commutativity_k2_xboole_0)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => k3_relat_1(X1) = k3_relat_1(k4_relat_1(X1)) ) ),
    inference(assume_negation,[status(cth)],[t38_relat_1])).

fof(c_0_6,plain,(
    ! [X6] :
      ( ~ v1_relat_1(X6)
      | k3_relat_1(X6) = k2_xboole_0(k1_relat_1(X6),k2_relat_1(X6)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_relat_1])])).

fof(c_0_7,negated_conjecture,
    ( v1_relat_1(esk1_0)
    & k3_relat_1(esk1_0) != k3_relat_1(k4_relat_1(esk1_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

fof(c_0_8,plain,(
    ! [X7] :
      ( ~ v1_relat_1(X7)
      | v1_relat_1(k4_relat_1(X7)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_relat_1])])).

fof(c_0_9,plain,(
    ! [X10] :
      ( ( k2_relat_1(X10) = k1_relat_1(k4_relat_1(X10))
        | ~ v1_relat_1(X10) )
      & ( k1_relat_1(X10) = k2_relat_1(k4_relat_1(X10))
        | ~ v1_relat_1(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_relat_1])])])).

cnf(c_0_10,plain,
    ( k3_relat_1(X1) = k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,negated_conjecture,
    ( v1_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( v1_relat_1(k4_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( k2_relat_1(X1) = k1_relat_1(k4_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( k1_relat_1(X1) = k2_relat_1(k4_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_15,plain,(
    ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_16,negated_conjecture,
    ( k3_relat_1(esk1_0) != k3_relat_1(k4_relat_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_17,negated_conjecture,
    ( k3_relat_1(esk1_0) = k2_xboole_0(k1_relat_1(esk1_0),k2_relat_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_18,negated_conjecture,
    ( v1_relat_1(k4_relat_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_12,c_0_11])).

cnf(c_0_19,negated_conjecture,
    ( k1_relat_1(k4_relat_1(esk1_0)) = k2_relat_1(esk1_0) ),
    inference(spm,[status(thm)],[c_0_13,c_0_11])).

cnf(c_0_20,negated_conjecture,
    ( k2_relat_1(k4_relat_1(esk1_0)) = k1_relat_1(esk1_0) ),
    inference(spm,[status(thm)],[c_0_14,c_0_11])).

cnf(c_0_21,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,negated_conjecture,
    ( k3_relat_1(k4_relat_1(esk1_0)) != k2_xboole_0(k1_relat_1(esk1_0),k2_relat_1(esk1_0)) ),
    inference(rw,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_23,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_18]),c_0_19]),c_0_20]),c_0_21]),c_0_22]),
    [proof]).
%------------------------------------------------------------------------------
