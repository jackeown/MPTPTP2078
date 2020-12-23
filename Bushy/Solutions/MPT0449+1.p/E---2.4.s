%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : relat_1__t33_relat_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:01 EDT 2019

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   44 ( 254 expanded)
%              Number of clauses        :   27 ( 103 expanded)
%              Number of leaves         :    8 (  67 expanded)
%              Depth                    :    8
%              Number of atoms          :   74 ( 416 expanded)
%              Number of equality atoms :   36 ( 227 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t33_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k3_relat_1(k2_xboole_0(X1,X2)) = k2_xboole_0(k3_relat_1(X1),k3_relat_1(X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t33_relat_1.p',t33_relat_1)).

fof(fc3_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X2) )
     => v1_relat_1(k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t33_relat_1.p',fc3_relat_1)).

fof(t13_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k1_relat_1(k2_xboole_0(X1,X2)) = k2_xboole_0(k1_relat_1(X1),k1_relat_1(X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t33_relat_1.p',t13_relat_1)).

fof(t26_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k2_relat_1(k2_xboole_0(X1,X2)) = k2_xboole_0(k2_relat_1(X1),k2_relat_1(X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t33_relat_1.p',t26_relat_1)).

fof(t4_xboole_1,axiom,(
    ! [X1,X2,X3] : k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t33_relat_1.p',t4_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t33_relat_1.p',commutativity_k2_xboole_0)).

fof(d6_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k3_relat_1(X1) = k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t33_relat_1.p',d6_relat_1)).

fof(idempotence_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/relat_1__t33_relat_1.p',idempotence_k2_xboole_0)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => k3_relat_1(k2_xboole_0(X1,X2)) = k2_xboole_0(k3_relat_1(X1),k3_relat_1(X2)) ) ) ),
    inference(assume_negation,[status(cth)],[t33_relat_1])).

fof(c_0_9,plain,(
    ! [X17,X18] :
      ( ~ v1_relat_1(X17)
      | ~ v1_relat_1(X18)
      | v1_relat_1(k2_xboole_0(X17,X18)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc3_relat_1])])).

fof(c_0_10,negated_conjecture,
    ( v1_relat_1(esk1_0)
    & v1_relat_1(esk2_0)
    & k3_relat_1(k2_xboole_0(esk1_0,esk2_0)) != k2_xboole_0(k3_relat_1(esk1_0),k3_relat_1(esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).

fof(c_0_11,plain,(
    ! [X10,X11] :
      ( ~ v1_relat_1(X10)
      | ~ v1_relat_1(X11)
      | k1_relat_1(k2_xboole_0(X10,X11)) = k2_xboole_0(k1_relat_1(X10),k1_relat_1(X11)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_relat_1])])])).

fof(c_0_12,plain,(
    ! [X12,X13] :
      ( ~ v1_relat_1(X12)
      | ~ v1_relat_1(X13)
      | k2_relat_1(k2_xboole_0(X12,X13)) = k2_xboole_0(k2_relat_1(X12),k2_relat_1(X13)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_relat_1])])])).

fof(c_0_13,plain,(
    ! [X14,X15,X16] : k2_xboole_0(k2_xboole_0(X14,X15),X16) = k2_xboole_0(X14,k2_xboole_0(X15,X16)) ),
    inference(variable_rename,[status(thm)],[t4_xboole_1])).

fof(c_0_14,plain,(
    ! [X6,X7] : k2_xboole_0(X6,X7) = k2_xboole_0(X7,X6) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_15,plain,
    ( v1_relat_1(k2_xboole_0(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,plain,
    ( k1_relat_1(k2_xboole_0(X1,X2)) = k2_xboole_0(k1_relat_1(X1),k1_relat_1(X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( k2_relat_1(k2_xboole_0(X1,X2)) = k2_xboole_0(k2_relat_1(X1),k2_relat_1(X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_19,plain,(
    ! [X8] :
      ( ~ v1_relat_1(X8)
      | k3_relat_1(X8) = k2_xboole_0(k1_relat_1(X8),k2_relat_1(X8)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_relat_1])])).

cnf(c_0_20,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,negated_conjecture,
    ( v1_relat_1(k2_xboole_0(X1,esk2_0))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_23,negated_conjecture,
    ( v1_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_24,negated_conjecture,
    ( k1_relat_1(k2_xboole_0(X1,esk2_0)) = k2_xboole_0(k1_relat_1(X1),k1_relat_1(esk2_0))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_17,c_0_16])).

cnf(c_0_25,negated_conjecture,
    ( k2_relat_1(k2_xboole_0(X1,esk2_0)) = k2_xboole_0(k2_relat_1(X1),k2_relat_1(esk2_0))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_16])).

cnf(c_0_26,plain,
    ( k3_relat_1(X1) = k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(X2,k2_xboole_0(X3,X1)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_28,negated_conjecture,
    ( v1_relat_1(k2_xboole_0(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_29,negated_conjecture,
    ( k1_relat_1(k2_xboole_0(esk1_0,esk2_0)) = k2_xboole_0(k1_relat_1(esk1_0),k1_relat_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_23])).

cnf(c_0_30,negated_conjecture,
    ( k2_relat_1(k2_xboole_0(esk1_0,esk2_0)) = k2_xboole_0(k2_relat_1(esk1_0),k2_relat_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_23])).

cnf(c_0_31,negated_conjecture,
    ( k2_xboole_0(k1_relat_1(esk1_0),k2_relat_1(esk1_0)) = k3_relat_1(esk1_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_23])).

cnf(c_0_32,negated_conjecture,
    ( k2_xboole_0(k1_relat_1(esk2_0),k2_relat_1(esk2_0)) = k3_relat_1(esk2_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_16])).

fof(c_0_33,plain,(
    ! [X9] : k2_xboole_0(X9,X9) = X9 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).

cnf(c_0_34,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(X3,k2_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_21])).

cnf(c_0_35,negated_conjecture,
    ( k2_xboole_0(k1_relat_1(esk1_0),k2_xboole_0(k1_relat_1(esk2_0),k2_xboole_0(k2_relat_1(esk1_0),k2_relat_1(esk2_0)))) = k3_relat_1(k2_xboole_0(esk1_0,esk2_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_28]),c_0_29]),c_0_30]),c_0_20])).

cnf(c_0_36,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(X2,k2_xboole_0(X1,X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_20])).

cnf(c_0_37,negated_conjecture,
    ( k2_xboole_0(k1_relat_1(esk1_0),k2_xboole_0(k2_relat_1(esk1_0),X1)) = k2_xboole_0(k3_relat_1(esk1_0),X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_31])).

cnf(c_0_38,negated_conjecture,
    ( k2_xboole_0(k1_relat_1(esk2_0),k2_xboole_0(k2_relat_1(esk2_0),X1)) = k2_xboole_0(k3_relat_1(esk2_0),X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_32])).

cnf(c_0_39,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_40,negated_conjecture,
    ( k2_xboole_0(k3_relat_1(esk1_0),k2_xboole_0(k3_relat_1(esk2_0),X1)) = k2_xboole_0(X1,k3_relat_1(k2_xboole_0(esk1_0,esk2_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_20]),c_0_20]),c_0_36]),c_0_36]),c_0_37]),c_0_36]),c_0_38])).

cnf(c_0_41,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_20,c_0_39])).

cnf(c_0_42,negated_conjecture,
    ( k3_relat_1(k2_xboole_0(esk1_0,esk2_0)) != k2_xboole_0(k3_relat_1(esk1_0),k3_relat_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_43,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_40]),c_0_39]),c_0_41]),c_0_42]),
    [proof]).
%------------------------------------------------------------------------------
