%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:52:22 EST 2020

% Result     : Theorem 11.48s
% Output     : CNFRefutation 11.48s
% Verified   : 
% Statistics : Number of formulae       :   56 (1410 expanded)
%              Number of clauses        :   37 ( 599 expanded)
%              Number of leaves         :    9 ( 360 expanded)
%              Depth                    :   11
%              Number of atoms          :   87 (2420 expanded)
%              Number of equality atoms :   49 (1185 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :   11 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t192_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,X1) = k7_relat_1(X2,k3_xboole_0(k1_relat_1(X2),X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t192_relat_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t207_relat_1,conjecture,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r1_xboole_0(X1,X2)
       => k7_relat_1(k7_relat_1(X3,X1),X2) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t207_relat_1)).

fof(t108_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => k7_relat_1(X3,k3_xboole_0(X1,X2)) = k3_xboole_0(k7_relat_1(X3,X1),k7_relat_1(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_relat_1)).

fof(t90_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k1_relat_1(k7_relat_1(X2,X1)) = k3_xboole_0(k1_relat_1(X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

fof(dt_k7_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k7_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(t110_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t110_relat_1)).

fof(c_0_9,plain,(
    ! [X19,X20] :
      ( ~ v1_relat_1(X20)
      | k7_relat_1(X20,X19) = k7_relat_1(X20,k3_xboole_0(k1_relat_1(X20),X19)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t192_relat_1])])).

fof(c_0_10,plain,(
    ! [X9,X10] : k4_xboole_0(X9,k4_xboole_0(X9,X10)) = k3_xboole_0(X9,X10) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( v1_relat_1(X3)
       => ( r1_xboole_0(X1,X2)
         => k7_relat_1(k7_relat_1(X3,X1),X2) = k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t207_relat_1])).

fof(c_0_12,plain,(
    ! [X13,X14,X15] :
      ( ~ v1_relat_1(X15)
      | k7_relat_1(X15,k3_xboole_0(X13,X14)) = k3_xboole_0(k7_relat_1(X15,X13),k7_relat_1(X15,X14)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t108_relat_1])])).

fof(c_0_13,plain,(
    ! [X21,X22] :
      ( ~ v1_relat_1(X22)
      | k1_relat_1(k7_relat_1(X22,X21)) = k3_xboole_0(k1_relat_1(X22),X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t90_relat_1])])).

cnf(c_0_14,plain,
    ( k7_relat_1(X1,X2) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_16,negated_conjecture,
    ( v1_relat_1(esk3_0)
    & r1_xboole_0(esk1_0,esk2_0)
    & k7_relat_1(k7_relat_1(esk3_0,esk1_0),esk2_0) != k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).

cnf(c_0_17,plain,
    ( k7_relat_1(X1,k3_xboole_0(X2,X3)) = k3_xboole_0(k7_relat_1(X1,X2),k7_relat_1(X1,X3))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = k3_xboole_0(k1_relat_1(X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_19,plain,(
    ! [X11,X12] :
      ( ~ v1_relat_1(X11)
      | v1_relat_1(k7_relat_1(X11,X12)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).

cnf(c_0_20,plain,
    ( k7_relat_1(X1,X2) = k7_relat_1(X1,k4_xboole_0(k1_relat_1(X1),k4_xboole_0(k1_relat_1(X1),X2)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_21,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,plain,
    ( k7_relat_1(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))) = k4_xboole_0(k7_relat_1(X1,X2),k4_xboole_0(k7_relat_1(X1,X2),k7_relat_1(X1,X3)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17,c_0_15]),c_0_15])).

cnf(c_0_23,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = k4_xboole_0(k1_relat_1(X1),k4_xboole_0(k1_relat_1(X1),X2))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_18,c_0_15])).

cnf(c_0_24,plain,
    ( v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,negated_conjecture,
    ( k7_relat_1(esk3_0,k4_xboole_0(k1_relat_1(esk3_0),k4_xboole_0(k1_relat_1(esk3_0),X1))) = k7_relat_1(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_26,negated_conjecture,
    ( k7_relat_1(esk3_0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k4_xboole_0(k7_relat_1(esk3_0,X1),k4_xboole_0(k7_relat_1(esk3_0,X1),k7_relat_1(esk3_0,X2))) ),
    inference(spm,[status(thm)],[c_0_22,c_0_21])).

cnf(c_0_27,negated_conjecture,
    ( k1_relat_1(k7_relat_1(esk3_0,X1)) = k4_xboole_0(k1_relat_1(esk3_0),k4_xboole_0(k1_relat_1(esk3_0),X1)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_21])).

fof(c_0_28,plain,(
    ! [X4,X5] : k3_xboole_0(X4,X5) = k3_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_29,negated_conjecture,
    ( v1_relat_1(k7_relat_1(esk3_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_21])])).

fof(c_0_30,plain,(
    ! [X6,X7] :
      ( ( ~ r1_xboole_0(X6,X7)
        | k3_xboole_0(X6,X7) = k1_xboole_0 )
      & ( k3_xboole_0(X6,X7) != k1_xboole_0
        | r1_xboole_0(X6,X7) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

fof(c_0_31,plain,(
    ! [X16] :
      ( ~ v1_relat_1(X16)
      | k7_relat_1(X16,k1_xboole_0) = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t110_relat_1])])).

cnf(c_0_32,negated_conjecture,
    ( v1_relat_1(k4_xboole_0(k7_relat_1(esk3_0,X1),k4_xboole_0(k7_relat_1(esk3_0,X1),k7_relat_1(esk3_0,X2)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_26]),c_0_21])])).

cnf(c_0_33,negated_conjecture,
    ( k1_relat_1(k4_xboole_0(k7_relat_1(esk3_0,X1),k4_xboole_0(k7_relat_1(esk3_0,X1),k7_relat_1(esk3_0,X2)))) = k4_xboole_0(k1_relat_1(esk3_0),k4_xboole_0(k1_relat_1(esk3_0),k4_xboole_0(X1,k4_xboole_0(X1,X2)))) ),
    inference(spm,[status(thm)],[c_0_27,c_0_26])).

cnf(c_0_34,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_35,negated_conjecture,
    ( k7_relat_1(k7_relat_1(esk3_0,X1),k4_xboole_0(k4_xboole_0(k1_relat_1(esk3_0),k4_xboole_0(k1_relat_1(esk3_0),X1)),k4_xboole_0(k4_xboole_0(k1_relat_1(esk3_0),k4_xboole_0(k1_relat_1(esk3_0),X1)),X2))) = k7_relat_1(k7_relat_1(esk3_0,X1),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_29]),c_0_27]),c_0_27])).

cnf(c_0_36,negated_conjecture,
    ( k7_relat_1(k7_relat_1(esk3_0,X1),k4_xboole_0(X2,k4_xboole_0(X2,X3))) = k4_xboole_0(k7_relat_1(k7_relat_1(esk3_0,X1),X2),k4_xboole_0(k7_relat_1(k7_relat_1(esk3_0,X1),X2),k7_relat_1(k7_relat_1(esk3_0,X1),X3))) ),
    inference(spm,[status(thm)],[c_0_22,c_0_29])).

cnf(c_0_37,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_38,plain,
    ( k7_relat_1(X1,k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_39,negated_conjecture,
    ( k7_relat_1(k4_xboole_0(k7_relat_1(esk3_0,X1),k4_xboole_0(k7_relat_1(esk3_0,X1),k7_relat_1(esk3_0,X2))),k4_xboole_0(k4_xboole_0(k1_relat_1(esk3_0),k4_xboole_0(k1_relat_1(esk3_0),k4_xboole_0(X1,k4_xboole_0(X1,X2)))),k4_xboole_0(k4_xboole_0(k1_relat_1(esk3_0),k4_xboole_0(k1_relat_1(esk3_0),k4_xboole_0(X1,k4_xboole_0(X1,X2)))),X3))) = k7_relat_1(k4_xboole_0(k7_relat_1(esk3_0,X1),k4_xboole_0(k7_relat_1(esk3_0,X1),k7_relat_1(esk3_0,X2))),X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_32]),c_0_33]),c_0_33])).

cnf(c_0_40,negated_conjecture,
    ( k7_relat_1(k4_xboole_0(k7_relat_1(esk3_0,X1),k4_xboole_0(k7_relat_1(esk3_0,X1),k7_relat_1(esk3_0,X2))),k4_xboole_0(X3,k4_xboole_0(X3,X4))) = k4_xboole_0(k7_relat_1(k4_xboole_0(k7_relat_1(esk3_0,X1),k4_xboole_0(k7_relat_1(esk3_0,X1),k7_relat_1(esk3_0,X2))),X3),k4_xboole_0(k7_relat_1(k4_xboole_0(k7_relat_1(esk3_0,X1),k4_xboole_0(k7_relat_1(esk3_0,X1),k7_relat_1(esk3_0,X2))),X3),k7_relat_1(k4_xboole_0(k7_relat_1(esk3_0,X1),k4_xboole_0(k7_relat_1(esk3_0,X1),k7_relat_1(esk3_0,X2))),X4))) ),
    inference(spm,[status(thm)],[c_0_22,c_0_32])).

cnf(c_0_41,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X2,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_15]),c_0_15])).

cnf(c_0_42,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(k7_relat_1(k7_relat_1(esk3_0,X1),k1_relat_1(esk3_0)),k4_xboole_0(k7_relat_1(k7_relat_1(esk3_0,X1),k1_relat_1(esk3_0)),k7_relat_1(k7_relat_1(esk3_0,X1),X1))),k4_xboole_0(k4_xboole_0(k7_relat_1(k7_relat_1(esk3_0,X1),k1_relat_1(esk3_0)),k4_xboole_0(k7_relat_1(k7_relat_1(esk3_0,X1),k1_relat_1(esk3_0)),k7_relat_1(k7_relat_1(esk3_0,X1),X1))),k7_relat_1(k7_relat_1(esk3_0,X1),X2))) = k7_relat_1(k7_relat_1(esk3_0,X1),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_36]),c_0_36]),c_0_36])).

cnf(c_0_43,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_37,c_0_15])).

cnf(c_0_44,negated_conjecture,
    ( r1_xboole_0(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_45,plain,
    ( k7_relat_1(k7_relat_1(X1,X2),k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_24])).

cnf(c_0_46,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(k7_relat_1(k4_xboole_0(k7_relat_1(esk3_0,X1),k4_xboole_0(k7_relat_1(esk3_0,X1),k7_relat_1(esk3_0,X2))),k1_relat_1(esk3_0)),k4_xboole_0(k7_relat_1(k4_xboole_0(k7_relat_1(esk3_0,X1),k4_xboole_0(k7_relat_1(esk3_0,X1),k7_relat_1(esk3_0,X2))),k1_relat_1(esk3_0)),k4_xboole_0(k7_relat_1(k4_xboole_0(k7_relat_1(esk3_0,X1),k4_xboole_0(k7_relat_1(esk3_0,X1),k7_relat_1(esk3_0,X2))),X1),k4_xboole_0(k7_relat_1(k4_xboole_0(k7_relat_1(esk3_0,X1),k4_xboole_0(k7_relat_1(esk3_0,X1),k7_relat_1(esk3_0,X2))),X1),k7_relat_1(k4_xboole_0(k7_relat_1(esk3_0,X1),k4_xboole_0(k7_relat_1(esk3_0,X1),k7_relat_1(esk3_0,X2))),X2))))),k4_xboole_0(k4_xboole_0(k7_relat_1(k4_xboole_0(k7_relat_1(esk3_0,X1),k4_xboole_0(k7_relat_1(esk3_0,X1),k7_relat_1(esk3_0,X2))),k1_relat_1(esk3_0)),k4_xboole_0(k7_relat_1(k4_xboole_0(k7_relat_1(esk3_0,X1),k4_xboole_0(k7_relat_1(esk3_0,X1),k7_relat_1(esk3_0,X2))),k1_relat_1(esk3_0)),k4_xboole_0(k7_relat_1(k4_xboole_0(k7_relat_1(esk3_0,X1),k4_xboole_0(k7_relat_1(esk3_0,X1),k7_relat_1(esk3_0,X2))),X1),k4_xboole_0(k7_relat_1(k4_xboole_0(k7_relat_1(esk3_0,X1),k4_xboole_0(k7_relat_1(esk3_0,X1),k7_relat_1(esk3_0,X2))),X1),k7_relat_1(k4_xboole_0(k7_relat_1(esk3_0,X1),k4_xboole_0(k7_relat_1(esk3_0,X1),k7_relat_1(esk3_0,X2))),X2))))),k7_relat_1(k4_xboole_0(k7_relat_1(esk3_0,X1),k4_xboole_0(k7_relat_1(esk3_0,X1),k7_relat_1(esk3_0,X2))),X3))) = k7_relat_1(k4_xboole_0(k7_relat_1(esk3_0,X1),k4_xboole_0(k7_relat_1(esk3_0,X1),k7_relat_1(esk3_0,X2))),X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_40]),c_0_40]),c_0_40]),c_0_40]),c_0_40])).

cnf(c_0_47,negated_conjecture,
    ( k4_xboole_0(k7_relat_1(esk3_0,k1_relat_1(esk3_0)),k4_xboole_0(k7_relat_1(esk3_0,k1_relat_1(esk3_0)),k7_relat_1(esk3_0,X1))) = k7_relat_1(esk3_0,X1) ),
    inference(rw,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_48,negated_conjecture,
    ( k4_xboole_0(k7_relat_1(k7_relat_1(esk3_0,X1),X2),k4_xboole_0(k7_relat_1(k7_relat_1(esk3_0,X1),X2),k4_xboole_0(k7_relat_1(k7_relat_1(esk3_0,X1),k1_relat_1(esk3_0)),k4_xboole_0(k7_relat_1(k7_relat_1(esk3_0,X1),k1_relat_1(esk3_0)),k7_relat_1(k7_relat_1(esk3_0,X1),X1))))) = k7_relat_1(k7_relat_1(esk3_0,X1),X2) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_49,negated_conjecture,
    ( k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk2_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_50,negated_conjecture,
    ( k7_relat_1(k7_relat_1(esk3_0,X1),k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_45,c_0_21])).

cnf(c_0_51,negated_conjecture,
    ( k4_xboole_0(k7_relat_1(k7_relat_1(esk3_0,X1),k1_relat_1(esk3_0)),k4_xboole_0(k7_relat_1(k7_relat_1(esk3_0,X1),k1_relat_1(esk3_0)),k7_relat_1(k7_relat_1(esk3_0,X1),X2))) = k7_relat_1(k7_relat_1(esk3_0,X1),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_48]),c_0_48])).

cnf(c_0_52,negated_conjecture,
    ( k4_xboole_0(k7_relat_1(k7_relat_1(esk3_0,X1),esk1_0),k4_xboole_0(k7_relat_1(k7_relat_1(esk3_0,X1),esk1_0),k7_relat_1(k7_relat_1(esk3_0,X1),esk2_0))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_49]),c_0_50])).

cnf(c_0_53,negated_conjecture,
    ( k4_xboole_0(k7_relat_1(k7_relat_1(esk3_0,X1),X1),k4_xboole_0(k7_relat_1(k7_relat_1(esk3_0,X1),X1),k7_relat_1(k7_relat_1(esk3_0,X1),X2))) = k7_relat_1(k7_relat_1(esk3_0,X1),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_51]),c_0_51])).

cnf(c_0_54,negated_conjecture,
    ( k7_relat_1(k7_relat_1(esk3_0,esk1_0),esk2_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_55,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_54]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 16:52:30 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 11.48/11.65  # AutoSched0-Mode selected heuristic G_E___208_B00_00_F1_SE_CS_SP_PS_S070I
% 11.48/11.65  # and selection function SelectVGNonCR.
% 11.48/11.65  #
% 11.48/11.65  # Preprocessing time       : 0.026 s
% 11.48/11.65  # Presaturation interreduction done
% 11.48/11.65  
% 11.48/11.65  # Proof found!
% 11.48/11.65  # SZS status Theorem
% 11.48/11.65  # SZS output start CNFRefutation
% 11.48/11.65  fof(t192_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k7_relat_1(X2,X1)=k7_relat_1(X2,k3_xboole_0(k1_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t192_relat_1)).
% 11.48/11.65  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 11.48/11.65  fof(t207_relat_1, conjecture, ![X1, X2, X3]:(v1_relat_1(X3)=>(r1_xboole_0(X1,X2)=>k7_relat_1(k7_relat_1(X3,X1),X2)=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t207_relat_1)).
% 11.48/11.65  fof(t108_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>k7_relat_1(X3,k3_xboole_0(X1,X2))=k3_xboole_0(k7_relat_1(X3,X1),k7_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t108_relat_1)).
% 11.48/11.65  fof(t90_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k1_relat_1(k7_relat_1(X2,X1))=k3_xboole_0(k1_relat_1(X2),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_relat_1)).
% 11.48/11.65  fof(dt_k7_relat_1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k7_relat_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 11.48/11.65  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 11.48/11.65  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 11.48/11.65  fof(t110_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k7_relat_1(X1,k1_xboole_0)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t110_relat_1)).
% 11.48/11.65  fof(c_0_9, plain, ![X19, X20]:(~v1_relat_1(X20)|k7_relat_1(X20,X19)=k7_relat_1(X20,k3_xboole_0(k1_relat_1(X20),X19))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t192_relat_1])])).
% 11.48/11.65  fof(c_0_10, plain, ![X9, X10]:k4_xboole_0(X9,k4_xboole_0(X9,X10))=k3_xboole_0(X9,X10), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 11.48/11.65  fof(c_0_11, negated_conjecture, ~(![X1, X2, X3]:(v1_relat_1(X3)=>(r1_xboole_0(X1,X2)=>k7_relat_1(k7_relat_1(X3,X1),X2)=k1_xboole_0))), inference(assume_negation,[status(cth)],[t207_relat_1])).
% 11.48/11.65  fof(c_0_12, plain, ![X13, X14, X15]:(~v1_relat_1(X15)|k7_relat_1(X15,k3_xboole_0(X13,X14))=k3_xboole_0(k7_relat_1(X15,X13),k7_relat_1(X15,X14))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t108_relat_1])])).
% 11.48/11.65  fof(c_0_13, plain, ![X21, X22]:(~v1_relat_1(X22)|k1_relat_1(k7_relat_1(X22,X21))=k3_xboole_0(k1_relat_1(X22),X21)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t90_relat_1])])).
% 11.48/11.65  cnf(c_0_14, plain, (k7_relat_1(X1,X2)=k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 11.48/11.65  cnf(c_0_15, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 11.48/11.65  fof(c_0_16, negated_conjecture, (v1_relat_1(esk3_0)&(r1_xboole_0(esk1_0,esk2_0)&k7_relat_1(k7_relat_1(esk3_0,esk1_0),esk2_0)!=k1_xboole_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).
% 11.48/11.65  cnf(c_0_17, plain, (k7_relat_1(X1,k3_xboole_0(X2,X3))=k3_xboole_0(k7_relat_1(X1,X2),k7_relat_1(X1,X3))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 11.48/11.65  cnf(c_0_18, plain, (k1_relat_1(k7_relat_1(X1,X2))=k3_xboole_0(k1_relat_1(X1),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 11.48/11.65  fof(c_0_19, plain, ![X11, X12]:(~v1_relat_1(X11)|v1_relat_1(k7_relat_1(X11,X12))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).
% 11.48/11.65  cnf(c_0_20, plain, (k7_relat_1(X1,X2)=k7_relat_1(X1,k4_xboole_0(k1_relat_1(X1),k4_xboole_0(k1_relat_1(X1),X2)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_14, c_0_15])).
% 11.48/11.65  cnf(c_0_21, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 11.48/11.65  cnf(c_0_22, plain, (k7_relat_1(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))=k4_xboole_0(k7_relat_1(X1,X2),k4_xboole_0(k7_relat_1(X1,X2),k7_relat_1(X1,X3)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17, c_0_15]), c_0_15])).
% 11.48/11.65  cnf(c_0_23, plain, (k1_relat_1(k7_relat_1(X1,X2))=k4_xboole_0(k1_relat_1(X1),k4_xboole_0(k1_relat_1(X1),X2))|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_18, c_0_15])).
% 11.48/11.65  cnf(c_0_24, plain, (v1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 11.48/11.65  cnf(c_0_25, negated_conjecture, (k7_relat_1(esk3_0,k4_xboole_0(k1_relat_1(esk3_0),k4_xboole_0(k1_relat_1(esk3_0),X1)))=k7_relat_1(esk3_0,X1)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 11.48/11.65  cnf(c_0_26, negated_conjecture, (k7_relat_1(esk3_0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))=k4_xboole_0(k7_relat_1(esk3_0,X1),k4_xboole_0(k7_relat_1(esk3_0,X1),k7_relat_1(esk3_0,X2)))), inference(spm,[status(thm)],[c_0_22, c_0_21])).
% 11.48/11.65  cnf(c_0_27, negated_conjecture, (k1_relat_1(k7_relat_1(esk3_0,X1))=k4_xboole_0(k1_relat_1(esk3_0),k4_xboole_0(k1_relat_1(esk3_0),X1))), inference(spm,[status(thm)],[c_0_23, c_0_21])).
% 11.48/11.65  fof(c_0_28, plain, ![X4, X5]:k3_xboole_0(X4,X5)=k3_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 11.48/11.65  cnf(c_0_29, negated_conjecture, (v1_relat_1(k7_relat_1(esk3_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_21])])).
% 11.48/11.65  fof(c_0_30, plain, ![X6, X7]:((~r1_xboole_0(X6,X7)|k3_xboole_0(X6,X7)=k1_xboole_0)&(k3_xboole_0(X6,X7)!=k1_xboole_0|r1_xboole_0(X6,X7))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 11.48/11.65  fof(c_0_31, plain, ![X16]:(~v1_relat_1(X16)|k7_relat_1(X16,k1_xboole_0)=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t110_relat_1])])).
% 11.48/11.65  cnf(c_0_32, negated_conjecture, (v1_relat_1(k4_xboole_0(k7_relat_1(esk3_0,X1),k4_xboole_0(k7_relat_1(esk3_0,X1),k7_relat_1(esk3_0,X2))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_26]), c_0_21])])).
% 11.48/11.65  cnf(c_0_33, negated_conjecture, (k1_relat_1(k4_xboole_0(k7_relat_1(esk3_0,X1),k4_xboole_0(k7_relat_1(esk3_0,X1),k7_relat_1(esk3_0,X2))))=k4_xboole_0(k1_relat_1(esk3_0),k4_xboole_0(k1_relat_1(esk3_0),k4_xboole_0(X1,k4_xboole_0(X1,X2))))), inference(spm,[status(thm)],[c_0_27, c_0_26])).
% 11.48/11.65  cnf(c_0_34, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 11.48/11.65  cnf(c_0_35, negated_conjecture, (k7_relat_1(k7_relat_1(esk3_0,X1),k4_xboole_0(k4_xboole_0(k1_relat_1(esk3_0),k4_xboole_0(k1_relat_1(esk3_0),X1)),k4_xboole_0(k4_xboole_0(k1_relat_1(esk3_0),k4_xboole_0(k1_relat_1(esk3_0),X1)),X2)))=k7_relat_1(k7_relat_1(esk3_0,X1),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_29]), c_0_27]), c_0_27])).
% 11.48/11.65  cnf(c_0_36, negated_conjecture, (k7_relat_1(k7_relat_1(esk3_0,X1),k4_xboole_0(X2,k4_xboole_0(X2,X3)))=k4_xboole_0(k7_relat_1(k7_relat_1(esk3_0,X1),X2),k4_xboole_0(k7_relat_1(k7_relat_1(esk3_0,X1),X2),k7_relat_1(k7_relat_1(esk3_0,X1),X3)))), inference(spm,[status(thm)],[c_0_22, c_0_29])).
% 11.48/11.65  cnf(c_0_37, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 11.48/11.65  cnf(c_0_38, plain, (k7_relat_1(X1,k1_xboole_0)=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 11.48/11.65  cnf(c_0_39, negated_conjecture, (k7_relat_1(k4_xboole_0(k7_relat_1(esk3_0,X1),k4_xboole_0(k7_relat_1(esk3_0,X1),k7_relat_1(esk3_0,X2))),k4_xboole_0(k4_xboole_0(k1_relat_1(esk3_0),k4_xboole_0(k1_relat_1(esk3_0),k4_xboole_0(X1,k4_xboole_0(X1,X2)))),k4_xboole_0(k4_xboole_0(k1_relat_1(esk3_0),k4_xboole_0(k1_relat_1(esk3_0),k4_xboole_0(X1,k4_xboole_0(X1,X2)))),X3)))=k7_relat_1(k4_xboole_0(k7_relat_1(esk3_0,X1),k4_xboole_0(k7_relat_1(esk3_0,X1),k7_relat_1(esk3_0,X2))),X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_32]), c_0_33]), c_0_33])).
% 11.48/11.65  cnf(c_0_40, negated_conjecture, (k7_relat_1(k4_xboole_0(k7_relat_1(esk3_0,X1),k4_xboole_0(k7_relat_1(esk3_0,X1),k7_relat_1(esk3_0,X2))),k4_xboole_0(X3,k4_xboole_0(X3,X4)))=k4_xboole_0(k7_relat_1(k4_xboole_0(k7_relat_1(esk3_0,X1),k4_xboole_0(k7_relat_1(esk3_0,X1),k7_relat_1(esk3_0,X2))),X3),k4_xboole_0(k7_relat_1(k4_xboole_0(k7_relat_1(esk3_0,X1),k4_xboole_0(k7_relat_1(esk3_0,X1),k7_relat_1(esk3_0,X2))),X3),k7_relat_1(k4_xboole_0(k7_relat_1(esk3_0,X1),k4_xboole_0(k7_relat_1(esk3_0,X1),k7_relat_1(esk3_0,X2))),X4)))), inference(spm,[status(thm)],[c_0_22, c_0_32])).
% 11.48/11.65  cnf(c_0_41, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k4_xboole_0(X2,k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_15]), c_0_15])).
% 11.48/11.65  cnf(c_0_42, negated_conjecture, (k4_xboole_0(k4_xboole_0(k7_relat_1(k7_relat_1(esk3_0,X1),k1_relat_1(esk3_0)),k4_xboole_0(k7_relat_1(k7_relat_1(esk3_0,X1),k1_relat_1(esk3_0)),k7_relat_1(k7_relat_1(esk3_0,X1),X1))),k4_xboole_0(k4_xboole_0(k7_relat_1(k7_relat_1(esk3_0,X1),k1_relat_1(esk3_0)),k4_xboole_0(k7_relat_1(k7_relat_1(esk3_0,X1),k1_relat_1(esk3_0)),k7_relat_1(k7_relat_1(esk3_0,X1),X1))),k7_relat_1(k7_relat_1(esk3_0,X1),X2)))=k7_relat_1(k7_relat_1(esk3_0,X1),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_36]), c_0_36]), c_0_36])).
% 11.48/11.65  cnf(c_0_43, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_37, c_0_15])).
% 11.48/11.65  cnf(c_0_44, negated_conjecture, (r1_xboole_0(esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 11.48/11.65  cnf(c_0_45, plain, (k7_relat_1(k7_relat_1(X1,X2),k1_xboole_0)=k1_xboole_0|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_38, c_0_24])).
% 11.48/11.65  cnf(c_0_46, negated_conjecture, (k4_xboole_0(k4_xboole_0(k7_relat_1(k4_xboole_0(k7_relat_1(esk3_0,X1),k4_xboole_0(k7_relat_1(esk3_0,X1),k7_relat_1(esk3_0,X2))),k1_relat_1(esk3_0)),k4_xboole_0(k7_relat_1(k4_xboole_0(k7_relat_1(esk3_0,X1),k4_xboole_0(k7_relat_1(esk3_0,X1),k7_relat_1(esk3_0,X2))),k1_relat_1(esk3_0)),k4_xboole_0(k7_relat_1(k4_xboole_0(k7_relat_1(esk3_0,X1),k4_xboole_0(k7_relat_1(esk3_0,X1),k7_relat_1(esk3_0,X2))),X1),k4_xboole_0(k7_relat_1(k4_xboole_0(k7_relat_1(esk3_0,X1),k4_xboole_0(k7_relat_1(esk3_0,X1),k7_relat_1(esk3_0,X2))),X1),k7_relat_1(k4_xboole_0(k7_relat_1(esk3_0,X1),k4_xboole_0(k7_relat_1(esk3_0,X1),k7_relat_1(esk3_0,X2))),X2))))),k4_xboole_0(k4_xboole_0(k7_relat_1(k4_xboole_0(k7_relat_1(esk3_0,X1),k4_xboole_0(k7_relat_1(esk3_0,X1),k7_relat_1(esk3_0,X2))),k1_relat_1(esk3_0)),k4_xboole_0(k7_relat_1(k4_xboole_0(k7_relat_1(esk3_0,X1),k4_xboole_0(k7_relat_1(esk3_0,X1),k7_relat_1(esk3_0,X2))),k1_relat_1(esk3_0)),k4_xboole_0(k7_relat_1(k4_xboole_0(k7_relat_1(esk3_0,X1),k4_xboole_0(k7_relat_1(esk3_0,X1),k7_relat_1(esk3_0,X2))),X1),k4_xboole_0(k7_relat_1(k4_xboole_0(k7_relat_1(esk3_0,X1),k4_xboole_0(k7_relat_1(esk3_0,X1),k7_relat_1(esk3_0,X2))),X1),k7_relat_1(k4_xboole_0(k7_relat_1(esk3_0,X1),k4_xboole_0(k7_relat_1(esk3_0,X1),k7_relat_1(esk3_0,X2))),X2))))),k7_relat_1(k4_xboole_0(k7_relat_1(esk3_0,X1),k4_xboole_0(k7_relat_1(esk3_0,X1),k7_relat_1(esk3_0,X2))),X3)))=k7_relat_1(k4_xboole_0(k7_relat_1(esk3_0,X1),k4_xboole_0(k7_relat_1(esk3_0,X1),k7_relat_1(esk3_0,X2))),X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39, c_0_40]), c_0_40]), c_0_40]), c_0_40]), c_0_40])).
% 11.48/11.65  cnf(c_0_47, negated_conjecture, (k4_xboole_0(k7_relat_1(esk3_0,k1_relat_1(esk3_0)),k4_xboole_0(k7_relat_1(esk3_0,k1_relat_1(esk3_0)),k7_relat_1(esk3_0,X1)))=k7_relat_1(esk3_0,X1)), inference(rw,[status(thm)],[c_0_25, c_0_26])).
% 11.48/11.65  cnf(c_0_48, negated_conjecture, (k4_xboole_0(k7_relat_1(k7_relat_1(esk3_0,X1),X2),k4_xboole_0(k7_relat_1(k7_relat_1(esk3_0,X1),X2),k4_xboole_0(k7_relat_1(k7_relat_1(esk3_0,X1),k1_relat_1(esk3_0)),k4_xboole_0(k7_relat_1(k7_relat_1(esk3_0,X1),k1_relat_1(esk3_0)),k7_relat_1(k7_relat_1(esk3_0,X1),X1)))))=k7_relat_1(k7_relat_1(esk3_0,X1),X2)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 11.48/11.65  cnf(c_0_49, negated_conjecture, (k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk2_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 11.48/11.65  cnf(c_0_50, negated_conjecture, (k7_relat_1(k7_relat_1(esk3_0,X1),k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_45, c_0_21])).
% 11.48/11.65  cnf(c_0_51, negated_conjecture, (k4_xboole_0(k7_relat_1(k7_relat_1(esk3_0,X1),k1_relat_1(esk3_0)),k4_xboole_0(k7_relat_1(k7_relat_1(esk3_0,X1),k1_relat_1(esk3_0)),k7_relat_1(k7_relat_1(esk3_0,X1),X2)))=k7_relat_1(k7_relat_1(esk3_0,X1),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_48]), c_0_48])).
% 11.48/11.65  cnf(c_0_52, negated_conjecture, (k4_xboole_0(k7_relat_1(k7_relat_1(esk3_0,X1),esk1_0),k4_xboole_0(k7_relat_1(k7_relat_1(esk3_0,X1),esk1_0),k7_relat_1(k7_relat_1(esk3_0,X1),esk2_0)))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_49]), c_0_50])).
% 11.48/11.65  cnf(c_0_53, negated_conjecture, (k4_xboole_0(k7_relat_1(k7_relat_1(esk3_0,X1),X1),k4_xboole_0(k7_relat_1(k7_relat_1(esk3_0,X1),X1),k7_relat_1(k7_relat_1(esk3_0,X1),X2)))=k7_relat_1(k7_relat_1(esk3_0,X1),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42, c_0_51]), c_0_51])).
% 11.48/11.65  cnf(c_0_54, negated_conjecture, (k7_relat_1(k7_relat_1(esk3_0,esk1_0),esk2_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_16])).
% 11.48/11.65  cnf(c_0_55, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_54]), ['proof']).
% 11.48/11.65  # SZS output end CNFRefutation
% 11.48/11.65  # Proof object total steps             : 56
% 11.48/11.65  # Proof object clause steps            : 37
% 11.48/11.65  # Proof object formula steps           : 19
% 11.48/11.65  # Proof object conjectures             : 26
% 11.48/11.65  # Proof object clause conjectures      : 23
% 11.48/11.65  # Proof object formula conjectures     : 3
% 11.48/11.65  # Proof object initial clauses used    : 11
% 11.48/11.65  # Proof object initial formulas used   : 9
% 11.48/11.65  # Proof object generating inferences   : 17
% 11.48/11.65  # Proof object simplifying inferences  : 30
% 11.48/11.65  # Training examples: 0 positive, 0 negative
% 11.48/11.65  # Parsed axioms                        : 12
% 11.48/11.65  # Removed by relevancy pruning/SinE    : 0
% 11.48/11.65  # Initial clauses                      : 16
% 11.48/11.65  # Removed in clause preprocessing      : 1
% 11.48/11.65  # Initial clauses in saturation        : 15
% 11.48/11.65  # Processed clauses                    : 12348
% 11.48/11.65  # ...of these trivial                  : 203
% 11.48/11.65  # ...subsumed                          : 10537
% 11.48/11.65  # ...remaining for further processing  : 1608
% 11.48/11.65  # Other redundant clauses eliminated   : 0
% 11.48/11.65  # Clauses deleted for lack of memory   : 0
% 11.48/11.65  # Backward-subsumed                    : 53
% 11.48/11.65  # Backward-rewritten                   : 106
% 11.48/11.65  # Generated clauses                    : 676326
% 11.48/11.65  # ...of the previous two non-trivial   : 273529
% 11.48/11.65  # Contextual simplify-reflections      : 1
% 11.48/11.65  # Paramodulations                      : 676326
% 11.48/11.65  # Factorizations                       : 0
% 11.48/11.65  # Equation resolutions                 : 0
% 11.48/11.65  # Propositional unsat checks           : 0
% 11.48/11.65  #    Propositional check models        : 0
% 11.48/11.65  #    Propositional check unsatisfiable : 0
% 11.48/11.65  #    Propositional clauses             : 0
% 11.48/11.65  #    Propositional clauses after purity: 0
% 11.48/11.65  #    Propositional unsat core size     : 0
% 11.48/11.65  #    Propositional preprocessing time  : 0.000
% 11.48/11.65  #    Propositional encoding time       : 0.000
% 11.48/11.65  #    Propositional solver time         : 0.000
% 11.48/11.65  #    Success case prop preproc time    : 0.000
% 11.48/11.65  #    Success case prop encoding time   : 0.000
% 11.48/11.65  #    Success case prop solver time     : 0.000
% 11.48/11.65  # Current number of processed clauses  : 1434
% 11.48/11.65  #    Positive orientable unit clauses  : 349
% 11.48/11.65  #    Positive unorientable unit clauses: 12
% 11.48/11.65  #    Negative unit clauses             : 3
% 11.48/11.65  #    Non-unit-clauses                  : 1070
% 11.48/11.65  # Current number of unprocessed clauses: 260645
% 11.48/11.65  # ...number of literals in the above   : 512282
% 11.48/11.65  # Current number of archived formulas  : 0
% 11.48/11.65  # Current number of archived clauses   : 175
% 11.48/11.65  # Clause-clause subsumption calls (NU) : 120505
% 11.48/11.65  # Rec. Clause-clause subsumption calls : 111372
% 11.48/11.65  # Non-unit clause-clause subsumptions  : 10573
% 11.48/11.65  # Unit Clause-clause subsumption calls : 1370
% 11.48/11.65  # Rewrite failures with RHS unbound    : 0
% 11.48/11.65  # BW rewrite match attempts            : 6530
% 11.48/11.65  # BW rewrite match successes           : 130
% 11.48/11.65  # Condensation attempts                : 0
% 11.48/11.65  # Condensation successes               : 0
% 11.48/11.65  # Termbank termtop insertions          : 132126583
% 11.49/11.67  
% 11.49/11.67  # -------------------------------------------------
% 11.49/11.67  # User time                : 11.170 s
% 11.49/11.67  # System time              : 0.162 s
% 11.49/11.67  # Total time               : 11.333 s
% 11.49/11.67  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
