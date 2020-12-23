%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:51:09 EST 2020

% Result     : Theorem 1.16s
% Output     : CNFRefutation 1.16s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 130 expanded)
%              Number of clauses        :   36 (  55 expanded)
%              Number of leaves         :   17 (  35 expanded)
%              Depth                    :   10
%              Number of atoms          :  144 ( 233 expanded)
%              Number of equality atoms :   42 (  68 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t163_relat_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k3_xboole_0(k1_relat_1(X2),X1),k9_relat_1(k4_relat_1(X2),k9_relat_1(X2,X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t163_relat_1)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(t90_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k1_relat_1(k7_relat_1(X2,X1)) = k3_xboole_0(k1_relat_1(X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

fof(t25_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => ( r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
              & r1_tarski(k2_relat_1(X1),k2_relat_1(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

fof(t37_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( k2_relat_1(X1) = k1_relat_1(k4_relat_1(X1))
        & k1_relat_1(X1) = k2_relat_1(k4_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).

fof(dt_k4_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k4_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relat_1)).

fof(t80_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k5_relat_1(X1,k6_relat_1(k2_relat_1(X1))) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

fof(t148_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k2_relat_1(k7_relat_1(X2,X1)) = k9_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(dt_k7_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k7_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(t54_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k4_relat_1(k5_relat_1(X1,X2)) = k5_relat_1(k4_relat_1(X2),k4_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_relat_1)).

fof(involutiveness_k4_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k4_relat_1(k4_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).

fof(t92_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => r1_tarski(k5_relat_1(k7_relat_1(X2,X1),X3),k5_relat_1(X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_relat_1)).

fof(dt_k6_relat_1,axiom,(
    ! [X1] : v1_relat_1(k6_relat_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(t94_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,X1) = k5_relat_1(k6_relat_1(X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(t72_relat_1,axiom,(
    ! [X1] : k4_relat_1(k6_relat_1(X1)) = k6_relat_1(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_relat_1)).

fof(c_0_17,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => r1_tarski(k3_xboole_0(k1_relat_1(X2),X1),k9_relat_1(k4_relat_1(X2),k9_relat_1(X2,X1))) ) ),
    inference(assume_negation,[status(cth)],[t163_relat_1])).

fof(c_0_18,plain,(
    ! [X8,X9] : k1_setfam_1(k2_tarski(X8,X9)) = k3_xboole_0(X8,X9) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_19,plain,(
    ! [X6,X7] : k1_enumset1(X6,X6,X7) = k2_tarski(X6,X7) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_20,negated_conjecture,
    ( v1_relat_1(esk2_0)
    & ~ r1_tarski(k3_xboole_0(k1_relat_1(esk2_0),esk1_0),k9_relat_1(k4_relat_1(esk2_0),k9_relat_1(esk2_0,esk1_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).

cnf(c_0_21,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_22,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_23,plain,(
    ! [X4,X5] : k2_tarski(X4,X5) = k2_tarski(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

fof(c_0_24,plain,(
    ! [X24,X25] :
      ( ~ v1_relat_1(X25)
      | k1_relat_1(k7_relat_1(X25,X24)) = k3_xboole_0(k1_relat_1(X25),X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t90_relat_1])])).

cnf(c_0_25,negated_conjecture,
    ( ~ r1_tarski(k3_xboole_0(k1_relat_1(esk2_0),esk1_0),k9_relat_1(k4_relat_1(esk2_0),k9_relat_1(esk2_0,esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_27,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_28,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = k3_xboole_0(k1_relat_1(X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_29,plain,(
    ! [X17,X18] :
      ( ( r1_tarski(k1_relat_1(X17),k1_relat_1(X18))
        | ~ r1_tarski(X17,X18)
        | ~ v1_relat_1(X18)
        | ~ v1_relat_1(X17) )
      & ( r1_tarski(k2_relat_1(X17),k2_relat_1(X18))
        | ~ r1_tarski(X17,X18)
        | ~ v1_relat_1(X18)
        | ~ v1_relat_1(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_relat_1])])])])).

fof(c_0_30,plain,(
    ! [X19] :
      ( ( k2_relat_1(X19) = k1_relat_1(k4_relat_1(X19))
        | ~ v1_relat_1(X19) )
      & ( k1_relat_1(X19) = k2_relat_1(k4_relat_1(X19))
        | ~ v1_relat_1(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_relat_1])])])).

fof(c_0_31,plain,(
    ! [X10] :
      ( ~ v1_relat_1(X10)
      | v1_relat_1(k4_relat_1(X10)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_relat_1])])).

fof(c_0_32,plain,(
    ! [X23] :
      ( ~ v1_relat_1(X23)
      | k5_relat_1(X23,k6_relat_1(k2_relat_1(X23))) = X23 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t80_relat_1])])).

fof(c_0_33,plain,(
    ! [X15,X16] :
      ( ~ v1_relat_1(X16)
      | k2_relat_1(k7_relat_1(X16,X15)) = k9_relat_1(X16,X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).

fof(c_0_34,plain,(
    ! [X12,X13] :
      ( ~ v1_relat_1(X12)
      | v1_relat_1(k7_relat_1(X12,X13)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).

fof(c_0_35,plain,(
    ! [X20,X21] :
      ( ~ v1_relat_1(X20)
      | ~ v1_relat_1(X21)
      | k4_relat_1(k5_relat_1(X20,X21)) = k5_relat_1(k4_relat_1(X21),k4_relat_1(X20)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t54_relat_1])])])).

fof(c_0_36,plain,(
    ! [X14] :
      ( ~ v1_relat_1(X14)
      | k4_relat_1(k4_relat_1(X14)) = X14 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k4_relat_1])])).

cnf(c_0_37,negated_conjecture,
    ( ~ r1_tarski(k1_setfam_1(k1_enumset1(k1_relat_1(esk2_0),k1_relat_1(esk2_0),esk1_0)),k9_relat_1(k4_relat_1(esk2_0),k9_relat_1(esk2_0,esk1_0))) ),
    inference(rw,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_38,plain,
    ( k1_enumset1(X1,X1,X2) = k1_enumset1(X2,X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_22]),c_0_22])).

cnf(c_0_39,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = k1_setfam_1(k1_enumset1(k1_relat_1(X1),k1_relat_1(X1),X2))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_28,c_0_26])).

cnf(c_0_40,plain,
    ( r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
    | ~ r1_tarski(X1,X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_41,plain,
    ( k2_relat_1(X1) = k1_relat_1(k4_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_42,plain,
    ( v1_relat_1(k4_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_43,plain,(
    ! [X26,X27,X28] :
      ( ~ v1_relat_1(X27)
      | ~ v1_relat_1(X28)
      | r1_tarski(k5_relat_1(k7_relat_1(X27,X26),X28),k5_relat_1(X27,X28)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t92_relat_1])])])).

cnf(c_0_44,plain,
    ( k5_relat_1(X1,k6_relat_1(k2_relat_1(X1))) = X1
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_45,plain,
    ( k2_relat_1(k7_relat_1(X1,X2)) = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_46,plain,
    ( v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

fof(c_0_47,plain,(
    ! [X11] : v1_relat_1(k6_relat_1(X11)) ),
    inference(variable_rename,[status(thm)],[dt_k6_relat_1])).

cnf(c_0_48,plain,
    ( k4_relat_1(k5_relat_1(X1,X2)) = k5_relat_1(k4_relat_1(X2),k4_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_49,plain,
    ( k4_relat_1(k4_relat_1(X1)) = X1
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

fof(c_0_50,plain,(
    ! [X29,X30] :
      ( ~ v1_relat_1(X30)
      | k7_relat_1(X30,X29) = k5_relat_1(k6_relat_1(X29),X30) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).

fof(c_0_51,plain,(
    ! [X22] : k4_relat_1(k6_relat_1(X22)) = k6_relat_1(X22) ),
    inference(variable_rename,[status(thm)],[t72_relat_1])).

cnf(c_0_52,negated_conjecture,
    ( ~ r1_tarski(k1_setfam_1(k1_enumset1(esk1_0,esk1_0,k1_relat_1(esk2_0))),k9_relat_1(k4_relat_1(esk2_0),k9_relat_1(esk2_0,esk1_0))) ),
    inference(rw,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_53,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,k1_relat_1(X2))) = k1_relat_1(k7_relat_1(X2,X1))
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_39,c_0_38])).

cnf(c_0_54,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_55,plain,
    ( r1_tarski(k1_relat_1(X1),k2_relat_1(X2))
    | ~ r1_tarski(X1,k4_relat_1(X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42])).

cnf(c_0_56,plain,
    ( r1_tarski(k5_relat_1(k7_relat_1(X1,X3),X2),k5_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_57,plain,
    ( k5_relat_1(k7_relat_1(X1,X2),k6_relat_1(k9_relat_1(X1,X2))) = k7_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_46])).

cnf(c_0_58,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_59,plain,
    ( k4_relat_1(k5_relat_1(X1,k4_relat_1(X2))) = k5_relat_1(X2,k4_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_42])).

cnf(c_0_60,plain,
    ( k7_relat_1(X1,X2) = k5_relat_1(k6_relat_1(X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_61,plain,
    ( k4_relat_1(k6_relat_1(X1)) = k6_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_62,negated_conjecture,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1(esk2_0,esk1_0)),k9_relat_1(k4_relat_1(esk2_0),k9_relat_1(esk2_0,esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_54])])).

cnf(c_0_63,plain,
    ( r1_tarski(k1_relat_1(X1),k9_relat_1(X2,X3))
    | ~ r1_tarski(X1,k4_relat_1(k7_relat_1(X2,X3)))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_45]),c_0_46])).

cnf(c_0_64,plain,
    ( r1_tarski(k7_relat_1(X1,X2),k5_relat_1(X1,k6_relat_1(k9_relat_1(X1,X2))))
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_58])])).

cnf(c_0_65,plain,
    ( k5_relat_1(X1,k6_relat_1(X2)) = k4_relat_1(k7_relat_1(k4_relat_1(X1),X2))
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_61]),c_0_58])]),c_0_42])).

cnf(c_0_66,negated_conjecture,
    ( ~ r1_tarski(k7_relat_1(esk2_0,esk1_0),k4_relat_1(k7_relat_1(k4_relat_1(esk2_0),k9_relat_1(esk2_0,esk1_0))))
    | ~ v1_relat_1(k7_relat_1(esk2_0,esk1_0))
    | ~ v1_relat_1(k4_relat_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_67,plain,
    ( r1_tarski(k7_relat_1(X1,X2),k4_relat_1(k7_relat_1(k4_relat_1(X1),k9_relat_1(X1,X2))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_68,negated_conjecture,
    ( ~ v1_relat_1(k7_relat_1(esk2_0,esk1_0))
    | ~ v1_relat_1(k4_relat_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_54])])).

cnf(c_0_69,negated_conjecture,
    ( ~ v1_relat_1(k4_relat_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_46]),c_0_54])])).

cnf(c_0_70,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_42]),c_0_54])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:14:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 1.16/1.32  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 1.16/1.32  # and selection function SelectComplexExceptUniqMaxHorn.
% 1.16/1.32  #
% 1.16/1.32  # Preprocessing time       : 0.027 s
% 1.16/1.32  # Presaturation interreduction done
% 1.16/1.32  
% 1.16/1.32  # Proof found!
% 1.16/1.32  # SZS status Theorem
% 1.16/1.32  # SZS output start CNFRefutation
% 1.16/1.32  fof(t163_relat_1, conjecture, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k3_xboole_0(k1_relat_1(X2),X1),k9_relat_1(k4_relat_1(X2),k9_relat_1(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t163_relat_1)).
% 1.16/1.32  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 1.16/1.32  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 1.16/1.32  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 1.16/1.32  fof(t90_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k1_relat_1(k7_relat_1(X2,X1))=k3_xboole_0(k1_relat_1(X2),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_relat_1)).
% 1.16/1.32  fof(t25_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_tarski(X1,X2)=>(r1_tarski(k1_relat_1(X1),k1_relat_1(X2))&r1_tarski(k2_relat_1(X1),k2_relat_1(X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_relat_1)).
% 1.16/1.32  fof(t37_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>(k2_relat_1(X1)=k1_relat_1(k4_relat_1(X1))&k1_relat_1(X1)=k2_relat_1(k4_relat_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_relat_1)).
% 1.16/1.32  fof(dt_k4_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>v1_relat_1(k4_relat_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 1.16/1.32  fof(t80_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k5_relat_1(X1,k6_relat_1(k2_relat_1(X1)))=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_relat_1)).
% 1.16/1.32  fof(t148_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k2_relat_1(k7_relat_1(X2,X1))=k9_relat_1(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 1.16/1.32  fof(dt_k7_relat_1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k7_relat_1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 1.16/1.32  fof(t54_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>k4_relat_1(k5_relat_1(X1,X2))=k5_relat_1(k4_relat_1(X2),k4_relat_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t54_relat_1)).
% 1.16/1.32  fof(involutiveness_k4_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k4_relat_1(k4_relat_1(X1))=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k4_relat_1)).
% 1.16/1.32  fof(t92_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>r1_tarski(k5_relat_1(k7_relat_1(X2,X1),X3),k5_relat_1(X2,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_relat_1)).
% 1.16/1.32  fof(dt_k6_relat_1, axiom, ![X1]:v1_relat_1(k6_relat_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 1.16/1.32  fof(t94_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k7_relat_1(X2,X1)=k5_relat_1(k6_relat_1(X1),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 1.16/1.32  fof(t72_relat_1, axiom, ![X1]:k4_relat_1(k6_relat_1(X1))=k6_relat_1(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_relat_1)).
% 1.16/1.32  fof(c_0_17, negated_conjecture, ~(![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k3_xboole_0(k1_relat_1(X2),X1),k9_relat_1(k4_relat_1(X2),k9_relat_1(X2,X1))))), inference(assume_negation,[status(cth)],[t163_relat_1])).
% 1.16/1.32  fof(c_0_18, plain, ![X8, X9]:k1_setfam_1(k2_tarski(X8,X9))=k3_xboole_0(X8,X9), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 1.16/1.32  fof(c_0_19, plain, ![X6, X7]:k1_enumset1(X6,X6,X7)=k2_tarski(X6,X7), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 1.16/1.32  fof(c_0_20, negated_conjecture, (v1_relat_1(esk2_0)&~r1_tarski(k3_xboole_0(k1_relat_1(esk2_0),esk1_0),k9_relat_1(k4_relat_1(esk2_0),k9_relat_1(esk2_0,esk1_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).
% 1.16/1.32  cnf(c_0_21, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 1.16/1.32  cnf(c_0_22, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 1.16/1.32  fof(c_0_23, plain, ![X4, X5]:k2_tarski(X4,X5)=k2_tarski(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 1.16/1.32  fof(c_0_24, plain, ![X24, X25]:(~v1_relat_1(X25)|k1_relat_1(k7_relat_1(X25,X24))=k3_xboole_0(k1_relat_1(X25),X24)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t90_relat_1])])).
% 1.16/1.32  cnf(c_0_25, negated_conjecture, (~r1_tarski(k3_xboole_0(k1_relat_1(esk2_0),esk1_0),k9_relat_1(k4_relat_1(esk2_0),k9_relat_1(esk2_0,esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 1.16/1.32  cnf(c_0_26, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_21, c_0_22])).
% 1.16/1.32  cnf(c_0_27, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 1.16/1.32  cnf(c_0_28, plain, (k1_relat_1(k7_relat_1(X1,X2))=k3_xboole_0(k1_relat_1(X1),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 1.16/1.32  fof(c_0_29, plain, ![X17, X18]:((r1_tarski(k1_relat_1(X17),k1_relat_1(X18))|~r1_tarski(X17,X18)|~v1_relat_1(X18)|~v1_relat_1(X17))&(r1_tarski(k2_relat_1(X17),k2_relat_1(X18))|~r1_tarski(X17,X18)|~v1_relat_1(X18)|~v1_relat_1(X17))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_relat_1])])])])).
% 1.16/1.32  fof(c_0_30, plain, ![X19]:((k2_relat_1(X19)=k1_relat_1(k4_relat_1(X19))|~v1_relat_1(X19))&(k1_relat_1(X19)=k2_relat_1(k4_relat_1(X19))|~v1_relat_1(X19))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_relat_1])])])).
% 1.16/1.32  fof(c_0_31, plain, ![X10]:(~v1_relat_1(X10)|v1_relat_1(k4_relat_1(X10))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_relat_1])])).
% 1.16/1.32  fof(c_0_32, plain, ![X23]:(~v1_relat_1(X23)|k5_relat_1(X23,k6_relat_1(k2_relat_1(X23)))=X23), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t80_relat_1])])).
% 1.16/1.32  fof(c_0_33, plain, ![X15, X16]:(~v1_relat_1(X16)|k2_relat_1(k7_relat_1(X16,X15))=k9_relat_1(X16,X15)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).
% 1.16/1.32  fof(c_0_34, plain, ![X12, X13]:(~v1_relat_1(X12)|v1_relat_1(k7_relat_1(X12,X13))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).
% 1.16/1.32  fof(c_0_35, plain, ![X20, X21]:(~v1_relat_1(X20)|(~v1_relat_1(X21)|k4_relat_1(k5_relat_1(X20,X21))=k5_relat_1(k4_relat_1(X21),k4_relat_1(X20)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t54_relat_1])])])).
% 1.16/1.32  fof(c_0_36, plain, ![X14]:(~v1_relat_1(X14)|k4_relat_1(k4_relat_1(X14))=X14), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k4_relat_1])])).
% 1.16/1.32  cnf(c_0_37, negated_conjecture, (~r1_tarski(k1_setfam_1(k1_enumset1(k1_relat_1(esk2_0),k1_relat_1(esk2_0),esk1_0)),k9_relat_1(k4_relat_1(esk2_0),k9_relat_1(esk2_0,esk1_0)))), inference(rw,[status(thm)],[c_0_25, c_0_26])).
% 1.16/1.32  cnf(c_0_38, plain, (k1_enumset1(X1,X1,X2)=k1_enumset1(X2,X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27, c_0_22]), c_0_22])).
% 1.16/1.32  cnf(c_0_39, plain, (k1_relat_1(k7_relat_1(X1,X2))=k1_setfam_1(k1_enumset1(k1_relat_1(X1),k1_relat_1(X1),X2))|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_28, c_0_26])).
% 1.16/1.32  cnf(c_0_40, plain, (r1_tarski(k1_relat_1(X1),k1_relat_1(X2))|~r1_tarski(X1,X2)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 1.16/1.32  cnf(c_0_41, plain, (k2_relat_1(X1)=k1_relat_1(k4_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 1.16/1.32  cnf(c_0_42, plain, (v1_relat_1(k4_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 1.16/1.32  fof(c_0_43, plain, ![X26, X27, X28]:(~v1_relat_1(X27)|(~v1_relat_1(X28)|r1_tarski(k5_relat_1(k7_relat_1(X27,X26),X28),k5_relat_1(X27,X28)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t92_relat_1])])])).
% 1.16/1.32  cnf(c_0_44, plain, (k5_relat_1(X1,k6_relat_1(k2_relat_1(X1)))=X1|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 1.16/1.32  cnf(c_0_45, plain, (k2_relat_1(k7_relat_1(X1,X2))=k9_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 1.16/1.32  cnf(c_0_46, plain, (v1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 1.16/1.32  fof(c_0_47, plain, ![X11]:v1_relat_1(k6_relat_1(X11)), inference(variable_rename,[status(thm)],[dt_k6_relat_1])).
% 1.16/1.32  cnf(c_0_48, plain, (k4_relat_1(k5_relat_1(X1,X2))=k5_relat_1(k4_relat_1(X2),k4_relat_1(X1))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 1.16/1.32  cnf(c_0_49, plain, (k4_relat_1(k4_relat_1(X1))=X1|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 1.16/1.32  fof(c_0_50, plain, ![X29, X30]:(~v1_relat_1(X30)|k7_relat_1(X30,X29)=k5_relat_1(k6_relat_1(X29),X30)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).
% 1.16/1.32  fof(c_0_51, plain, ![X22]:k4_relat_1(k6_relat_1(X22))=k6_relat_1(X22), inference(variable_rename,[status(thm)],[t72_relat_1])).
% 1.16/1.32  cnf(c_0_52, negated_conjecture, (~r1_tarski(k1_setfam_1(k1_enumset1(esk1_0,esk1_0,k1_relat_1(esk2_0))),k9_relat_1(k4_relat_1(esk2_0),k9_relat_1(esk2_0,esk1_0)))), inference(rw,[status(thm)],[c_0_37, c_0_38])).
% 1.16/1.32  cnf(c_0_53, plain, (k1_setfam_1(k1_enumset1(X1,X1,k1_relat_1(X2)))=k1_relat_1(k7_relat_1(X2,X1))|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_39, c_0_38])).
% 1.16/1.32  cnf(c_0_54, negated_conjecture, (v1_relat_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 1.16/1.32  cnf(c_0_55, plain, (r1_tarski(k1_relat_1(X1),k2_relat_1(X2))|~r1_tarski(X1,k4_relat_1(X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_42])).
% 1.16/1.32  cnf(c_0_56, plain, (r1_tarski(k5_relat_1(k7_relat_1(X1,X3),X2),k5_relat_1(X1,X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 1.16/1.32  cnf(c_0_57, plain, (k5_relat_1(k7_relat_1(X1,X2),k6_relat_1(k9_relat_1(X1,X2)))=k7_relat_1(X1,X2)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_46])).
% 1.16/1.32  cnf(c_0_58, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_47])).
% 1.16/1.32  cnf(c_0_59, plain, (k4_relat_1(k5_relat_1(X1,k4_relat_1(X2)))=k5_relat_1(X2,k4_relat_1(X1))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_42])).
% 1.16/1.32  cnf(c_0_60, plain, (k7_relat_1(X1,X2)=k5_relat_1(k6_relat_1(X2),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 1.16/1.32  cnf(c_0_61, plain, (k4_relat_1(k6_relat_1(X1))=k6_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 1.16/1.32  cnf(c_0_62, negated_conjecture, (~r1_tarski(k1_relat_1(k7_relat_1(esk2_0,esk1_0)),k9_relat_1(k4_relat_1(esk2_0),k9_relat_1(esk2_0,esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_54])])).
% 1.16/1.32  cnf(c_0_63, plain, (r1_tarski(k1_relat_1(X1),k9_relat_1(X2,X3))|~r1_tarski(X1,k4_relat_1(k7_relat_1(X2,X3)))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_45]), c_0_46])).
% 1.16/1.32  cnf(c_0_64, plain, (r1_tarski(k7_relat_1(X1,X2),k5_relat_1(X1,k6_relat_1(k9_relat_1(X1,X2))))|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_58])])).
% 1.16/1.32  cnf(c_0_65, plain, (k5_relat_1(X1,k6_relat_1(X2))=k4_relat_1(k7_relat_1(k4_relat_1(X1),X2))|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_61]), c_0_58])]), c_0_42])).
% 1.16/1.32  cnf(c_0_66, negated_conjecture, (~r1_tarski(k7_relat_1(esk2_0,esk1_0),k4_relat_1(k7_relat_1(k4_relat_1(esk2_0),k9_relat_1(esk2_0,esk1_0))))|~v1_relat_1(k7_relat_1(esk2_0,esk1_0))|~v1_relat_1(k4_relat_1(esk2_0))), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 1.16/1.32  cnf(c_0_67, plain, (r1_tarski(k7_relat_1(X1,X2),k4_relat_1(k7_relat_1(k4_relat_1(X1),k9_relat_1(X1,X2))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 1.16/1.32  cnf(c_0_68, negated_conjecture, (~v1_relat_1(k7_relat_1(esk2_0,esk1_0))|~v1_relat_1(k4_relat_1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_54])])).
% 1.16/1.32  cnf(c_0_69, negated_conjecture, (~v1_relat_1(k4_relat_1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_46]), c_0_54])])).
% 1.16/1.32  cnf(c_0_70, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_42]), c_0_54])]), ['proof']).
% 1.16/1.32  # SZS output end CNFRefutation
% 1.16/1.32  # Proof object total steps             : 71
% 1.16/1.32  # Proof object clause steps            : 36
% 1.16/1.32  # Proof object formula steps           : 35
% 1.16/1.32  # Proof object conjectures             : 12
% 1.16/1.32  # Proof object clause conjectures      : 9
% 1.16/1.32  # Proof object formula conjectures     : 3
% 1.16/1.32  # Proof object initial clauses used    : 18
% 1.16/1.32  # Proof object initial formulas used   : 17
% 1.16/1.32  # Proof object generating inferences   : 13
% 1.16/1.32  # Proof object simplifying inferences  : 24
% 1.16/1.32  # Training examples: 0 positive, 0 negative
% 1.16/1.32  # Parsed axioms                        : 17
% 1.16/1.32  # Removed by relevancy pruning/SinE    : 0
% 1.16/1.32  # Initial clauses                      : 20
% 1.16/1.32  # Removed in clause preprocessing      : 2
% 1.16/1.32  # Initial clauses in saturation        : 18
% 1.16/1.32  # Processed clauses                    : 8490
% 1.16/1.32  # ...of these trivial                  : 137
% 1.16/1.32  # ...subsumed                          : 7414
% 1.16/1.32  # ...remaining for further processing  : 939
% 1.16/1.32  # Other redundant clauses eliminated   : 0
% 1.16/1.32  # Clauses deleted for lack of memory   : 0
% 1.16/1.32  # Backward-subsumed                    : 11
% 1.16/1.32  # Backward-rewritten                   : 13
% 1.16/1.32  # Generated clauses                    : 111495
% 1.16/1.32  # ...of the previous two non-trivial   : 109025
% 1.16/1.32  # Contextual simplify-reflections      : 382
% 1.16/1.32  # Paramodulations                      : 111495
% 1.16/1.32  # Factorizations                       : 0
% 1.16/1.32  # Equation resolutions                 : 0
% 1.16/1.32  # Propositional unsat checks           : 0
% 1.16/1.32  #    Propositional check models        : 0
% 1.16/1.32  #    Propositional check unsatisfiable : 0
% 1.16/1.32  #    Propositional clauses             : 0
% 1.16/1.32  #    Propositional clauses after purity: 0
% 1.16/1.32  #    Propositional unsat core size     : 0
% 1.16/1.32  #    Propositional preprocessing time  : 0.000
% 1.16/1.32  #    Propositional encoding time       : 0.000
% 1.16/1.32  #    Propositional solver time         : 0.000
% 1.16/1.32  #    Success case prop preproc time    : 0.000
% 1.16/1.32  #    Success case prop encoding time   : 0.000
% 1.16/1.32  #    Success case prop solver time     : 0.000
% 1.16/1.32  # Current number of processed clauses  : 897
% 1.16/1.32  #    Positive orientable unit clauses  : 44
% 1.16/1.32  #    Positive unorientable unit clauses: 1
% 1.16/1.32  #    Negative unit clauses             : 3
% 1.16/1.32  #    Non-unit-clauses                  : 849
% 1.16/1.32  # Current number of unprocessed clauses: 100470
% 1.16/1.32  # ...number of literals in the above   : 427437
% 1.16/1.32  # Current number of archived formulas  : 0
% 1.16/1.32  # Current number of archived clauses   : 44
% 1.16/1.32  # Clause-clause subsumption calls (NU) : 145317
% 1.16/1.32  # Rec. Clause-clause subsumption calls : 97875
% 1.16/1.32  # Non-unit clause-clause subsumptions  : 7807
% 1.16/1.32  # Unit Clause-clause subsumption calls : 15
% 1.16/1.32  # Rewrite failures with RHS unbound    : 0
% 1.16/1.32  # BW rewrite match attempts            : 72
% 1.16/1.32  # BW rewrite match successes           : 17
% 1.16/1.32  # Condensation attempts                : 0
% 1.16/1.32  # Condensation successes               : 0
% 1.16/1.32  # Termbank termtop insertions          : 2422756
% 1.16/1.33  
% 1.16/1.33  # -------------------------------------------------
% 1.16/1.33  # User time                : 0.930 s
% 1.16/1.33  # System time              : 0.052 s
% 1.16/1.33  # Total time               : 0.981 s
% 1.16/1.33  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
