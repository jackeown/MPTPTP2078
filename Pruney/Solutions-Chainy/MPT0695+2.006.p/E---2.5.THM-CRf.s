%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:55:01 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 761 expanded)
%              Number of clauses        :   60 ( 317 expanded)
%              Number of leaves         :   11 ( 185 expanded)
%              Depth                    :   12
%              Number of atoms          :  133 (1670 expanded)
%              Number of equality atoms :   72 ( 578 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    9 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t150_funct_1,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => k9_relat_1(X3,k3_xboole_0(X1,k10_relat_1(X3,X2))) = k3_xboole_0(k9_relat_1(X3,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_funct_1)).

fof(t90_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k1_relat_1(k7_relat_1(X2,X1)) = k3_xboole_0(k1_relat_1(X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t100_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => k7_relat_1(k7_relat_1(X3,X1),X2) = k7_relat_1(X3,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).

fof(fc8_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_relat_1(k7_relat_1(X1,X2))
        & v1_funct_1(k7_relat_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_funct_1)).

fof(t139_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => k10_relat_1(k7_relat_1(X3,X1),X2) = k3_xboole_0(X1,k10_relat_1(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).

fof(t101_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k7_relat_1(X2,X1),X1) = k7_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t101_relat_1)).

fof(t145_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k9_relat_1(X2,X1) = k9_relat_1(X2,k3_xboole_0(k1_relat_1(X2),X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_relat_1)).

fof(t148_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k2_relat_1(k7_relat_1(X2,X1)) = k9_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(t148_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => k9_relat_1(X2,k10_relat_1(X2,X1)) = k3_xboole_0(X1,k9_relat_1(X2,k1_relat_1(X2))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_funct_1)).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_relat_1(X3)
          & v1_funct_1(X3) )
       => k9_relat_1(X3,k3_xboole_0(X1,k10_relat_1(X3,X2))) = k3_xboole_0(k9_relat_1(X3,X1),X2) ) ),
    inference(assume_negation,[status(cth)],[t150_funct_1])).

fof(c_0_12,plain,(
    ! [X17,X18] :
      ( ~ v1_relat_1(X18)
      | k1_relat_1(k7_relat_1(X18,X17)) = k3_xboole_0(k1_relat_1(X18),X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t90_relat_1])])).

fof(c_0_13,plain,(
    ! [X6,X7] : k1_setfam_1(k2_tarski(X6,X7)) = k3_xboole_0(X6,X7) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_14,plain,(
    ! [X8,X9,X10] :
      ( ~ v1_relat_1(X10)
      | k7_relat_1(k7_relat_1(X10,X8),X9) = k7_relat_1(X10,k3_xboole_0(X8,X9)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t100_relat_1])])).

fof(c_0_15,plain,(
    ! [X19,X20] :
      ( ( v1_relat_1(k7_relat_1(X19,X20))
        | ~ v1_relat_1(X19)
        | ~ v1_funct_1(X19) )
      & ( v1_funct_1(k7_relat_1(X19,X20))
        | ~ v1_relat_1(X19)
        | ~ v1_funct_1(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc8_funct_1])])])).

fof(c_0_16,negated_conjecture,
    ( v1_relat_1(esk3_0)
    & v1_funct_1(esk3_0)
    & k9_relat_1(esk3_0,k3_xboole_0(esk1_0,k10_relat_1(esk3_0,esk2_0))) != k3_xboole_0(k9_relat_1(esk3_0,esk1_0),esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).

fof(c_0_17,plain,(
    ! [X21,X22,X23] :
      ( ~ v1_relat_1(X23)
      | k10_relat_1(k7_relat_1(X23,X21),X22) = k3_xboole_0(X21,k10_relat_1(X23,X22)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t139_funct_1])])).

cnf(c_0_18,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = k3_xboole_0(k1_relat_1(X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_20,plain,(
    ! [X11,X12] :
      ( ~ v1_relat_1(X12)
      | k7_relat_1(k7_relat_1(X12,X11),X11) = k7_relat_1(X12,X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t101_relat_1])])).

cnf(c_0_21,plain,
    ( k7_relat_1(k7_relat_1(X1,X2),X3) = k7_relat_1(X1,k3_xboole_0(X2,X3))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,plain,
    ( v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,plain,
    ( v1_funct_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_26,plain,
    ( k10_relat_1(k7_relat_1(X1,X2),X3) = k3_xboole_0(X2,k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_27,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = k1_setfam_1(k2_tarski(k1_relat_1(X1),X2))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_28,plain,
    ( k7_relat_1(k7_relat_1(X1,X2),X2) = k7_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,plain,
    ( k7_relat_1(k7_relat_1(X1,X2),X3) = k7_relat_1(X1,k1_setfam_1(k2_tarski(X2,X3)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_21,c_0_19])).

fof(c_0_30,plain,(
    ! [X13,X14] :
      ( ~ v1_relat_1(X14)
      | k9_relat_1(X14,X13) = k9_relat_1(X14,k3_xboole_0(k1_relat_1(X14),X13)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t145_relat_1])])).

fof(c_0_31,plain,(
    ! [X15,X16] :
      ( ~ v1_relat_1(X16)
      | k2_relat_1(k7_relat_1(X16,X15)) = k9_relat_1(X16,X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).

cnf(c_0_32,plain,
    ( v1_relat_1(k7_relat_1(k7_relat_1(X1,X2),X3))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_22])).

cnf(c_0_33,negated_conjecture,
    ( v1_relat_1(k7_relat_1(esk3_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_24]),c_0_25])])).

cnf(c_0_34,plain,
    ( k10_relat_1(k7_relat_1(X1,X2),X3) = k1_setfam_1(k2_tarski(X2,k10_relat_1(X1,X3)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_26,c_0_19])).

fof(c_0_35,plain,(
    ! [X4,X5] : k2_tarski(X4,X5) = k2_tarski(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

cnf(c_0_36,negated_conjecture,
    ( k1_relat_1(k7_relat_1(esk3_0,X1)) = k1_setfam_1(k2_tarski(k1_relat_1(esk3_0),X1)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_25])).

cnf(c_0_37,negated_conjecture,
    ( k7_relat_1(k7_relat_1(esk3_0,X1),X1) = k7_relat_1(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_25])).

cnf(c_0_38,negated_conjecture,
    ( k7_relat_1(k7_relat_1(esk3_0,X1),X2) = k7_relat_1(esk3_0,k1_setfam_1(k2_tarski(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_29,c_0_25])).

cnf(c_0_39,plain,
    ( k9_relat_1(X1,X2) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_40,plain,
    ( k2_relat_1(k7_relat_1(X1,X2)) = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_41,negated_conjecture,
    ( v1_relat_1(k7_relat_1(k7_relat_1(esk3_0,X1),X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_24]),c_0_25])])).

cnf(c_0_42,negated_conjecture,
    ( k7_relat_1(k7_relat_1(k7_relat_1(esk3_0,X1),X2),X3) = k7_relat_1(k7_relat_1(esk3_0,X1),k1_setfam_1(k2_tarski(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_29,c_0_33])).

cnf(c_0_43,negated_conjecture,
    ( k1_setfam_1(k2_tarski(X1,k10_relat_1(esk3_0,X2))) = k10_relat_1(k7_relat_1(esk3_0,X1),X2) ),
    inference(spm,[status(thm)],[c_0_34,c_0_25])).

cnf(c_0_44,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

fof(c_0_45,plain,(
    ! [X24,X25] :
      ( ~ v1_relat_1(X25)
      | ~ v1_funct_1(X25)
      | k9_relat_1(X25,k10_relat_1(X25,X24)) = k3_xboole_0(X24,k9_relat_1(X25,k1_relat_1(X25))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_funct_1])])).

cnf(c_0_46,negated_conjecture,
    ( k1_relat_1(k7_relat_1(k7_relat_1(esk3_0,X1),X2)) = k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(k1_relat_1(esk3_0),X1)),X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_33]),c_0_36])).

cnf(c_0_47,negated_conjecture,
    ( k7_relat_1(esk3_0,k1_setfam_1(k2_tarski(X1,X1))) = k7_relat_1(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_48,plain,
    ( k9_relat_1(X1,X2) = k9_relat_1(X1,k1_setfam_1(k2_tarski(k1_relat_1(X1),X2)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_39,c_0_19])).

cnf(c_0_49,negated_conjecture,
    ( k2_relat_1(k7_relat_1(k7_relat_1(esk3_0,X1),X2)) = k9_relat_1(k7_relat_1(esk3_0,X1),X2) ),
    inference(spm,[status(thm)],[c_0_40,c_0_33])).

cnf(c_0_50,negated_conjecture,
    ( k2_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(esk3_0,X1),X2),X3)) = k9_relat_1(k7_relat_1(k7_relat_1(esk3_0,X1),X2),X3) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_51,negated_conjecture,
    ( k7_relat_1(k7_relat_1(esk3_0,X1),k1_setfam_1(k2_tarski(X1,X2))) = k7_relat_1(k7_relat_1(esk3_0,X1),X2) ),
    inference(spm,[status(thm)],[c_0_42,c_0_37])).

cnf(c_0_52,negated_conjecture,
    ( k9_relat_1(esk3_0,k3_xboole_0(esk1_0,k10_relat_1(esk3_0,esk2_0))) != k3_xboole_0(k9_relat_1(esk3_0,esk1_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_53,negated_conjecture,
    ( k1_setfam_1(k2_tarski(k10_relat_1(esk3_0,X1),X2)) = k10_relat_1(k7_relat_1(esk3_0,X2),X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_54,negated_conjecture,
    ( k2_relat_1(k7_relat_1(esk3_0,X1)) = k9_relat_1(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_25])).

cnf(c_0_55,plain,
    ( k9_relat_1(X1,k10_relat_1(X1,X2)) = k3_xboole_0(X2,k9_relat_1(X1,k1_relat_1(X1)))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_56,negated_conjecture,
    ( k1_setfam_1(k2_tarski(X1,k1_setfam_1(k2_tarski(k1_relat_1(esk3_0),X1)))) = k1_setfam_1(k2_tarski(k1_relat_1(esk3_0),X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_37]),c_0_36]),c_0_44])).

cnf(c_0_57,negated_conjecture,
    ( k1_setfam_1(k2_tarski(k1_relat_1(esk3_0),k1_setfam_1(k2_tarski(X1,X1)))) = k1_setfam_1(k2_tarski(k1_relat_1(esk3_0),X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_47]),c_0_36])).

cnf(c_0_58,negated_conjecture,
    ( k9_relat_1(k7_relat_1(esk3_0,X1),k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(k1_relat_1(esk3_0),X1)),X2))) = k9_relat_1(k7_relat_1(esk3_0,X1),X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_33]),c_0_36])).

cnf(c_0_59,negated_conjecture,
    ( k9_relat_1(k7_relat_1(k7_relat_1(esk3_0,X1),X2),X3) = k9_relat_1(k7_relat_1(esk3_0,X1),k1_setfam_1(k2_tarski(X2,X3))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_42]),c_0_50])).

cnf(c_0_60,negated_conjecture,
    ( k7_relat_1(k7_relat_1(esk3_0,X1),k1_setfam_1(k2_tarski(X2,X1))) = k7_relat_1(k7_relat_1(esk3_0,X1),X2) ),
    inference(spm,[status(thm)],[c_0_51,c_0_44])).

cnf(c_0_61,negated_conjecture,
    ( k9_relat_1(esk3_0,k1_setfam_1(k2_tarski(esk1_0,k10_relat_1(esk3_0,esk2_0)))) != k1_setfam_1(k2_tarski(k9_relat_1(esk3_0,esk1_0),esk2_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_19]),c_0_19])).

cnf(c_0_62,negated_conjecture,
    ( k7_relat_1(esk3_0,k10_relat_1(k7_relat_1(esk3_0,X1),X2)) = k7_relat_1(k7_relat_1(esk3_0,k10_relat_1(esk3_0,X2)),X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_53])).

cnf(c_0_63,negated_conjecture,
    ( k9_relat_1(k7_relat_1(esk3_0,X1),X2) = k9_relat_1(esk3_0,k1_setfam_1(k2_tarski(X1,X2))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_38]),c_0_49])).

cnf(c_0_64,plain,
    ( k9_relat_1(X1,k10_relat_1(X1,X2)) = k1_setfam_1(k2_tarski(X2,k9_relat_1(X1,k1_relat_1(X1))))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(rw,[status(thm)],[c_0_55,c_0_19])).

cnf(c_0_65,negated_conjecture,
    ( v1_funct_1(k7_relat_1(k7_relat_1(esk3_0,X1),X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_38]),c_0_24]),c_0_25])])).

cnf(c_0_66,negated_conjecture,
    ( k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(X1,X1)),k1_setfam_1(k2_tarski(k1_relat_1(esk3_0),X1)))) = k1_setfam_1(k2_tarski(k1_relat_1(esk3_0),X1)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_67,negated_conjecture,
    ( k9_relat_1(k7_relat_1(k7_relat_1(esk3_0,X1),k1_relat_1(esk3_0)),X2) = k9_relat_1(k7_relat_1(esk3_0,X1),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58,c_0_59]),c_0_60])).

cnf(c_0_68,negated_conjecture,
    ( k9_relat_1(k7_relat_1(esk3_0,X1),k1_setfam_1(k2_tarski(X1,X2))) = k9_relat_1(k7_relat_1(esk3_0,X1),X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_51]),c_0_49])).

cnf(c_0_69,negated_conjecture,
    ( k1_setfam_1(k2_tarski(k9_relat_1(esk3_0,esk1_0),esk2_0)) != k9_relat_1(esk3_0,k10_relat_1(k7_relat_1(esk3_0,esk1_0),esk2_0)) ),
    inference(rw,[status(thm)],[c_0_61,c_0_43])).

cnf(c_0_70,negated_conjecture,
    ( k9_relat_1(esk3_0,k10_relat_1(k7_relat_1(esk3_0,X1),X2)) = k9_relat_1(k7_relat_1(esk3_0,k10_relat_1(esk3_0,X2)),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_62]),c_0_49])).

cnf(c_0_71,negated_conjecture,
    ( k9_relat_1(k7_relat_1(esk3_0,X1),X2) = k9_relat_1(esk3_0,k1_setfam_1(k2_tarski(X2,X1))) ),
    inference(spm,[status(thm)],[c_0_63,c_0_44])).

cnf(c_0_72,negated_conjecture,
    ( k1_setfam_1(k2_tarski(X1,k9_relat_1(k7_relat_1(k7_relat_1(esk3_0,X2),X3),k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(k1_relat_1(esk3_0),X2)),X3))))) = k9_relat_1(k7_relat_1(k7_relat_1(esk3_0,X2),X3),k10_relat_1(k7_relat_1(k7_relat_1(esk3_0,X2),X3),X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_46]),c_0_41])])).

cnf(c_0_73,negated_conjecture,
    ( k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(k1_relat_1(esk3_0),X1)),k1_setfam_1(k2_tarski(X1,X1)))) = k1_setfam_1(k2_tarski(k1_relat_1(esk3_0),X1)) ),
    inference(spm,[status(thm)],[c_0_66,c_0_44])).

cnf(c_0_74,negated_conjecture,
    ( k9_relat_1(k7_relat_1(esk3_0,X1),k1_setfam_1(k2_tarski(k1_relat_1(esk3_0),X2))) = k9_relat_1(k7_relat_1(esk3_0,X1),X2) ),
    inference(spm,[status(thm)],[c_0_59,c_0_67])).

cnf(c_0_75,negated_conjecture,
    ( k9_relat_1(k7_relat_1(esk3_0,X1),X1) = k9_relat_1(esk3_0,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_37]),c_0_54])).

cnf(c_0_76,negated_conjecture,
    ( k9_relat_1(k7_relat_1(esk3_0,X1),k10_relat_1(k7_relat_1(esk3_0,X1),X2)) = k9_relat_1(k7_relat_1(esk3_0,X1),k10_relat_1(esk3_0,X2)) ),
    inference(spm,[status(thm)],[c_0_68,c_0_43])).

cnf(c_0_77,negated_conjecture,
    ( k1_setfam_1(k2_tarski(k9_relat_1(esk3_0,esk1_0),esk2_0)) != k9_relat_1(k7_relat_1(esk3_0,k10_relat_1(esk3_0,esk2_0)),esk1_0) ),
    inference(rw,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_78,negated_conjecture,
    ( k9_relat_1(k7_relat_1(esk3_0,X1),X2) = k9_relat_1(k7_relat_1(esk3_0,X2),X1) ),
    inference(spm,[status(thm)],[c_0_63,c_0_71])).

cnf(c_0_79,negated_conjecture,
    ( k1_setfam_1(k2_tarski(X1,k9_relat_1(esk3_0,X2))) = k9_relat_1(k7_relat_1(esk3_0,X2),k10_relat_1(esk3_0,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_51]),c_0_37]),c_0_74]),c_0_75]),c_0_51]),c_0_37]),c_0_51]),c_0_37]),c_0_76])).

cnf(c_0_80,negated_conjecture,
    ( k1_setfam_1(k2_tarski(k9_relat_1(esk3_0,esk1_0),esk2_0)) != k9_relat_1(k7_relat_1(esk3_0,esk1_0),k10_relat_1(esk3_0,esk2_0)) ),
    inference(rw,[status(thm)],[c_0_77,c_0_78])).

cnf(c_0_81,negated_conjecture,
    ( k1_setfam_1(k2_tarski(k9_relat_1(esk3_0,X1),X2)) = k9_relat_1(k7_relat_1(esk3_0,X1),k10_relat_1(esk3_0,X2)) ),
    inference(spm,[status(thm)],[c_0_79,c_0_44])).

cnf(c_0_82,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_80,c_0_81])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:30:23 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.45  # AutoSched0-Mode selected heuristic G_E___208_B00_00_F1_SE_CS_SP_PS_S070I
% 0.19/0.45  # and selection function SelectVGNonCR.
% 0.19/0.45  #
% 0.19/0.45  # Preprocessing time       : 0.027 s
% 0.19/0.45  # Presaturation interreduction done
% 0.19/0.45  
% 0.19/0.45  # Proof found!
% 0.19/0.45  # SZS status Theorem
% 0.19/0.45  # SZS output start CNFRefutation
% 0.19/0.45  fof(t150_funct_1, conjecture, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>k9_relat_1(X3,k3_xboole_0(X1,k10_relat_1(X3,X2)))=k3_xboole_0(k9_relat_1(X3,X1),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t150_funct_1)).
% 0.19/0.45  fof(t90_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k1_relat_1(k7_relat_1(X2,X1))=k3_xboole_0(k1_relat_1(X2),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_relat_1)).
% 0.19/0.45  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.19/0.45  fof(t100_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>k7_relat_1(k7_relat_1(X3,X1),X2)=k7_relat_1(X3,k3_xboole_0(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_relat_1)).
% 0.19/0.45  fof(fc8_funct_1, axiom, ![X1, X2]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v1_relat_1(k7_relat_1(X1,X2))&v1_funct_1(k7_relat_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc8_funct_1)).
% 0.19/0.45  fof(t139_funct_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>k10_relat_1(k7_relat_1(X3,X1),X2)=k3_xboole_0(X1,k10_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t139_funct_1)).
% 0.19/0.45  fof(t101_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k7_relat_1(k7_relat_1(X2,X1),X1)=k7_relat_1(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t101_relat_1)).
% 0.19/0.45  fof(t145_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k9_relat_1(X2,X1)=k9_relat_1(X2,k3_xboole_0(k1_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t145_relat_1)).
% 0.19/0.45  fof(t148_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k2_relat_1(k7_relat_1(X2,X1))=k9_relat_1(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 0.19/0.45  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 0.19/0.45  fof(t148_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>k9_relat_1(X2,k10_relat_1(X2,X1))=k3_xboole_0(X1,k9_relat_1(X2,k1_relat_1(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_funct_1)).
% 0.19/0.45  fof(c_0_11, negated_conjecture, ~(![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>k9_relat_1(X3,k3_xboole_0(X1,k10_relat_1(X3,X2)))=k3_xboole_0(k9_relat_1(X3,X1),X2))), inference(assume_negation,[status(cth)],[t150_funct_1])).
% 0.19/0.45  fof(c_0_12, plain, ![X17, X18]:(~v1_relat_1(X18)|k1_relat_1(k7_relat_1(X18,X17))=k3_xboole_0(k1_relat_1(X18),X17)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t90_relat_1])])).
% 0.19/0.45  fof(c_0_13, plain, ![X6, X7]:k1_setfam_1(k2_tarski(X6,X7))=k3_xboole_0(X6,X7), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.19/0.45  fof(c_0_14, plain, ![X8, X9, X10]:(~v1_relat_1(X10)|k7_relat_1(k7_relat_1(X10,X8),X9)=k7_relat_1(X10,k3_xboole_0(X8,X9))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t100_relat_1])])).
% 0.19/0.45  fof(c_0_15, plain, ![X19, X20]:((v1_relat_1(k7_relat_1(X19,X20))|(~v1_relat_1(X19)|~v1_funct_1(X19)))&(v1_funct_1(k7_relat_1(X19,X20))|(~v1_relat_1(X19)|~v1_funct_1(X19)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc8_funct_1])])])).
% 0.19/0.45  fof(c_0_16, negated_conjecture, ((v1_relat_1(esk3_0)&v1_funct_1(esk3_0))&k9_relat_1(esk3_0,k3_xboole_0(esk1_0,k10_relat_1(esk3_0,esk2_0)))!=k3_xboole_0(k9_relat_1(esk3_0,esk1_0),esk2_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).
% 0.19/0.45  fof(c_0_17, plain, ![X21, X22, X23]:(~v1_relat_1(X23)|k10_relat_1(k7_relat_1(X23,X21),X22)=k3_xboole_0(X21,k10_relat_1(X23,X22))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t139_funct_1])])).
% 0.19/0.45  cnf(c_0_18, plain, (k1_relat_1(k7_relat_1(X1,X2))=k3_xboole_0(k1_relat_1(X1),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.45  cnf(c_0_19, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.45  fof(c_0_20, plain, ![X11, X12]:(~v1_relat_1(X12)|k7_relat_1(k7_relat_1(X12,X11),X11)=k7_relat_1(X12,X11)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t101_relat_1])])).
% 0.19/0.45  cnf(c_0_21, plain, (k7_relat_1(k7_relat_1(X1,X2),X3)=k7_relat_1(X1,k3_xboole_0(X2,X3))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.45  cnf(c_0_22, plain, (v1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.45  cnf(c_0_23, plain, (v1_funct_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.45  cnf(c_0_24, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.45  cnf(c_0_25, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.45  cnf(c_0_26, plain, (k10_relat_1(k7_relat_1(X1,X2),X3)=k3_xboole_0(X2,k10_relat_1(X1,X3))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.45  cnf(c_0_27, plain, (k1_relat_1(k7_relat_1(X1,X2))=k1_setfam_1(k2_tarski(k1_relat_1(X1),X2))|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_18, c_0_19])).
% 0.19/0.45  cnf(c_0_28, plain, (k7_relat_1(k7_relat_1(X1,X2),X2)=k7_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.45  cnf(c_0_29, plain, (k7_relat_1(k7_relat_1(X1,X2),X3)=k7_relat_1(X1,k1_setfam_1(k2_tarski(X2,X3)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_21, c_0_19])).
% 0.19/0.45  fof(c_0_30, plain, ![X13, X14]:(~v1_relat_1(X14)|k9_relat_1(X14,X13)=k9_relat_1(X14,k3_xboole_0(k1_relat_1(X14),X13))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t145_relat_1])])).
% 0.19/0.45  fof(c_0_31, plain, ![X15, X16]:(~v1_relat_1(X16)|k2_relat_1(k7_relat_1(X16,X15))=k9_relat_1(X16,X15)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).
% 0.19/0.45  cnf(c_0_32, plain, (v1_relat_1(k7_relat_1(k7_relat_1(X1,X2),X3))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_22])).
% 0.19/0.45  cnf(c_0_33, negated_conjecture, (v1_relat_1(k7_relat_1(esk3_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_24]), c_0_25])])).
% 0.19/0.45  cnf(c_0_34, plain, (k10_relat_1(k7_relat_1(X1,X2),X3)=k1_setfam_1(k2_tarski(X2,k10_relat_1(X1,X3)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_26, c_0_19])).
% 0.19/0.45  fof(c_0_35, plain, ![X4, X5]:k2_tarski(X4,X5)=k2_tarski(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 0.19/0.45  cnf(c_0_36, negated_conjecture, (k1_relat_1(k7_relat_1(esk3_0,X1))=k1_setfam_1(k2_tarski(k1_relat_1(esk3_0),X1))), inference(spm,[status(thm)],[c_0_27, c_0_25])).
% 0.19/0.45  cnf(c_0_37, negated_conjecture, (k7_relat_1(k7_relat_1(esk3_0,X1),X1)=k7_relat_1(esk3_0,X1)), inference(spm,[status(thm)],[c_0_28, c_0_25])).
% 0.19/0.45  cnf(c_0_38, negated_conjecture, (k7_relat_1(k7_relat_1(esk3_0,X1),X2)=k7_relat_1(esk3_0,k1_setfam_1(k2_tarski(X1,X2)))), inference(spm,[status(thm)],[c_0_29, c_0_25])).
% 0.19/0.45  cnf(c_0_39, plain, (k9_relat_1(X1,X2)=k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.45  cnf(c_0_40, plain, (k2_relat_1(k7_relat_1(X1,X2))=k9_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.45  cnf(c_0_41, negated_conjecture, (v1_relat_1(k7_relat_1(k7_relat_1(esk3_0,X1),X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_24]), c_0_25])])).
% 0.19/0.45  cnf(c_0_42, negated_conjecture, (k7_relat_1(k7_relat_1(k7_relat_1(esk3_0,X1),X2),X3)=k7_relat_1(k7_relat_1(esk3_0,X1),k1_setfam_1(k2_tarski(X2,X3)))), inference(spm,[status(thm)],[c_0_29, c_0_33])).
% 0.19/0.45  cnf(c_0_43, negated_conjecture, (k1_setfam_1(k2_tarski(X1,k10_relat_1(esk3_0,X2)))=k10_relat_1(k7_relat_1(esk3_0,X1),X2)), inference(spm,[status(thm)],[c_0_34, c_0_25])).
% 0.19/0.45  cnf(c_0_44, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.19/0.45  fof(c_0_45, plain, ![X24, X25]:(~v1_relat_1(X25)|~v1_funct_1(X25)|k9_relat_1(X25,k10_relat_1(X25,X24))=k3_xboole_0(X24,k9_relat_1(X25,k1_relat_1(X25)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_funct_1])])).
% 0.19/0.45  cnf(c_0_46, negated_conjecture, (k1_relat_1(k7_relat_1(k7_relat_1(esk3_0,X1),X2))=k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(k1_relat_1(esk3_0),X1)),X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_33]), c_0_36])).
% 0.19/0.45  cnf(c_0_47, negated_conjecture, (k7_relat_1(esk3_0,k1_setfam_1(k2_tarski(X1,X1)))=k7_relat_1(esk3_0,X1)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.19/0.45  cnf(c_0_48, plain, (k9_relat_1(X1,X2)=k9_relat_1(X1,k1_setfam_1(k2_tarski(k1_relat_1(X1),X2)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_39, c_0_19])).
% 0.19/0.45  cnf(c_0_49, negated_conjecture, (k2_relat_1(k7_relat_1(k7_relat_1(esk3_0,X1),X2))=k9_relat_1(k7_relat_1(esk3_0,X1),X2)), inference(spm,[status(thm)],[c_0_40, c_0_33])).
% 0.19/0.45  cnf(c_0_50, negated_conjecture, (k2_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(esk3_0,X1),X2),X3))=k9_relat_1(k7_relat_1(k7_relat_1(esk3_0,X1),X2),X3)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.19/0.45  cnf(c_0_51, negated_conjecture, (k7_relat_1(k7_relat_1(esk3_0,X1),k1_setfam_1(k2_tarski(X1,X2)))=k7_relat_1(k7_relat_1(esk3_0,X1),X2)), inference(spm,[status(thm)],[c_0_42, c_0_37])).
% 0.19/0.45  cnf(c_0_52, negated_conjecture, (k9_relat_1(esk3_0,k3_xboole_0(esk1_0,k10_relat_1(esk3_0,esk2_0)))!=k3_xboole_0(k9_relat_1(esk3_0,esk1_0),esk2_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.45  cnf(c_0_53, negated_conjecture, (k1_setfam_1(k2_tarski(k10_relat_1(esk3_0,X1),X2))=k10_relat_1(k7_relat_1(esk3_0,X2),X1)), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.19/0.45  cnf(c_0_54, negated_conjecture, (k2_relat_1(k7_relat_1(esk3_0,X1))=k9_relat_1(esk3_0,X1)), inference(spm,[status(thm)],[c_0_40, c_0_25])).
% 0.19/0.45  cnf(c_0_55, plain, (k9_relat_1(X1,k10_relat_1(X1,X2))=k3_xboole_0(X2,k9_relat_1(X1,k1_relat_1(X1)))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.19/0.45  cnf(c_0_56, negated_conjecture, (k1_setfam_1(k2_tarski(X1,k1_setfam_1(k2_tarski(k1_relat_1(esk3_0),X1))))=k1_setfam_1(k2_tarski(k1_relat_1(esk3_0),X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_37]), c_0_36]), c_0_44])).
% 0.19/0.45  cnf(c_0_57, negated_conjecture, (k1_setfam_1(k2_tarski(k1_relat_1(esk3_0),k1_setfam_1(k2_tarski(X1,X1))))=k1_setfam_1(k2_tarski(k1_relat_1(esk3_0),X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_47]), c_0_36])).
% 0.19/0.45  cnf(c_0_58, negated_conjecture, (k9_relat_1(k7_relat_1(esk3_0,X1),k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(k1_relat_1(esk3_0),X1)),X2)))=k9_relat_1(k7_relat_1(esk3_0,X1),X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_33]), c_0_36])).
% 0.19/0.45  cnf(c_0_59, negated_conjecture, (k9_relat_1(k7_relat_1(k7_relat_1(esk3_0,X1),X2),X3)=k9_relat_1(k7_relat_1(esk3_0,X1),k1_setfam_1(k2_tarski(X2,X3)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_42]), c_0_50])).
% 0.19/0.45  cnf(c_0_60, negated_conjecture, (k7_relat_1(k7_relat_1(esk3_0,X1),k1_setfam_1(k2_tarski(X2,X1)))=k7_relat_1(k7_relat_1(esk3_0,X1),X2)), inference(spm,[status(thm)],[c_0_51, c_0_44])).
% 0.19/0.45  cnf(c_0_61, negated_conjecture, (k9_relat_1(esk3_0,k1_setfam_1(k2_tarski(esk1_0,k10_relat_1(esk3_0,esk2_0))))!=k1_setfam_1(k2_tarski(k9_relat_1(esk3_0,esk1_0),esk2_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52, c_0_19]), c_0_19])).
% 0.19/0.45  cnf(c_0_62, negated_conjecture, (k7_relat_1(esk3_0,k10_relat_1(k7_relat_1(esk3_0,X1),X2))=k7_relat_1(k7_relat_1(esk3_0,k10_relat_1(esk3_0,X2)),X1)), inference(spm,[status(thm)],[c_0_38, c_0_53])).
% 0.19/0.45  cnf(c_0_63, negated_conjecture, (k9_relat_1(k7_relat_1(esk3_0,X1),X2)=k9_relat_1(esk3_0,k1_setfam_1(k2_tarski(X1,X2)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_38]), c_0_49])).
% 0.19/0.45  cnf(c_0_64, plain, (k9_relat_1(X1,k10_relat_1(X1,X2))=k1_setfam_1(k2_tarski(X2,k9_relat_1(X1,k1_relat_1(X1))))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(rw,[status(thm)],[c_0_55, c_0_19])).
% 0.19/0.45  cnf(c_0_65, negated_conjecture, (v1_funct_1(k7_relat_1(k7_relat_1(esk3_0,X1),X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_38]), c_0_24]), c_0_25])])).
% 0.19/0.45  cnf(c_0_66, negated_conjecture, (k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(X1,X1)),k1_setfam_1(k2_tarski(k1_relat_1(esk3_0),X1))))=k1_setfam_1(k2_tarski(k1_relat_1(esk3_0),X1))), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.19/0.45  cnf(c_0_67, negated_conjecture, (k9_relat_1(k7_relat_1(k7_relat_1(esk3_0,X1),k1_relat_1(esk3_0)),X2)=k9_relat_1(k7_relat_1(esk3_0,X1),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58, c_0_59]), c_0_60])).
% 0.19/0.45  cnf(c_0_68, negated_conjecture, (k9_relat_1(k7_relat_1(esk3_0,X1),k1_setfam_1(k2_tarski(X1,X2)))=k9_relat_1(k7_relat_1(esk3_0,X1),X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_51]), c_0_49])).
% 0.19/0.45  cnf(c_0_69, negated_conjecture, (k1_setfam_1(k2_tarski(k9_relat_1(esk3_0,esk1_0),esk2_0))!=k9_relat_1(esk3_0,k10_relat_1(k7_relat_1(esk3_0,esk1_0),esk2_0))), inference(rw,[status(thm)],[c_0_61, c_0_43])).
% 0.19/0.45  cnf(c_0_70, negated_conjecture, (k9_relat_1(esk3_0,k10_relat_1(k7_relat_1(esk3_0,X1),X2))=k9_relat_1(k7_relat_1(esk3_0,k10_relat_1(esk3_0,X2)),X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_62]), c_0_49])).
% 0.19/0.45  cnf(c_0_71, negated_conjecture, (k9_relat_1(k7_relat_1(esk3_0,X1),X2)=k9_relat_1(esk3_0,k1_setfam_1(k2_tarski(X2,X1)))), inference(spm,[status(thm)],[c_0_63, c_0_44])).
% 0.19/0.45  cnf(c_0_72, negated_conjecture, (k1_setfam_1(k2_tarski(X1,k9_relat_1(k7_relat_1(k7_relat_1(esk3_0,X2),X3),k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(k1_relat_1(esk3_0),X2)),X3)))))=k9_relat_1(k7_relat_1(k7_relat_1(esk3_0,X2),X3),k10_relat_1(k7_relat_1(k7_relat_1(esk3_0,X2),X3),X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_46]), c_0_41])])).
% 0.19/0.45  cnf(c_0_73, negated_conjecture, (k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(k1_relat_1(esk3_0),X1)),k1_setfam_1(k2_tarski(X1,X1))))=k1_setfam_1(k2_tarski(k1_relat_1(esk3_0),X1))), inference(spm,[status(thm)],[c_0_66, c_0_44])).
% 0.19/0.45  cnf(c_0_74, negated_conjecture, (k9_relat_1(k7_relat_1(esk3_0,X1),k1_setfam_1(k2_tarski(k1_relat_1(esk3_0),X2)))=k9_relat_1(k7_relat_1(esk3_0,X1),X2)), inference(spm,[status(thm)],[c_0_59, c_0_67])).
% 0.19/0.45  cnf(c_0_75, negated_conjecture, (k9_relat_1(k7_relat_1(esk3_0,X1),X1)=k9_relat_1(esk3_0,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_37]), c_0_54])).
% 0.19/0.45  cnf(c_0_76, negated_conjecture, (k9_relat_1(k7_relat_1(esk3_0,X1),k10_relat_1(k7_relat_1(esk3_0,X1),X2))=k9_relat_1(k7_relat_1(esk3_0,X1),k10_relat_1(esk3_0,X2))), inference(spm,[status(thm)],[c_0_68, c_0_43])).
% 0.19/0.45  cnf(c_0_77, negated_conjecture, (k1_setfam_1(k2_tarski(k9_relat_1(esk3_0,esk1_0),esk2_0))!=k9_relat_1(k7_relat_1(esk3_0,k10_relat_1(esk3_0,esk2_0)),esk1_0)), inference(rw,[status(thm)],[c_0_69, c_0_70])).
% 0.19/0.45  cnf(c_0_78, negated_conjecture, (k9_relat_1(k7_relat_1(esk3_0,X1),X2)=k9_relat_1(k7_relat_1(esk3_0,X2),X1)), inference(spm,[status(thm)],[c_0_63, c_0_71])).
% 0.19/0.45  cnf(c_0_79, negated_conjecture, (k1_setfam_1(k2_tarski(X1,k9_relat_1(esk3_0,X2)))=k9_relat_1(k7_relat_1(esk3_0,X2),k10_relat_1(esk3_0,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_73]), c_0_51]), c_0_37]), c_0_74]), c_0_75]), c_0_51]), c_0_37]), c_0_51]), c_0_37]), c_0_76])).
% 0.19/0.45  cnf(c_0_80, negated_conjecture, (k1_setfam_1(k2_tarski(k9_relat_1(esk3_0,esk1_0),esk2_0))!=k9_relat_1(k7_relat_1(esk3_0,esk1_0),k10_relat_1(esk3_0,esk2_0))), inference(rw,[status(thm)],[c_0_77, c_0_78])).
% 0.19/0.45  cnf(c_0_81, negated_conjecture, (k1_setfam_1(k2_tarski(k9_relat_1(esk3_0,X1),X2))=k9_relat_1(k7_relat_1(esk3_0,X1),k10_relat_1(esk3_0,X2))), inference(spm,[status(thm)],[c_0_79, c_0_44])).
% 0.19/0.45  cnf(c_0_82, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_80, c_0_81])]), ['proof']).
% 0.19/0.45  # SZS output end CNFRefutation
% 0.19/0.45  # Proof object total steps             : 83
% 0.19/0.45  # Proof object clause steps            : 60
% 0.19/0.45  # Proof object formula steps           : 23
% 0.19/0.45  # Proof object conjectures             : 46
% 0.19/0.45  # Proof object clause conjectures      : 43
% 0.19/0.45  # Proof object formula conjectures     : 3
% 0.19/0.45  # Proof object initial clauses used    : 14
% 0.19/0.45  # Proof object initial formulas used   : 11
% 0.19/0.45  # Proof object generating inferences   : 35
% 0.19/0.45  # Proof object simplifying inferences  : 44
% 0.19/0.45  # Training examples: 0 positive, 0 negative
% 0.19/0.45  # Parsed axioms                        : 11
% 0.19/0.45  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.45  # Initial clauses                      : 14
% 0.19/0.45  # Removed in clause preprocessing      : 1
% 0.19/0.45  # Initial clauses in saturation        : 13
% 0.19/0.45  # Processed clauses                    : 526
% 0.19/0.45  # ...of these trivial                  : 145
% 0.19/0.45  # ...subsumed                          : 163
% 0.19/0.45  # ...remaining for further processing  : 218
% 0.19/0.45  # Other redundant clauses eliminated   : 0
% 0.19/0.45  # Clauses deleted for lack of memory   : 0
% 0.19/0.45  # Backward-subsumed                    : 1
% 0.19/0.45  # Backward-rewritten                   : 58
% 0.19/0.45  # Generated clauses                    : 5216
% 0.19/0.45  # ...of the previous two non-trivial   : 3372
% 0.19/0.45  # Contextual simplify-reflections      : 7
% 0.19/0.45  # Paramodulations                      : 5216
% 0.19/0.45  # Factorizations                       : 0
% 0.19/0.45  # Equation resolutions                 : 0
% 0.19/0.45  # Propositional unsat checks           : 0
% 0.19/0.45  #    Propositional check models        : 0
% 0.19/0.45  #    Propositional check unsatisfiable : 0
% 0.19/0.45  #    Propositional clauses             : 0
% 0.19/0.45  #    Propositional clauses after purity: 0
% 0.19/0.45  #    Propositional unsat core size     : 0
% 0.19/0.45  #    Propositional preprocessing time  : 0.000
% 0.19/0.45  #    Propositional encoding time       : 0.000
% 0.19/0.45  #    Propositional solver time         : 0.000
% 0.19/0.45  #    Success case prop preproc time    : 0.000
% 0.19/0.45  #    Success case prop encoding time   : 0.000
% 0.19/0.45  #    Success case prop solver time     : 0.000
% 0.19/0.45  # Current number of processed clauses  : 146
% 0.19/0.45  #    Positive orientable unit clauses  : 111
% 0.19/0.45  #    Positive unorientable unit clauses: 19
% 0.19/0.45  #    Negative unit clauses             : 0
% 0.19/0.45  #    Non-unit-clauses                  : 16
% 0.19/0.45  # Current number of unprocessed clauses: 2777
% 0.19/0.45  # ...number of literals in the above   : 2783
% 0.19/0.45  # Current number of archived formulas  : 0
% 0.19/0.45  # Current number of archived clauses   : 73
% 0.19/0.45  # Clause-clause subsumption calls (NU) : 122
% 0.19/0.45  # Rec. Clause-clause subsumption calls : 106
% 0.19/0.45  # Non-unit clause-clause subsumptions  : 7
% 0.19/0.45  # Unit Clause-clause subsumption calls : 159
% 0.19/0.45  # Rewrite failures with RHS unbound    : 0
% 0.19/0.45  # BW rewrite match attempts            : 752
% 0.19/0.45  # BW rewrite match successes           : 243
% 0.19/0.45  # Condensation attempts                : 0
% 0.19/0.45  # Condensation successes               : 0
% 0.19/0.45  # Termbank termtop insertions          : 105173
% 0.19/0.45  
% 0.19/0.45  # -------------------------------------------------
% 0.19/0.45  # User time                : 0.104 s
% 0.19/0.45  # System time              : 0.011 s
% 0.19/0.45  # Total time               : 0.115 s
% 0.19/0.45  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
