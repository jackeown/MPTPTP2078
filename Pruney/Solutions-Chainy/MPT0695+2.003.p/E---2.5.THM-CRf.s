%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:55:00 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 847 expanded)
%              Number of clauses        :   54 ( 378 expanded)
%              Number of leaves         :   14 ( 206 expanded)
%              Depth                    :   14
%              Number of atoms          :  138 (1473 expanded)
%              Number of equality atoms :   67 ( 678 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t150_funct_1,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => k9_relat_1(X3,k3_xboole_0(X1,k10_relat_1(X3,X2))) = k3_xboole_0(k9_relat_1(X3,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_funct_1)).

fof(t100_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => k7_relat_1(k7_relat_1(X3,X1),X2) = k7_relat_1(X3,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).

fof(dt_k7_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k7_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(t148_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k2_relat_1(k7_relat_1(X2,X1)) = k9_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(t145_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k9_relat_1(X2,X1) = k9_relat_1(X2,k3_xboole_0(k1_relat_1(X2),X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_relat_1)).

fof(t162_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2,X3] :
          ( r1_tarski(X2,X3)
         => k9_relat_1(k7_relat_1(X1,X3),X2) = k9_relat_1(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_relat_1)).

fof(t87_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k1_relat_1(k7_relat_1(X2,X1)),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

fof(t139_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => k10_relat_1(k7_relat_1(X3,X1),X2) = k3_xboole_0(X1,k10_relat_1(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).

fof(t148_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => k9_relat_1(X2,k10_relat_1(X2,X1)) = k3_xboole_0(X1,k9_relat_1(X2,k1_relat_1(X2))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_funct_1)).

fof(fc8_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_relat_1(k7_relat_1(X1,X2))
        & v1_funct_1(k7_relat_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_funct_1)).

fof(t146_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,k1_relat_1(X1)) = k2_relat_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

fof(c_0_14,plain,(
    ! [X8,X9] : k1_setfam_1(k2_tarski(X8,X9)) = k3_xboole_0(X8,X9) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_15,plain,(
    ! [X6,X7] : k1_enumset1(X6,X6,X7) = k2_tarski(X6,X7) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_16,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_relat_1(X3)
          & v1_funct_1(X3) )
       => k9_relat_1(X3,k3_xboole_0(X1,k10_relat_1(X3,X2))) = k3_xboole_0(k9_relat_1(X3,X1),X2) ) ),
    inference(assume_negation,[status(cth)],[t150_funct_1])).

fof(c_0_17,plain,(
    ! [X12,X13,X14] :
      ( ~ v1_relat_1(X14)
      | k7_relat_1(k7_relat_1(X14,X12),X13) = k7_relat_1(X14,k3_xboole_0(X12,X13)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t100_relat_1])])).

cnf(c_0_18,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_20,plain,(
    ! [X10,X11] :
      ( ~ v1_relat_1(X10)
      | v1_relat_1(k7_relat_1(X10,X11)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).

fof(c_0_21,negated_conjecture,
    ( v1_relat_1(esk3_0)
    & v1_funct_1(esk3_0)
    & k9_relat_1(esk3_0,k3_xboole_0(esk1_0,k10_relat_1(esk3_0,esk2_0))) != k3_xboole_0(k9_relat_1(esk3_0,esk1_0),esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).

fof(c_0_22,plain,(
    ! [X18,X19] :
      ( ~ v1_relat_1(X19)
      | k2_relat_1(k7_relat_1(X19,X18)) = k9_relat_1(X19,X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).

cnf(c_0_23,plain,
    ( k7_relat_1(k7_relat_1(X1,X2),X3) = k7_relat_1(X1,k3_xboole_0(X2,X3))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_25,plain,
    ( v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,plain,
    ( k2_relat_1(k7_relat_1(X1,X2)) = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,plain,
    ( k7_relat_1(k7_relat_1(X1,X2),X3) = k7_relat_1(X1,k1_setfam_1(k1_enumset1(X2,X2,X3)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_29,negated_conjecture,
    ( v1_relat_1(k7_relat_1(esk3_0,X1)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

fof(c_0_30,plain,(
    ! [X4,X5] : k2_tarski(X4,X5) = k2_tarski(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

fof(c_0_31,plain,(
    ! [X15,X16] :
      ( ~ v1_relat_1(X16)
      | k9_relat_1(X16,X15) = k9_relat_1(X16,k3_xboole_0(k1_relat_1(X16),X15)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t145_relat_1])])).

cnf(c_0_32,negated_conjecture,
    ( k2_relat_1(k7_relat_1(esk3_0,X1)) = k9_relat_1(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_26])).

cnf(c_0_33,negated_conjecture,
    ( k7_relat_1(esk3_0,k1_setfam_1(k1_enumset1(X1,X1,X2))) = k7_relat_1(k7_relat_1(esk3_0,X1),X2) ),
    inference(spm,[status(thm)],[c_0_28,c_0_26])).

cnf(c_0_34,negated_conjecture,
    ( k2_relat_1(k7_relat_1(k7_relat_1(esk3_0,X1),X2)) = k9_relat_1(k7_relat_1(esk3_0,X1),X2) ),
    inference(spm,[status(thm)],[c_0_27,c_0_29])).

cnf(c_0_35,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_36,plain,
    ( k9_relat_1(X1,X2) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_37,negated_conjecture,
    ( k9_relat_1(esk3_0,k1_setfam_1(k1_enumset1(X1,X1,X2))) = k9_relat_1(k7_relat_1(esk3_0,X1),X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34])).

cnf(c_0_38,plain,
    ( k1_enumset1(X1,X1,X2) = k1_enumset1(X2,X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_19]),c_0_19])).

fof(c_0_39,plain,(
    ! [X20,X21,X22] :
      ( ~ v1_relat_1(X20)
      | ~ r1_tarski(X21,X22)
      | k9_relat_1(k7_relat_1(X20,X22),X21) = k9_relat_1(X20,X21) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t162_relat_1])])])).

fof(c_0_40,plain,(
    ! [X23,X24] :
      ( ~ v1_relat_1(X24)
      | r1_tarski(k1_relat_1(k7_relat_1(X24,X23)),X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t87_relat_1])])).

cnf(c_0_41,plain,
    ( k9_relat_1(X1,X2) = k9_relat_1(X1,k1_setfam_1(k1_enumset1(k1_relat_1(X1),k1_relat_1(X1),X2)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_36,c_0_24])).

cnf(c_0_42,negated_conjecture,
    ( k9_relat_1(k7_relat_1(esk3_0,X1),X2) = k9_relat_1(k7_relat_1(esk3_0,X2),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_37])).

cnf(c_0_43,negated_conjecture,
    ( v1_relat_1(k7_relat_1(k7_relat_1(esk3_0,X1),X2)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_29])).

cnf(c_0_44,plain,
    ( k9_relat_1(k7_relat_1(X1,X3),X2) = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_45,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

fof(c_0_46,plain,(
    ! [X27,X28,X29] :
      ( ~ v1_relat_1(X29)
      | k10_relat_1(k7_relat_1(X29,X27),X28) = k3_xboole_0(X27,k10_relat_1(X29,X28)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t139_funct_1])])).

cnf(c_0_47,negated_conjecture,
    ( k9_relat_1(k7_relat_1(esk3_0,X1),k1_setfam_1(k1_enumset1(k1_relat_1(k7_relat_1(esk3_0,X1)),k1_relat_1(k7_relat_1(esk3_0,X1)),X2))) = k9_relat_1(k7_relat_1(esk3_0,X1),X2) ),
    inference(spm,[status(thm)],[c_0_41,c_0_29])).

cnf(c_0_48,negated_conjecture,
    ( k9_relat_1(k7_relat_1(esk3_0,X1),k1_setfam_1(k1_enumset1(X2,X2,X3))) = k9_relat_1(k7_relat_1(k7_relat_1(esk3_0,X2),X3),X1) ),
    inference(spm,[status(thm)],[c_0_42,c_0_33])).

cnf(c_0_49,negated_conjecture,
    ( k7_relat_1(k7_relat_1(esk3_0,X1),k1_setfam_1(k1_enumset1(X2,X2,X3))) = k7_relat_1(k7_relat_1(k7_relat_1(esk3_0,X1),X2),X3) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_50,negated_conjecture,
    ( k2_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(esk3_0,X1),X2),X3)) = k9_relat_1(k7_relat_1(k7_relat_1(esk3_0,X1),X2),X3) ),
    inference(spm,[status(thm)],[c_0_27,c_0_43])).

cnf(c_0_51,negated_conjecture,
    ( k9_relat_1(k7_relat_1(k7_relat_1(esk3_0,X1),X2),X3) = k9_relat_1(k7_relat_1(esk3_0,X1),X3)
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_44,c_0_29])).

cnf(c_0_52,negated_conjecture,
    ( r1_tarski(k1_relat_1(k7_relat_1(esk3_0,X1)),X1) ),
    inference(spm,[status(thm)],[c_0_45,c_0_26])).

cnf(c_0_53,negated_conjecture,
    ( k9_relat_1(esk3_0,k3_xboole_0(esk1_0,k10_relat_1(esk3_0,esk2_0))) != k3_xboole_0(k9_relat_1(esk3_0,esk1_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_54,plain,
    ( k10_relat_1(k7_relat_1(X1,X2),X3) = k3_xboole_0(X2,k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

fof(c_0_55,plain,(
    ! [X30,X31] :
      ( ~ v1_relat_1(X31)
      | ~ v1_funct_1(X31)
      | k9_relat_1(X31,k10_relat_1(X31,X30)) = k3_xboole_0(X30,k9_relat_1(X31,k1_relat_1(X31))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_funct_1])])).

fof(c_0_56,plain,(
    ! [X25,X26] :
      ( ( v1_relat_1(k7_relat_1(X25,X26))
        | ~ v1_relat_1(X25)
        | ~ v1_funct_1(X25) )
      & ( v1_funct_1(k7_relat_1(X25,X26))
        | ~ v1_relat_1(X25)
        | ~ v1_funct_1(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc8_funct_1])])])).

fof(c_0_57,plain,(
    ! [X17] :
      ( ~ v1_relat_1(X17)
      | k9_relat_1(X17,k1_relat_1(X17)) = k2_relat_1(X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_relat_1])])).

cnf(c_0_58,negated_conjecture,
    ( k9_relat_1(k7_relat_1(k7_relat_1(esk3_0,k1_relat_1(k7_relat_1(esk3_0,X1))),X2),X1) = k9_relat_1(k7_relat_1(esk3_0,X1),X2) ),
    inference(rw,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_59,negated_conjecture,
    ( k9_relat_1(k7_relat_1(k7_relat_1(esk3_0,X1),X2),X3) = k9_relat_1(k7_relat_1(k7_relat_1(esk3_0,X3),X1),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_49]),c_0_50]),c_0_48])).

cnf(c_0_60,negated_conjecture,
    ( k9_relat_1(k7_relat_1(k7_relat_1(esk3_0,X1),X2),k1_relat_1(k7_relat_1(esk3_0,X2))) = k9_relat_1(k7_relat_1(esk3_0,X1),k1_relat_1(k7_relat_1(esk3_0,X2))) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_61,negated_conjecture,
    ( k9_relat_1(esk3_0,k1_setfam_1(k1_enumset1(esk1_0,esk1_0,k10_relat_1(esk3_0,esk2_0)))) != k1_setfam_1(k1_enumset1(k9_relat_1(esk3_0,esk1_0),k9_relat_1(esk3_0,esk1_0),esk2_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53,c_0_24]),c_0_24])).

cnf(c_0_62,plain,
    ( k10_relat_1(k7_relat_1(X1,X2),X3) = k1_setfam_1(k1_enumset1(X2,X2,k10_relat_1(X1,X3)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_54,c_0_24])).

cnf(c_0_63,plain,
    ( k9_relat_1(X1,k10_relat_1(X1,X2)) = k3_xboole_0(X2,k9_relat_1(X1,k1_relat_1(X1)))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_64,plain,
    ( v1_funct_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_65,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_66,plain,
    ( k9_relat_1(X1,k1_relat_1(X1)) = k2_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_67,negated_conjecture,
    ( k9_relat_1(k7_relat_1(esk3_0,X1),k1_relat_1(k7_relat_1(esk3_0,X2))) = k9_relat_1(k7_relat_1(esk3_0,X2),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58,c_0_59]),c_0_60])).

cnf(c_0_68,negated_conjecture,
    ( k9_relat_1(esk3_0,k1_setfam_1(k1_enumset1(esk1_0,esk1_0,k10_relat_1(esk3_0,esk2_0)))) != k1_setfam_1(k1_enumset1(esk2_0,esk2_0,k9_relat_1(esk3_0,esk1_0))) ),
    inference(rw,[status(thm)],[c_0_61,c_0_38])).

cnf(c_0_69,negated_conjecture,
    ( k1_setfam_1(k1_enumset1(X1,X1,k10_relat_1(esk3_0,X2))) = k10_relat_1(k7_relat_1(esk3_0,X1),X2) ),
    inference(spm,[status(thm)],[c_0_62,c_0_26])).

cnf(c_0_70,plain,
    ( k9_relat_1(X1,k10_relat_1(X1,X2)) = k1_setfam_1(k1_enumset1(X2,X2,k9_relat_1(X1,k1_relat_1(X1))))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(rw,[status(thm)],[c_0_63,c_0_24])).

cnf(c_0_71,negated_conjecture,
    ( v1_funct_1(k7_relat_1(esk3_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_26]),c_0_65])])).

cnf(c_0_72,negated_conjecture,
    ( k9_relat_1(k7_relat_1(esk3_0,X1),k1_relat_1(k7_relat_1(esk3_0,X1))) = k9_relat_1(esk3_0,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_29]),c_0_32])).

cnf(c_0_73,negated_conjecture,
    ( k9_relat_1(k7_relat_1(k7_relat_1(esk3_0,X1),X2),k1_relat_1(k7_relat_1(esk3_0,X2))) = k9_relat_1(k7_relat_1(esk3_0,X2),X1) ),
    inference(rw,[status(thm)],[c_0_60,c_0_67])).

cnf(c_0_74,negated_conjecture,
    ( k7_relat_1(k7_relat_1(esk3_0,X1),X2) = k7_relat_1(k7_relat_1(esk3_0,X2),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_38]),c_0_33])).

cnf(c_0_75,negated_conjecture,
    ( k1_setfam_1(k1_enumset1(esk2_0,esk2_0,k9_relat_1(esk3_0,esk1_0))) != k9_relat_1(esk3_0,k10_relat_1(k7_relat_1(esk3_0,esk1_0),esk2_0)) ),
    inference(rw,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_76,negated_conjecture,
    ( k1_setfam_1(k1_enumset1(X1,X1,k9_relat_1(esk3_0,X2))) = k9_relat_1(k7_relat_1(esk3_0,X2),k10_relat_1(k7_relat_1(esk3_0,X2),X1)) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_29]),c_0_71])]),c_0_72])).

cnf(c_0_77,negated_conjecture,
    ( k9_relat_1(k7_relat_1(k7_relat_1(esk3_0,X1),X2),k1_relat_1(k7_relat_1(esk3_0,X1))) = k9_relat_1(k7_relat_1(esk3_0,X1),X2) ),
    inference(spm,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_78,negated_conjecture,
    ( k7_relat_1(k7_relat_1(esk3_0,X1),k10_relat_1(esk3_0,X2)) = k7_relat_1(esk3_0,k10_relat_1(k7_relat_1(esk3_0,X1),X2)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_69])).

cnf(c_0_79,negated_conjecture,
    ( k9_relat_1(k7_relat_1(esk3_0,X1),k10_relat_1(esk3_0,X2)) = k9_relat_1(esk3_0,k10_relat_1(k7_relat_1(esk3_0,X1),X2)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_69])).

cnf(c_0_80,negated_conjecture,
    ( k9_relat_1(k7_relat_1(esk3_0,esk1_0),k10_relat_1(k7_relat_1(esk3_0,esk1_0),esk2_0)) != k9_relat_1(esk3_0,k10_relat_1(k7_relat_1(esk3_0,esk1_0),esk2_0)) ),
    inference(rw,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_81,negated_conjecture,
    ( k9_relat_1(k7_relat_1(esk3_0,X1),k10_relat_1(k7_relat_1(esk3_0,X1),X2)) = k9_relat_1(esk3_0,k10_relat_1(k7_relat_1(esk3_0,X1),X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_67]),c_0_79])).

cnf(c_0_82,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_80,c_0_81])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:41:20 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.14/0.41  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S089A
% 0.14/0.41  # and selection function SelectCQPrecW.
% 0.14/0.41  #
% 0.14/0.41  # Preprocessing time       : 0.027 s
% 0.14/0.41  # Presaturation interreduction done
% 0.14/0.41  
% 0.14/0.41  # Proof found!
% 0.14/0.41  # SZS status Theorem
% 0.14/0.41  # SZS output start CNFRefutation
% 0.14/0.41  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.14/0.41  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.14/0.41  fof(t150_funct_1, conjecture, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>k9_relat_1(X3,k3_xboole_0(X1,k10_relat_1(X3,X2)))=k3_xboole_0(k9_relat_1(X3,X1),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t150_funct_1)).
% 0.14/0.41  fof(t100_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>k7_relat_1(k7_relat_1(X3,X1),X2)=k7_relat_1(X3,k3_xboole_0(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_relat_1)).
% 0.14/0.41  fof(dt_k7_relat_1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k7_relat_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 0.14/0.41  fof(t148_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k2_relat_1(k7_relat_1(X2,X1))=k9_relat_1(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 0.14/0.41  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 0.14/0.41  fof(t145_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k9_relat_1(X2,X1)=k9_relat_1(X2,k3_xboole_0(k1_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t145_relat_1)).
% 0.14/0.41  fof(t162_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2, X3]:(r1_tarski(X2,X3)=>k9_relat_1(k7_relat_1(X1,X3),X2)=k9_relat_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t162_relat_1)).
% 0.14/0.41  fof(t87_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k1_relat_1(k7_relat_1(X2,X1)),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 0.14/0.41  fof(t139_funct_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>k10_relat_1(k7_relat_1(X3,X1),X2)=k3_xboole_0(X1,k10_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t139_funct_1)).
% 0.14/0.41  fof(t148_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>k9_relat_1(X2,k10_relat_1(X2,X1))=k3_xboole_0(X1,k9_relat_1(X2,k1_relat_1(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_funct_1)).
% 0.14/0.41  fof(fc8_funct_1, axiom, ![X1, X2]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v1_relat_1(k7_relat_1(X1,X2))&v1_funct_1(k7_relat_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc8_funct_1)).
% 0.14/0.41  fof(t146_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k9_relat_1(X1,k1_relat_1(X1))=k2_relat_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 0.14/0.41  fof(c_0_14, plain, ![X8, X9]:k1_setfam_1(k2_tarski(X8,X9))=k3_xboole_0(X8,X9), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.14/0.41  fof(c_0_15, plain, ![X6, X7]:k1_enumset1(X6,X6,X7)=k2_tarski(X6,X7), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.14/0.41  fof(c_0_16, negated_conjecture, ~(![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>k9_relat_1(X3,k3_xboole_0(X1,k10_relat_1(X3,X2)))=k3_xboole_0(k9_relat_1(X3,X1),X2))), inference(assume_negation,[status(cth)],[t150_funct_1])).
% 0.14/0.41  fof(c_0_17, plain, ![X12, X13, X14]:(~v1_relat_1(X14)|k7_relat_1(k7_relat_1(X14,X12),X13)=k7_relat_1(X14,k3_xboole_0(X12,X13))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t100_relat_1])])).
% 0.14/0.41  cnf(c_0_18, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.14/0.41  cnf(c_0_19, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.14/0.41  fof(c_0_20, plain, ![X10, X11]:(~v1_relat_1(X10)|v1_relat_1(k7_relat_1(X10,X11))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).
% 0.14/0.41  fof(c_0_21, negated_conjecture, ((v1_relat_1(esk3_0)&v1_funct_1(esk3_0))&k9_relat_1(esk3_0,k3_xboole_0(esk1_0,k10_relat_1(esk3_0,esk2_0)))!=k3_xboole_0(k9_relat_1(esk3_0,esk1_0),esk2_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).
% 0.14/0.41  fof(c_0_22, plain, ![X18, X19]:(~v1_relat_1(X19)|k2_relat_1(k7_relat_1(X19,X18))=k9_relat_1(X19,X18)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).
% 0.14/0.41  cnf(c_0_23, plain, (k7_relat_1(k7_relat_1(X1,X2),X3)=k7_relat_1(X1,k3_xboole_0(X2,X3))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.14/0.41  cnf(c_0_24, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_18, c_0_19])).
% 0.14/0.41  cnf(c_0_25, plain, (v1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.14/0.41  cnf(c_0_26, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.14/0.41  cnf(c_0_27, plain, (k2_relat_1(k7_relat_1(X1,X2))=k9_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.14/0.41  cnf(c_0_28, plain, (k7_relat_1(k7_relat_1(X1,X2),X3)=k7_relat_1(X1,k1_setfam_1(k1_enumset1(X2,X2,X3)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_23, c_0_24])).
% 0.14/0.41  cnf(c_0_29, negated_conjecture, (v1_relat_1(k7_relat_1(esk3_0,X1))), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.14/0.41  fof(c_0_30, plain, ![X4, X5]:k2_tarski(X4,X5)=k2_tarski(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 0.14/0.41  fof(c_0_31, plain, ![X15, X16]:(~v1_relat_1(X16)|k9_relat_1(X16,X15)=k9_relat_1(X16,k3_xboole_0(k1_relat_1(X16),X15))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t145_relat_1])])).
% 0.14/0.41  cnf(c_0_32, negated_conjecture, (k2_relat_1(k7_relat_1(esk3_0,X1))=k9_relat_1(esk3_0,X1)), inference(spm,[status(thm)],[c_0_27, c_0_26])).
% 0.14/0.41  cnf(c_0_33, negated_conjecture, (k7_relat_1(esk3_0,k1_setfam_1(k1_enumset1(X1,X1,X2)))=k7_relat_1(k7_relat_1(esk3_0,X1),X2)), inference(spm,[status(thm)],[c_0_28, c_0_26])).
% 0.14/0.41  cnf(c_0_34, negated_conjecture, (k2_relat_1(k7_relat_1(k7_relat_1(esk3_0,X1),X2))=k9_relat_1(k7_relat_1(esk3_0,X1),X2)), inference(spm,[status(thm)],[c_0_27, c_0_29])).
% 0.14/0.41  cnf(c_0_35, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.14/0.41  cnf(c_0_36, plain, (k9_relat_1(X1,X2)=k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.14/0.41  cnf(c_0_37, negated_conjecture, (k9_relat_1(esk3_0,k1_setfam_1(k1_enumset1(X1,X1,X2)))=k9_relat_1(k7_relat_1(esk3_0,X1),X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_34])).
% 0.14/0.41  cnf(c_0_38, plain, (k1_enumset1(X1,X1,X2)=k1_enumset1(X2,X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_19]), c_0_19])).
% 0.14/0.41  fof(c_0_39, plain, ![X20, X21, X22]:(~v1_relat_1(X20)|(~r1_tarski(X21,X22)|k9_relat_1(k7_relat_1(X20,X22),X21)=k9_relat_1(X20,X21))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t162_relat_1])])])).
% 0.14/0.41  fof(c_0_40, plain, ![X23, X24]:(~v1_relat_1(X24)|r1_tarski(k1_relat_1(k7_relat_1(X24,X23)),X23)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t87_relat_1])])).
% 0.14/0.41  cnf(c_0_41, plain, (k9_relat_1(X1,X2)=k9_relat_1(X1,k1_setfam_1(k1_enumset1(k1_relat_1(X1),k1_relat_1(X1),X2)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_36, c_0_24])).
% 0.14/0.41  cnf(c_0_42, negated_conjecture, (k9_relat_1(k7_relat_1(esk3_0,X1),X2)=k9_relat_1(k7_relat_1(esk3_0,X2),X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_37])).
% 0.14/0.41  cnf(c_0_43, negated_conjecture, (v1_relat_1(k7_relat_1(k7_relat_1(esk3_0,X1),X2))), inference(spm,[status(thm)],[c_0_25, c_0_29])).
% 0.14/0.41  cnf(c_0_44, plain, (k9_relat_1(k7_relat_1(X1,X3),X2)=k9_relat_1(X1,X2)|~v1_relat_1(X1)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.14/0.41  cnf(c_0_45, plain, (r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.14/0.41  fof(c_0_46, plain, ![X27, X28, X29]:(~v1_relat_1(X29)|k10_relat_1(k7_relat_1(X29,X27),X28)=k3_xboole_0(X27,k10_relat_1(X29,X28))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t139_funct_1])])).
% 0.14/0.41  cnf(c_0_47, negated_conjecture, (k9_relat_1(k7_relat_1(esk3_0,X1),k1_setfam_1(k1_enumset1(k1_relat_1(k7_relat_1(esk3_0,X1)),k1_relat_1(k7_relat_1(esk3_0,X1)),X2)))=k9_relat_1(k7_relat_1(esk3_0,X1),X2)), inference(spm,[status(thm)],[c_0_41, c_0_29])).
% 0.14/0.41  cnf(c_0_48, negated_conjecture, (k9_relat_1(k7_relat_1(esk3_0,X1),k1_setfam_1(k1_enumset1(X2,X2,X3)))=k9_relat_1(k7_relat_1(k7_relat_1(esk3_0,X2),X3),X1)), inference(spm,[status(thm)],[c_0_42, c_0_33])).
% 0.14/0.41  cnf(c_0_49, negated_conjecture, (k7_relat_1(k7_relat_1(esk3_0,X1),k1_setfam_1(k1_enumset1(X2,X2,X3)))=k7_relat_1(k7_relat_1(k7_relat_1(esk3_0,X1),X2),X3)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.14/0.41  cnf(c_0_50, negated_conjecture, (k2_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(esk3_0,X1),X2),X3))=k9_relat_1(k7_relat_1(k7_relat_1(esk3_0,X1),X2),X3)), inference(spm,[status(thm)],[c_0_27, c_0_43])).
% 0.14/0.41  cnf(c_0_51, negated_conjecture, (k9_relat_1(k7_relat_1(k7_relat_1(esk3_0,X1),X2),X3)=k9_relat_1(k7_relat_1(esk3_0,X1),X3)|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_44, c_0_29])).
% 0.14/0.41  cnf(c_0_52, negated_conjecture, (r1_tarski(k1_relat_1(k7_relat_1(esk3_0,X1)),X1)), inference(spm,[status(thm)],[c_0_45, c_0_26])).
% 0.14/0.41  cnf(c_0_53, negated_conjecture, (k9_relat_1(esk3_0,k3_xboole_0(esk1_0,k10_relat_1(esk3_0,esk2_0)))!=k3_xboole_0(k9_relat_1(esk3_0,esk1_0),esk2_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.14/0.41  cnf(c_0_54, plain, (k10_relat_1(k7_relat_1(X1,X2),X3)=k3_xboole_0(X2,k10_relat_1(X1,X3))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.14/0.41  fof(c_0_55, plain, ![X30, X31]:(~v1_relat_1(X31)|~v1_funct_1(X31)|k9_relat_1(X31,k10_relat_1(X31,X30))=k3_xboole_0(X30,k9_relat_1(X31,k1_relat_1(X31)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_funct_1])])).
% 0.14/0.41  fof(c_0_56, plain, ![X25, X26]:((v1_relat_1(k7_relat_1(X25,X26))|(~v1_relat_1(X25)|~v1_funct_1(X25)))&(v1_funct_1(k7_relat_1(X25,X26))|(~v1_relat_1(X25)|~v1_funct_1(X25)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc8_funct_1])])])).
% 0.14/0.41  fof(c_0_57, plain, ![X17]:(~v1_relat_1(X17)|k9_relat_1(X17,k1_relat_1(X17))=k2_relat_1(X17)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_relat_1])])).
% 0.14/0.41  cnf(c_0_58, negated_conjecture, (k9_relat_1(k7_relat_1(k7_relat_1(esk3_0,k1_relat_1(k7_relat_1(esk3_0,X1))),X2),X1)=k9_relat_1(k7_relat_1(esk3_0,X1),X2)), inference(rw,[status(thm)],[c_0_47, c_0_48])).
% 0.14/0.41  cnf(c_0_59, negated_conjecture, (k9_relat_1(k7_relat_1(k7_relat_1(esk3_0,X1),X2),X3)=k9_relat_1(k7_relat_1(k7_relat_1(esk3_0,X3),X1),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_49]), c_0_50]), c_0_48])).
% 0.14/0.41  cnf(c_0_60, negated_conjecture, (k9_relat_1(k7_relat_1(k7_relat_1(esk3_0,X1),X2),k1_relat_1(k7_relat_1(esk3_0,X2)))=k9_relat_1(k7_relat_1(esk3_0,X1),k1_relat_1(k7_relat_1(esk3_0,X2)))), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.14/0.41  cnf(c_0_61, negated_conjecture, (k9_relat_1(esk3_0,k1_setfam_1(k1_enumset1(esk1_0,esk1_0,k10_relat_1(esk3_0,esk2_0))))!=k1_setfam_1(k1_enumset1(k9_relat_1(esk3_0,esk1_0),k9_relat_1(esk3_0,esk1_0),esk2_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53, c_0_24]), c_0_24])).
% 0.14/0.41  cnf(c_0_62, plain, (k10_relat_1(k7_relat_1(X1,X2),X3)=k1_setfam_1(k1_enumset1(X2,X2,k10_relat_1(X1,X3)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_54, c_0_24])).
% 0.14/0.41  cnf(c_0_63, plain, (k9_relat_1(X1,k10_relat_1(X1,X2))=k3_xboole_0(X2,k9_relat_1(X1,k1_relat_1(X1)))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.14/0.41  cnf(c_0_64, plain, (v1_funct_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.14/0.41  cnf(c_0_65, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.14/0.41  cnf(c_0_66, plain, (k9_relat_1(X1,k1_relat_1(X1))=k2_relat_1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.14/0.41  cnf(c_0_67, negated_conjecture, (k9_relat_1(k7_relat_1(esk3_0,X1),k1_relat_1(k7_relat_1(esk3_0,X2)))=k9_relat_1(k7_relat_1(esk3_0,X2),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58, c_0_59]), c_0_60])).
% 0.14/0.41  cnf(c_0_68, negated_conjecture, (k9_relat_1(esk3_0,k1_setfam_1(k1_enumset1(esk1_0,esk1_0,k10_relat_1(esk3_0,esk2_0))))!=k1_setfam_1(k1_enumset1(esk2_0,esk2_0,k9_relat_1(esk3_0,esk1_0)))), inference(rw,[status(thm)],[c_0_61, c_0_38])).
% 0.14/0.41  cnf(c_0_69, negated_conjecture, (k1_setfam_1(k1_enumset1(X1,X1,k10_relat_1(esk3_0,X2)))=k10_relat_1(k7_relat_1(esk3_0,X1),X2)), inference(spm,[status(thm)],[c_0_62, c_0_26])).
% 0.14/0.41  cnf(c_0_70, plain, (k9_relat_1(X1,k10_relat_1(X1,X2))=k1_setfam_1(k1_enumset1(X2,X2,k9_relat_1(X1,k1_relat_1(X1))))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(rw,[status(thm)],[c_0_63, c_0_24])).
% 0.14/0.41  cnf(c_0_71, negated_conjecture, (v1_funct_1(k7_relat_1(esk3_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_26]), c_0_65])])).
% 0.14/0.41  cnf(c_0_72, negated_conjecture, (k9_relat_1(k7_relat_1(esk3_0,X1),k1_relat_1(k7_relat_1(esk3_0,X1)))=k9_relat_1(esk3_0,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_29]), c_0_32])).
% 0.14/0.41  cnf(c_0_73, negated_conjecture, (k9_relat_1(k7_relat_1(k7_relat_1(esk3_0,X1),X2),k1_relat_1(k7_relat_1(esk3_0,X2)))=k9_relat_1(k7_relat_1(esk3_0,X2),X1)), inference(rw,[status(thm)],[c_0_60, c_0_67])).
% 0.14/0.41  cnf(c_0_74, negated_conjecture, (k7_relat_1(k7_relat_1(esk3_0,X1),X2)=k7_relat_1(k7_relat_1(esk3_0,X2),X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_38]), c_0_33])).
% 0.14/0.41  cnf(c_0_75, negated_conjecture, (k1_setfam_1(k1_enumset1(esk2_0,esk2_0,k9_relat_1(esk3_0,esk1_0)))!=k9_relat_1(esk3_0,k10_relat_1(k7_relat_1(esk3_0,esk1_0),esk2_0))), inference(rw,[status(thm)],[c_0_68, c_0_69])).
% 0.14/0.41  cnf(c_0_76, negated_conjecture, (k1_setfam_1(k1_enumset1(X1,X1,k9_relat_1(esk3_0,X2)))=k9_relat_1(k7_relat_1(esk3_0,X2),k10_relat_1(k7_relat_1(esk3_0,X2),X1))), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_29]), c_0_71])]), c_0_72])).
% 0.14/0.41  cnf(c_0_77, negated_conjecture, (k9_relat_1(k7_relat_1(k7_relat_1(esk3_0,X1),X2),k1_relat_1(k7_relat_1(esk3_0,X1)))=k9_relat_1(k7_relat_1(esk3_0,X1),X2)), inference(spm,[status(thm)],[c_0_73, c_0_74])).
% 0.14/0.41  cnf(c_0_78, negated_conjecture, (k7_relat_1(k7_relat_1(esk3_0,X1),k10_relat_1(esk3_0,X2))=k7_relat_1(esk3_0,k10_relat_1(k7_relat_1(esk3_0,X1),X2))), inference(spm,[status(thm)],[c_0_33, c_0_69])).
% 0.14/0.41  cnf(c_0_79, negated_conjecture, (k9_relat_1(k7_relat_1(esk3_0,X1),k10_relat_1(esk3_0,X2))=k9_relat_1(esk3_0,k10_relat_1(k7_relat_1(esk3_0,X1),X2))), inference(spm,[status(thm)],[c_0_37, c_0_69])).
% 0.14/0.41  cnf(c_0_80, negated_conjecture, (k9_relat_1(k7_relat_1(esk3_0,esk1_0),k10_relat_1(k7_relat_1(esk3_0,esk1_0),esk2_0))!=k9_relat_1(esk3_0,k10_relat_1(k7_relat_1(esk3_0,esk1_0),esk2_0))), inference(rw,[status(thm)],[c_0_75, c_0_76])).
% 0.14/0.41  cnf(c_0_81, negated_conjecture, (k9_relat_1(k7_relat_1(esk3_0,X1),k10_relat_1(k7_relat_1(esk3_0,X1),X2))=k9_relat_1(esk3_0,k10_relat_1(k7_relat_1(esk3_0,X1),X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_78]), c_0_67]), c_0_79])).
% 0.14/0.41  cnf(c_0_82, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_80, c_0_81])]), ['proof']).
% 0.14/0.41  # SZS output end CNFRefutation
% 0.14/0.41  # Proof object total steps             : 83
% 0.14/0.41  # Proof object clause steps            : 54
% 0.14/0.41  # Proof object formula steps           : 29
% 0.14/0.41  # Proof object conjectures             : 38
% 0.14/0.41  # Proof object clause conjectures      : 35
% 0.14/0.41  # Proof object formula conjectures     : 3
% 0.14/0.41  # Proof object initial clauses used    : 16
% 0.14/0.41  # Proof object initial formulas used   : 14
% 0.14/0.41  # Proof object generating inferences   : 24
% 0.14/0.41  # Proof object simplifying inferences  : 31
% 0.14/0.41  # Training examples: 0 positive, 0 negative
% 0.14/0.41  # Parsed axioms                        : 14
% 0.14/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.41  # Initial clauses                      : 17
% 0.14/0.41  # Removed in clause preprocessing      : 2
% 0.14/0.41  # Initial clauses in saturation        : 15
% 0.14/0.41  # Processed clauses                    : 251
% 0.14/0.41  # ...of these trivial                  : 52
% 0.14/0.41  # ...subsumed                          : 21
% 0.14/0.41  # ...remaining for further processing  : 178
% 0.14/0.41  # Other redundant clauses eliminated   : 0
% 0.14/0.41  # Clauses deleted for lack of memory   : 0
% 0.14/0.41  # Backward-subsumed                    : 1
% 0.14/0.41  # Backward-rewritten                   : 42
% 0.14/0.41  # Generated clauses                    : 1281
% 0.14/0.41  # ...of the previous two non-trivial   : 897
% 0.14/0.41  # Contextual simplify-reflections      : 0
% 0.14/0.41  # Paramodulations                      : 1281
% 0.14/0.41  # Factorizations                       : 0
% 0.14/0.41  # Equation resolutions                 : 0
% 0.14/0.41  # Propositional unsat checks           : 0
% 0.14/0.41  #    Propositional check models        : 0
% 0.14/0.41  #    Propositional check unsatisfiable : 0
% 0.14/0.41  #    Propositional clauses             : 0
% 0.14/0.41  #    Propositional clauses after purity: 0
% 0.14/0.41  #    Propositional unsat core size     : 0
% 0.14/0.41  #    Propositional preprocessing time  : 0.000
% 0.14/0.41  #    Propositional encoding time       : 0.000
% 0.14/0.41  #    Propositional solver time         : 0.000
% 0.14/0.41  #    Success case prop preproc time    : 0.000
% 0.14/0.41  #    Success case prop encoding time   : 0.000
% 0.14/0.41  #    Success case prop solver time     : 0.000
% 0.14/0.41  # Current number of processed clauses  : 121
% 0.14/0.41  #    Positive orientable unit clauses  : 100
% 0.14/0.41  #    Positive unorientable unit clauses: 7
% 0.14/0.41  #    Negative unit clauses             : 0
% 0.14/0.41  #    Non-unit-clauses                  : 14
% 0.14/0.41  # Current number of unprocessed clauses: 671
% 0.14/0.41  # ...number of literals in the above   : 677
% 0.14/0.41  # Current number of archived formulas  : 0
% 0.14/0.41  # Current number of archived clauses   : 59
% 0.14/0.41  # Clause-clause subsumption calls (NU) : 18
% 0.14/0.41  # Rec. Clause-clause subsumption calls : 18
% 0.14/0.41  # Non-unit clause-clause subsumptions  : 1
% 0.14/0.41  # Unit Clause-clause subsumption calls : 44
% 0.14/0.41  # Rewrite failures with RHS unbound    : 0
% 0.14/0.41  # BW rewrite match attempts            : 925
% 0.14/0.41  # BW rewrite match successes           : 93
% 0.14/0.41  # Condensation attempts                : 0
% 0.14/0.41  # Condensation successes               : 0
% 0.14/0.41  # Termbank termtop insertions          : 26898
% 0.14/0.41  
% 0.14/0.41  # -------------------------------------------------
% 0.14/0.41  # User time                : 0.052 s
% 0.14/0.41  # System time              : 0.006 s
% 0.14/0.41  # Total time               : 0.058 s
% 0.14/0.41  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
