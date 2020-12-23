%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:53:30 EST 2020

% Result     : Theorem 0.61s
% Output     : CNFRefutation 0.61s
% Verified   : 
% Statistics : Number of formulae       :   95 (1888 expanded)
%              Number of clauses        :   60 ( 809 expanded)
%              Number of leaves         :   17 ( 539 expanded)
%              Depth                    :   13
%              Number of atoms          :  155 (3340 expanded)
%              Number of equality atoms :   77 (1157 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t80_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k5_relat_1(X1,k6_relat_1(k2_relat_1(X1))) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

fof(fc3_funct_1,axiom,(
    ! [X1] :
      ( v1_relat_1(k6_relat_1(X1))
      & v1_funct_1(k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(t71_relat_1,axiom,(
    ! [X1] :
      ( k1_relat_1(k6_relat_1(X1)) = X1
      & k2_relat_1(k6_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(t55_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( v1_relat_1(X3)
             => k5_relat_1(k5_relat_1(X1,X2),X3) = k5_relat_1(X1,k5_relat_1(X2,X3)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).

fof(t123_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k8_relat_1(X1,X2) = k5_relat_1(X2,k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(dt_k5_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X2) )
     => v1_relat_1(k5_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(t119_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k2_relat_1(k8_relat_1(X1,X2)) = k3_xboole_0(k2_relat_1(X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t119_relat_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t43_funct_1,conjecture,(
    ! [X1,X2] : k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)) = k6_relat_1(k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

fof(t77_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k1_relat_1(X2),X1)
       => k5_relat_1(k6_relat_1(X1),X2) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).

fof(t45_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => r1_tarski(k2_relat_1(k5_relat_1(X1,X2)),k2_relat_1(X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).

fof(t112_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => k7_relat_1(k5_relat_1(X2,X3),X1) = k5_relat_1(k7_relat_1(X2,X1),X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_relat_1)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(t94_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,X1) = k5_relat_1(k6_relat_1(X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(t90_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k1_relat_1(k7_relat_1(X2,X1)) = k3_xboole_0(k1_relat_1(X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

fof(c_0_17,plain,(
    ! [X35] :
      ( ~ v1_relat_1(X35)
      | k5_relat_1(X35,k6_relat_1(k2_relat_1(X35))) = X35 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t80_relat_1])])).

fof(c_0_18,plain,(
    ! [X40] :
      ( v1_relat_1(k6_relat_1(X40))
      & v1_funct_1(k6_relat_1(X40)) ) ),
    inference(variable_rename,[status(thm)],[fc3_funct_1])).

fof(c_0_19,plain,(
    ! [X29] :
      ( k1_relat_1(k6_relat_1(X29)) = X29
      & k2_relat_1(k6_relat_1(X29)) = X29 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

fof(c_0_20,plain,(
    ! [X26,X27,X28] :
      ( ~ v1_relat_1(X26)
      | ~ v1_relat_1(X27)
      | ~ v1_relat_1(X28)
      | k5_relat_1(k5_relat_1(X26,X27),X28) = k5_relat_1(X26,k5_relat_1(X27,X28)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_relat_1])])])).

cnf(c_0_21,plain,
    ( k5_relat_1(X1,k6_relat_1(k2_relat_1(X1))) = X1
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,plain,
    ( k2_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_24,plain,(
    ! [X22,X23] :
      ( ~ v1_relat_1(X23)
      | k8_relat_1(X22,X23) = k5_relat_1(X23,k6_relat_1(X22)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t123_relat_1])])).

fof(c_0_25,plain,(
    ! [X13,X14] : k1_setfam_1(k2_tarski(X13,X14)) = k3_xboole_0(X13,X14) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_26,plain,(
    ! [X8,X9] : k1_enumset1(X8,X8,X9) = k2_tarski(X8,X9) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

cnf(c_0_27,plain,
    ( k5_relat_1(k5_relat_1(X1,X2),X3) = k5_relat_1(X1,k5_relat_1(X2,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,plain,
    ( k5_relat_1(k6_relat_1(X1),k6_relat_1(X1)) = k6_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23])).

fof(c_0_29,plain,(
    ! [X15,X16] :
      ( ~ v1_relat_1(X15)
      | ~ v1_relat_1(X16)
      | v1_relat_1(k5_relat_1(X15,X16)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_relat_1])])).

cnf(c_0_30,plain,
    ( k8_relat_1(X2,X1) = k5_relat_1(X1,k6_relat_1(X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_31,plain,(
    ! [X20,X21] :
      ( ~ v1_relat_1(X21)
      | k2_relat_1(k8_relat_1(X20,X21)) = k3_xboole_0(k2_relat_1(X21),X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t119_relat_1])])).

cnf(c_0_32,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_33,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_34,plain,(
    ! [X10,X11,X12] : k2_enumset1(X10,X10,X11,X12) = k1_enumset1(X10,X11,X12) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_35,negated_conjecture,(
    ~ ! [X1,X2] : k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)) = k6_relat_1(k3_xboole_0(X1,X2)) ),
    inference(assume_negation,[status(cth)],[t43_funct_1])).

fof(c_0_36,plain,(
    ! [X32,X33] :
      ( ~ v1_relat_1(X33)
      | ~ r1_tarski(k1_relat_1(X33),X32)
      | k5_relat_1(k6_relat_1(X32),X33) = X33 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t77_relat_1])])).

fof(c_0_37,plain,(
    ! [X24,X25] :
      ( ~ v1_relat_1(X24)
      | ~ v1_relat_1(X25)
      | r1_tarski(k2_relat_1(k5_relat_1(X24,X25)),k2_relat_1(X25)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t45_relat_1])])])).

fof(c_0_38,plain,(
    ! [X17,X18,X19] :
      ( ~ v1_relat_1(X18)
      | ~ v1_relat_1(X19)
      | k7_relat_1(k5_relat_1(X18,X19),X17) = k5_relat_1(k7_relat_1(X18,X17),X19) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t112_relat_1])])])).

cnf(c_0_39,plain,
    ( k5_relat_1(k6_relat_1(X1),k5_relat_1(k6_relat_1(X1),X2)) = k5_relat_1(k6_relat_1(X1),X2)
    | ~ v1_relat_1(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_22])])).

cnf(c_0_40,plain,
    ( v1_relat_1(k5_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_41,plain,
    ( k8_relat_1(X1,k6_relat_1(X2)) = k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_22])).

fof(c_0_42,plain,(
    ! [X6,X7] : r1_tarski(k3_xboole_0(X6,X7),X6) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

cnf(c_0_43,plain,
    ( k2_relat_1(k8_relat_1(X2,X1)) = k3_xboole_0(k2_relat_1(X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_44,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_45,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

fof(c_0_46,negated_conjecture,(
    k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0)) != k6_relat_1(k3_xboole_0(esk1_0,esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_35])])])).

cnf(c_0_47,plain,
    ( k5_relat_1(k6_relat_1(X2),X1) = X1
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_48,plain,
    ( k1_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_49,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X1,X2)),k2_relat_1(X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

fof(c_0_50,plain,(
    ! [X38,X39] :
      ( ~ v1_relat_1(X39)
      | k7_relat_1(X39,X38) = k5_relat_1(k6_relat_1(X38),X39) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).

cnf(c_0_51,plain,
    ( k7_relat_1(k5_relat_1(X1,X2),X3) = k5_relat_1(k7_relat_1(X1,X3),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_52,plain,
    ( k5_relat_1(k6_relat_1(X1),k8_relat_1(X2,k6_relat_1(X1))) = k8_relat_1(X2,k6_relat_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_30]),c_0_22]),c_0_22])])).

cnf(c_0_53,plain,
    ( v1_relat_1(k8_relat_1(X1,k6_relat_1(X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_22]),c_0_22])])).

cnf(c_0_54,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_55,plain,
    ( k2_relat_1(k8_relat_1(X2,X1)) = k1_setfam_1(k2_enumset1(k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),X2))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_44]),c_0_45])).

cnf(c_0_56,negated_conjecture,
    ( k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0)) != k6_relat_1(k3_xboole_0(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

fof(c_0_57,plain,(
    ! [X36,X37] :
      ( ~ v1_relat_1(X37)
      | k1_relat_1(k7_relat_1(X37,X36)) = k3_xboole_0(k1_relat_1(X37),X36) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t90_relat_1])])).

cnf(c_0_58,plain,
    ( k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) = k6_relat_1(X2)
    | ~ r1_tarski(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_22])])).

cnf(c_0_59,plain,
    ( r1_tarski(k2_relat_1(k8_relat_1(X1,k6_relat_1(X2))),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_41]),c_0_23]),c_0_22]),c_0_22])])).

cnf(c_0_60,plain,
    ( k7_relat_1(X1,X2) = k5_relat_1(k6_relat_1(X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_61,plain,
    ( k7_relat_1(k8_relat_1(X1,k6_relat_1(X2)),X3) = k5_relat_1(k7_relat_1(k6_relat_1(X2),X3),k8_relat_1(X1,k6_relat_1(X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_53]),c_0_22])])).

cnf(c_0_62,plain,
    ( r1_tarski(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54,c_0_44]),c_0_45])).

cnf(c_0_63,plain,
    ( k1_setfam_1(k2_enumset1(X1,X1,X1,X2)) = k2_relat_1(k8_relat_1(X2,k6_relat_1(X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_23]),c_0_22])])).

cnf(c_0_64,negated_conjecture,
    ( k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0)) != k6_relat_1(k1_setfam_1(k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_44]),c_0_45])).

cnf(c_0_65,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = k3_xboole_0(k1_relat_1(X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_66,plain,
    ( k6_relat_1(k2_relat_1(k8_relat_1(X1,k6_relat_1(X2)))) = k8_relat_1(k2_relat_1(k8_relat_1(X1,k6_relat_1(X2))),k6_relat_1(X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_41])).

cnf(c_0_67,plain,
    ( k5_relat_1(k7_relat_1(k6_relat_1(X1),X2),k8_relat_1(X3,k6_relat_1(X1))) = k5_relat_1(k6_relat_1(X2),k8_relat_1(X3,k6_relat_1(X1))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_53]),c_0_61])).

cnf(c_0_68,plain,
    ( k8_relat_1(X1,k6_relat_1(X2)) = k7_relat_1(k6_relat_1(X1),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_60]),c_0_22]),c_0_22])])).

cnf(c_0_69,plain,
    ( r1_tarski(k2_relat_1(k8_relat_1(X1,k6_relat_1(X2))),X2) ),
    inference(rw,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_70,plain,
    ( v1_relat_1(k8_relat_1(X1,X2))
    | ~ v1_relat_1(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_30]),c_0_22])])).

cnf(c_0_71,negated_conjecture,
    ( k6_relat_1(k1_setfam_1(k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0))) != k8_relat_1(esk1_0,k6_relat_1(esk2_0)) ),
    inference(rw,[status(thm)],[c_0_64,c_0_41])).

cnf(c_0_72,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = k1_setfam_1(k2_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X2))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_65,c_0_44]),c_0_45])).

cnf(c_0_73,plain,
    ( k5_relat_1(k8_relat_1(X1,k6_relat_1(X2)),k8_relat_1(k2_relat_1(k8_relat_1(X1,k6_relat_1(X2))),k6_relat_1(X1))) = k8_relat_1(X1,k6_relat_1(X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_53]),c_0_66])).

cnf(c_0_74,plain,
    ( k5_relat_1(k8_relat_1(X1,k6_relat_1(X2)),k8_relat_1(X3,k6_relat_1(X1))) = k5_relat_1(k6_relat_1(X2),k8_relat_1(X3,k6_relat_1(X1))) ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_75,plain,
    ( k5_relat_1(k6_relat_1(X1),k8_relat_1(k2_relat_1(k8_relat_1(X2,k6_relat_1(X1))),k6_relat_1(X2))) = k8_relat_1(k2_relat_1(k8_relat_1(X2,k6_relat_1(X1))),k6_relat_1(X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_69]),c_0_66]),c_0_66])).

cnf(c_0_76,plain,
    ( k7_relat_1(k5_relat_1(k6_relat_1(X1),X2),X3) = k5_relat_1(k7_relat_1(k6_relat_1(X1),X3),X2)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_51,c_0_22])).

cnf(c_0_77,plain,
    ( v1_relat_1(k5_relat_1(X1,k6_relat_1(X2)))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_70,c_0_30])).

cnf(c_0_78,negated_conjecture,
    ( k6_relat_1(k2_relat_1(k5_relat_1(k6_relat_1(esk1_0),k6_relat_1(esk2_0)))) != k8_relat_1(esk1_0,k6_relat_1(esk2_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_71,c_0_63]),c_0_41])).

cnf(c_0_79,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = k2_relat_1(k8_relat_1(X2,k6_relat_1(k1_relat_1(X1))))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_72,c_0_63])).

cnf(c_0_80,plain,
    ( k8_relat_1(k2_relat_1(k8_relat_1(X1,k6_relat_1(X2))),k6_relat_1(X1)) = k8_relat_1(X1,k6_relat_1(X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_73,c_0_74]),c_0_75])).

cnf(c_0_81,plain,
    ( k5_relat_1(k7_relat_1(k6_relat_1(X1),X2),k8_relat_1(X3,k6_relat_1(X1))) = k5_relat_1(k7_relat_1(k6_relat_1(X1),X2),k6_relat_1(X3)) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_30]),c_0_22]),c_0_22])]),c_0_61])).

cnf(c_0_82,plain,
    ( v1_relat_1(k7_relat_1(k6_relat_1(X1),X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_60]),c_0_22]),c_0_22])])).

cnf(c_0_83,negated_conjecture,
    ( k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(esk2_0),esk1_0))) != k8_relat_1(esk1_0,k6_relat_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_60]),c_0_22])])).

cnf(c_0_84,plain,
    ( k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X1),X2))) = k8_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X1),X2)),k6_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_66,c_0_68])).

cnf(c_0_85,plain,
    ( k1_relat_1(k8_relat_1(X1,k6_relat_1(X2))) = k2_relat_1(k8_relat_1(X2,k6_relat_1(X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_68]),c_0_48]),c_0_22])])).

cnf(c_0_86,plain,
    ( k8_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X1),X2)),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_80,c_0_68])).

cnf(c_0_87,plain,
    ( k1_relat_1(k7_relat_1(k6_relat_1(X1),X2)) = k2_relat_1(k8_relat_1(X2,k6_relat_1(X1))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_22]),c_0_48])).

cnf(c_0_88,plain,
    ( k8_relat_1(X1,k7_relat_1(k6_relat_1(X2),X3)) = k5_relat_1(k7_relat_1(k6_relat_1(X2),X3),k8_relat_1(X1,k6_relat_1(X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_81]),c_0_82])])).

cnf(c_0_89,plain,
    ( k5_relat_1(k7_relat_1(k6_relat_1(X1),X2),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_28]),c_0_22])])).

cnf(c_0_90,negated_conjecture,
    ( k8_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(esk2_0),esk1_0)),k6_relat_1(esk2_0)) != k8_relat_1(esk1_0,k6_relat_1(esk2_0)) ),
    inference(rw,[status(thm)],[c_0_83,c_0_84])).

cnf(c_0_91,plain,
    ( k2_relat_1(k7_relat_1(k6_relat_1(X1),X2)) = k2_relat_1(k8_relat_1(X2,k6_relat_1(X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_86]),c_0_87]),c_0_84]),c_0_86]),c_0_88]),c_0_41]),c_0_28]),c_0_89])).

cnf(c_0_92,negated_conjecture,
    ( k7_relat_1(k6_relat_1(esk2_0),esk1_0) != k8_relat_1(esk1_0,k6_relat_1(esk2_0)) ),
    inference(rw,[status(thm)],[c_0_90,c_0_86])).

cnf(c_0_93,plain,
    ( k7_relat_1(k6_relat_1(X1),X2) = k8_relat_1(X2,k6_relat_1(X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_84,c_0_86]),c_0_91]),c_0_66]),c_0_80])).

cnf(c_0_94,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_92,c_0_93])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:23:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.61/0.81  # AutoSched0-Mode selected heuristic H_____042_B03_F1_AE_Q4_SP_S2S
% 0.61/0.81  # and selection function SelectNewComplexAHP.
% 0.61/0.81  #
% 0.61/0.81  # Preprocessing time       : 0.027 s
% 0.61/0.81  
% 0.61/0.81  # Proof found!
% 0.61/0.81  # SZS status Theorem
% 0.61/0.81  # SZS output start CNFRefutation
% 0.61/0.81  fof(t80_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k5_relat_1(X1,k6_relat_1(k2_relat_1(X1)))=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_relat_1)).
% 0.61/0.81  fof(fc3_funct_1, axiom, ![X1]:(v1_relat_1(k6_relat_1(X1))&v1_funct_1(k6_relat_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 0.61/0.81  fof(t71_relat_1, axiom, ![X1]:(k1_relat_1(k6_relat_1(X1))=X1&k2_relat_1(k6_relat_1(X1))=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 0.61/0.81  fof(t55_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>k5_relat_1(k5_relat_1(X1,X2),X3)=k5_relat_1(X1,k5_relat_1(X2,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_relat_1)).
% 0.61/0.81  fof(t123_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k8_relat_1(X1,X2)=k5_relat_1(X2,k6_relat_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_relat_1)).
% 0.61/0.81  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.61/0.81  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.61/0.81  fof(dt_k5_relat_1, axiom, ![X1, X2]:((v1_relat_1(X1)&v1_relat_1(X2))=>v1_relat_1(k5_relat_1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 0.61/0.81  fof(t119_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k2_relat_1(k8_relat_1(X1,X2))=k3_xboole_0(k2_relat_1(X2),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t119_relat_1)).
% 0.61/0.81  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.61/0.81  fof(t43_funct_1, conjecture, ![X1, X2]:k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))=k6_relat_1(k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_funct_1)).
% 0.61/0.81  fof(t77_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k1_relat_1(X2),X1)=>k5_relat_1(k6_relat_1(X1),X2)=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_relat_1)).
% 0.61/0.81  fof(t45_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>r1_tarski(k2_relat_1(k5_relat_1(X1,X2)),k2_relat_1(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_relat_1)).
% 0.61/0.81  fof(t112_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>k7_relat_1(k5_relat_1(X2,X3),X1)=k5_relat_1(k7_relat_1(X2,X1),X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t112_relat_1)).
% 0.61/0.81  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 0.61/0.81  fof(t94_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k7_relat_1(X2,X1)=k5_relat_1(k6_relat_1(X1),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 0.61/0.81  fof(t90_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k1_relat_1(k7_relat_1(X2,X1))=k3_xboole_0(k1_relat_1(X2),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_relat_1)).
% 0.61/0.81  fof(c_0_17, plain, ![X35]:(~v1_relat_1(X35)|k5_relat_1(X35,k6_relat_1(k2_relat_1(X35)))=X35), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t80_relat_1])])).
% 0.61/0.81  fof(c_0_18, plain, ![X40]:(v1_relat_1(k6_relat_1(X40))&v1_funct_1(k6_relat_1(X40))), inference(variable_rename,[status(thm)],[fc3_funct_1])).
% 0.61/0.81  fof(c_0_19, plain, ![X29]:(k1_relat_1(k6_relat_1(X29))=X29&k2_relat_1(k6_relat_1(X29))=X29), inference(variable_rename,[status(thm)],[t71_relat_1])).
% 0.61/0.81  fof(c_0_20, plain, ![X26, X27, X28]:(~v1_relat_1(X26)|(~v1_relat_1(X27)|(~v1_relat_1(X28)|k5_relat_1(k5_relat_1(X26,X27),X28)=k5_relat_1(X26,k5_relat_1(X27,X28))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_relat_1])])])).
% 0.61/0.81  cnf(c_0_21, plain, (k5_relat_1(X1,k6_relat_1(k2_relat_1(X1)))=X1|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.61/0.81  cnf(c_0_22, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.61/0.81  cnf(c_0_23, plain, (k2_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.61/0.81  fof(c_0_24, plain, ![X22, X23]:(~v1_relat_1(X23)|k8_relat_1(X22,X23)=k5_relat_1(X23,k6_relat_1(X22))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t123_relat_1])])).
% 0.61/0.81  fof(c_0_25, plain, ![X13, X14]:k1_setfam_1(k2_tarski(X13,X14))=k3_xboole_0(X13,X14), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.61/0.81  fof(c_0_26, plain, ![X8, X9]:k1_enumset1(X8,X8,X9)=k2_tarski(X8,X9), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.61/0.81  cnf(c_0_27, plain, (k5_relat_1(k5_relat_1(X1,X2),X3)=k5_relat_1(X1,k5_relat_1(X2,X3))|~v1_relat_1(X1)|~v1_relat_1(X2)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.61/0.81  cnf(c_0_28, plain, (k5_relat_1(k6_relat_1(X1),k6_relat_1(X1))=k6_relat_1(X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_23])).
% 0.61/0.81  fof(c_0_29, plain, ![X15, X16]:(~v1_relat_1(X15)|~v1_relat_1(X16)|v1_relat_1(k5_relat_1(X15,X16))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_relat_1])])).
% 0.61/0.81  cnf(c_0_30, plain, (k8_relat_1(X2,X1)=k5_relat_1(X1,k6_relat_1(X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.61/0.81  fof(c_0_31, plain, ![X20, X21]:(~v1_relat_1(X21)|k2_relat_1(k8_relat_1(X20,X21))=k3_xboole_0(k2_relat_1(X21),X20)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t119_relat_1])])).
% 0.61/0.81  cnf(c_0_32, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.61/0.81  cnf(c_0_33, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.61/0.81  fof(c_0_34, plain, ![X10, X11, X12]:k2_enumset1(X10,X10,X11,X12)=k1_enumset1(X10,X11,X12), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.61/0.81  fof(c_0_35, negated_conjecture, ~(![X1, X2]:k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))=k6_relat_1(k3_xboole_0(X1,X2))), inference(assume_negation,[status(cth)],[t43_funct_1])).
% 0.61/0.81  fof(c_0_36, plain, ![X32, X33]:(~v1_relat_1(X33)|(~r1_tarski(k1_relat_1(X33),X32)|k5_relat_1(k6_relat_1(X32),X33)=X33)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t77_relat_1])])).
% 0.61/0.81  fof(c_0_37, plain, ![X24, X25]:(~v1_relat_1(X24)|(~v1_relat_1(X25)|r1_tarski(k2_relat_1(k5_relat_1(X24,X25)),k2_relat_1(X25)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t45_relat_1])])])).
% 0.61/0.81  fof(c_0_38, plain, ![X17, X18, X19]:(~v1_relat_1(X18)|(~v1_relat_1(X19)|k7_relat_1(k5_relat_1(X18,X19),X17)=k5_relat_1(k7_relat_1(X18,X17),X19))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t112_relat_1])])])).
% 0.61/0.81  cnf(c_0_39, plain, (k5_relat_1(k6_relat_1(X1),k5_relat_1(k6_relat_1(X1),X2))=k5_relat_1(k6_relat_1(X1),X2)|~v1_relat_1(X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_22])])).
% 0.61/0.81  cnf(c_0_40, plain, (v1_relat_1(k5_relat_1(X1,X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.61/0.81  cnf(c_0_41, plain, (k8_relat_1(X1,k6_relat_1(X2))=k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))), inference(spm,[status(thm)],[c_0_30, c_0_22])).
% 0.61/0.81  fof(c_0_42, plain, ![X6, X7]:r1_tarski(k3_xboole_0(X6,X7),X6), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 0.61/0.81  cnf(c_0_43, plain, (k2_relat_1(k8_relat_1(X2,X1))=k3_xboole_0(k2_relat_1(X1),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.61/0.81  cnf(c_0_44, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_32, c_0_33])).
% 0.61/0.81  cnf(c_0_45, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.61/0.81  fof(c_0_46, negated_conjecture, k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0))!=k6_relat_1(k3_xboole_0(esk1_0,esk2_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_35])])])).
% 0.61/0.81  cnf(c_0_47, plain, (k5_relat_1(k6_relat_1(X2),X1)=X1|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.61/0.81  cnf(c_0_48, plain, (k1_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.61/0.81  cnf(c_0_49, plain, (r1_tarski(k2_relat_1(k5_relat_1(X1,X2)),k2_relat_1(X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.61/0.81  fof(c_0_50, plain, ![X38, X39]:(~v1_relat_1(X39)|k7_relat_1(X39,X38)=k5_relat_1(k6_relat_1(X38),X39)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).
% 0.61/0.81  cnf(c_0_51, plain, (k7_relat_1(k5_relat_1(X1,X2),X3)=k5_relat_1(k7_relat_1(X1,X3),X2)|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.61/0.81  cnf(c_0_52, plain, (k5_relat_1(k6_relat_1(X1),k8_relat_1(X2,k6_relat_1(X1)))=k8_relat_1(X2,k6_relat_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_30]), c_0_22]), c_0_22])])).
% 0.61/0.81  cnf(c_0_53, plain, (v1_relat_1(k8_relat_1(X1,k6_relat_1(X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_22]), c_0_22])])).
% 0.61/0.81  cnf(c_0_54, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.61/0.81  cnf(c_0_55, plain, (k2_relat_1(k8_relat_1(X2,X1))=k1_setfam_1(k2_enumset1(k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),X2))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43, c_0_44]), c_0_45])).
% 0.61/0.81  cnf(c_0_56, negated_conjecture, (k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0))!=k6_relat_1(k3_xboole_0(esk1_0,esk2_0))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.61/0.81  fof(c_0_57, plain, ![X36, X37]:(~v1_relat_1(X37)|k1_relat_1(k7_relat_1(X37,X36))=k3_xboole_0(k1_relat_1(X37),X36)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t90_relat_1])])).
% 0.61/0.81  cnf(c_0_58, plain, (k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))=k6_relat_1(X2)|~r1_tarski(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_22])])).
% 0.61/0.81  cnf(c_0_59, plain, (r1_tarski(k2_relat_1(k8_relat_1(X1,k6_relat_1(X2))),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_41]), c_0_23]), c_0_22]), c_0_22])])).
% 0.61/0.81  cnf(c_0_60, plain, (k7_relat_1(X1,X2)=k5_relat_1(k6_relat_1(X2),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.61/0.81  cnf(c_0_61, plain, (k7_relat_1(k8_relat_1(X1,k6_relat_1(X2)),X3)=k5_relat_1(k7_relat_1(k6_relat_1(X2),X3),k8_relat_1(X1,k6_relat_1(X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_53]), c_0_22])])).
% 0.61/0.81  cnf(c_0_62, plain, (r1_tarski(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54, c_0_44]), c_0_45])).
% 0.61/0.81  cnf(c_0_63, plain, (k1_setfam_1(k2_enumset1(X1,X1,X1,X2))=k2_relat_1(k8_relat_1(X2,k6_relat_1(X1)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_23]), c_0_22])])).
% 0.61/0.81  cnf(c_0_64, negated_conjecture, (k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0))!=k6_relat_1(k1_setfam_1(k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56, c_0_44]), c_0_45])).
% 0.61/0.81  cnf(c_0_65, plain, (k1_relat_1(k7_relat_1(X1,X2))=k3_xboole_0(k1_relat_1(X1),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.61/0.81  cnf(c_0_66, plain, (k6_relat_1(k2_relat_1(k8_relat_1(X1,k6_relat_1(X2))))=k8_relat_1(k2_relat_1(k8_relat_1(X1,k6_relat_1(X2))),k6_relat_1(X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_41])).
% 0.61/0.81  cnf(c_0_67, plain, (k5_relat_1(k7_relat_1(k6_relat_1(X1),X2),k8_relat_1(X3,k6_relat_1(X1)))=k5_relat_1(k6_relat_1(X2),k8_relat_1(X3,k6_relat_1(X1)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_53]), c_0_61])).
% 0.61/0.81  cnf(c_0_68, plain, (k8_relat_1(X1,k6_relat_1(X2))=k7_relat_1(k6_relat_1(X1),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_60]), c_0_22]), c_0_22])])).
% 0.61/0.81  cnf(c_0_69, plain, (r1_tarski(k2_relat_1(k8_relat_1(X1,k6_relat_1(X2))),X2)), inference(rw,[status(thm)],[c_0_62, c_0_63])).
% 0.61/0.81  cnf(c_0_70, plain, (v1_relat_1(k8_relat_1(X1,X2))|~v1_relat_1(X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_30]), c_0_22])])).
% 0.61/0.81  cnf(c_0_71, negated_conjecture, (k6_relat_1(k1_setfam_1(k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0)))!=k8_relat_1(esk1_0,k6_relat_1(esk2_0))), inference(rw,[status(thm)],[c_0_64, c_0_41])).
% 0.61/0.81  cnf(c_0_72, plain, (k1_relat_1(k7_relat_1(X1,X2))=k1_setfam_1(k2_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X2))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_65, c_0_44]), c_0_45])).
% 0.61/0.81  cnf(c_0_73, plain, (k5_relat_1(k8_relat_1(X1,k6_relat_1(X2)),k8_relat_1(k2_relat_1(k8_relat_1(X1,k6_relat_1(X2))),k6_relat_1(X1)))=k8_relat_1(X1,k6_relat_1(X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_53]), c_0_66])).
% 0.61/0.81  cnf(c_0_74, plain, (k5_relat_1(k8_relat_1(X1,k6_relat_1(X2)),k8_relat_1(X3,k6_relat_1(X1)))=k5_relat_1(k6_relat_1(X2),k8_relat_1(X3,k6_relat_1(X1)))), inference(spm,[status(thm)],[c_0_67, c_0_68])).
% 0.61/0.81  cnf(c_0_75, plain, (k5_relat_1(k6_relat_1(X1),k8_relat_1(k2_relat_1(k8_relat_1(X2,k6_relat_1(X1))),k6_relat_1(X2)))=k8_relat_1(k2_relat_1(k8_relat_1(X2,k6_relat_1(X1))),k6_relat_1(X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_69]), c_0_66]), c_0_66])).
% 0.61/0.81  cnf(c_0_76, plain, (k7_relat_1(k5_relat_1(k6_relat_1(X1),X2),X3)=k5_relat_1(k7_relat_1(k6_relat_1(X1),X3),X2)|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_51, c_0_22])).
% 0.61/0.81  cnf(c_0_77, plain, (v1_relat_1(k5_relat_1(X1,k6_relat_1(X2)))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_70, c_0_30])).
% 0.61/0.81  cnf(c_0_78, negated_conjecture, (k6_relat_1(k2_relat_1(k5_relat_1(k6_relat_1(esk1_0),k6_relat_1(esk2_0))))!=k8_relat_1(esk1_0,k6_relat_1(esk2_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_71, c_0_63]), c_0_41])).
% 0.61/0.81  cnf(c_0_79, plain, (k1_relat_1(k7_relat_1(X1,X2))=k2_relat_1(k8_relat_1(X2,k6_relat_1(k1_relat_1(X1))))|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_72, c_0_63])).
% 0.61/0.81  cnf(c_0_80, plain, (k8_relat_1(k2_relat_1(k8_relat_1(X1,k6_relat_1(X2))),k6_relat_1(X1))=k8_relat_1(X1,k6_relat_1(X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_73, c_0_74]), c_0_75])).
% 0.61/0.81  cnf(c_0_81, plain, (k5_relat_1(k7_relat_1(k6_relat_1(X1),X2),k8_relat_1(X3,k6_relat_1(X1)))=k5_relat_1(k7_relat_1(k6_relat_1(X1),X2),k6_relat_1(X3))), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_30]), c_0_22]), c_0_22])]), c_0_61])).
% 0.61/0.81  cnf(c_0_82, plain, (v1_relat_1(k7_relat_1(k6_relat_1(X1),X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_60]), c_0_22]), c_0_22])])).
% 0.61/0.81  cnf(c_0_83, negated_conjecture, (k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(esk2_0),esk1_0)))!=k8_relat_1(esk1_0,k6_relat_1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_60]), c_0_22])])).
% 0.61/0.81  cnf(c_0_84, plain, (k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X1),X2)))=k8_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X1),X2)),k6_relat_1(X1))), inference(spm,[status(thm)],[c_0_66, c_0_68])).
% 0.61/0.81  cnf(c_0_85, plain, (k1_relat_1(k8_relat_1(X1,k6_relat_1(X2)))=k2_relat_1(k8_relat_1(X2,k6_relat_1(X1)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_68]), c_0_48]), c_0_22])])).
% 0.61/0.81  cnf(c_0_86, plain, (k8_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X1),X2)),k6_relat_1(X1))=k7_relat_1(k6_relat_1(X1),X2)), inference(spm,[status(thm)],[c_0_80, c_0_68])).
% 0.61/0.81  cnf(c_0_87, plain, (k1_relat_1(k7_relat_1(k6_relat_1(X1),X2))=k2_relat_1(k8_relat_1(X2,k6_relat_1(X1)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_22]), c_0_48])).
% 0.61/0.81  cnf(c_0_88, plain, (k8_relat_1(X1,k7_relat_1(k6_relat_1(X2),X3))=k5_relat_1(k7_relat_1(k6_relat_1(X2),X3),k8_relat_1(X1,k6_relat_1(X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_81]), c_0_82])])).
% 0.61/0.81  cnf(c_0_89, plain, (k5_relat_1(k7_relat_1(k6_relat_1(X1),X2),k6_relat_1(X1))=k7_relat_1(k6_relat_1(X1),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_28]), c_0_22])])).
% 0.61/0.81  cnf(c_0_90, negated_conjecture, (k8_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(esk2_0),esk1_0)),k6_relat_1(esk2_0))!=k8_relat_1(esk1_0,k6_relat_1(esk2_0))), inference(rw,[status(thm)],[c_0_83, c_0_84])).
% 0.61/0.81  cnf(c_0_91, plain, (k2_relat_1(k7_relat_1(k6_relat_1(X1),X2))=k2_relat_1(k8_relat_1(X2,k6_relat_1(X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_86]), c_0_87]), c_0_84]), c_0_86]), c_0_88]), c_0_41]), c_0_28]), c_0_89])).
% 0.61/0.81  cnf(c_0_92, negated_conjecture, (k7_relat_1(k6_relat_1(esk2_0),esk1_0)!=k8_relat_1(esk1_0,k6_relat_1(esk2_0))), inference(rw,[status(thm)],[c_0_90, c_0_86])).
% 0.61/0.81  cnf(c_0_93, plain, (k7_relat_1(k6_relat_1(X1),X2)=k8_relat_1(X2,k6_relat_1(X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_84, c_0_86]), c_0_91]), c_0_66]), c_0_80])).
% 0.61/0.81  cnf(c_0_94, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_92, c_0_93])]), ['proof']).
% 0.61/0.81  # SZS output end CNFRefutation
% 0.61/0.81  # Proof object total steps             : 95
% 0.61/0.81  # Proof object clause steps            : 60
% 0.61/0.81  # Proof object formula steps           : 35
% 0.61/0.81  # Proof object conjectures             : 11
% 0.61/0.81  # Proof object clause conjectures      : 8
% 0.61/0.81  # Proof object formula conjectures     : 3
% 0.61/0.81  # Proof object initial clauses used    : 18
% 0.61/0.81  # Proof object initial formulas used   : 17
% 0.61/0.81  # Proof object generating inferences   : 28
% 0.61/0.81  # Proof object simplifying inferences  : 78
% 0.61/0.81  # Training examples: 0 positive, 0 negative
% 0.61/0.81  # Parsed axioms                        : 20
% 0.61/0.81  # Removed by relevancy pruning/SinE    : 0
% 0.61/0.81  # Initial clauses                      : 25
% 0.61/0.81  # Removed in clause preprocessing      : 3
% 0.61/0.81  # Initial clauses in saturation        : 22
% 0.61/0.81  # Processed clauses                    : 2031
% 0.61/0.81  # ...of these trivial                  : 380
% 0.61/0.81  # ...subsumed                          : 1021
% 0.61/0.81  # ...remaining for further processing  : 630
% 0.61/0.81  # Other redundant clauses eliminated   : 2
% 0.61/0.81  # Clauses deleted for lack of memory   : 0
% 0.61/0.81  # Backward-subsumed                    : 69
% 0.61/0.81  # Backward-rewritten                   : 213
% 0.61/0.81  # Generated clauses                    : 50222
% 0.61/0.81  # ...of the previous two non-trivial   : 47073
% 0.61/0.81  # Contextual simplify-reflections      : 0
% 0.61/0.81  # Paramodulations                      : 50220
% 0.61/0.81  # Factorizations                       : 0
% 0.61/0.81  # Equation resolutions                 : 2
% 0.61/0.81  # Propositional unsat checks           : 0
% 0.61/0.81  #    Propositional check models        : 0
% 0.61/0.81  #    Propositional check unsatisfiable : 0
% 0.61/0.81  #    Propositional clauses             : 0
% 0.61/0.81  #    Propositional clauses after purity: 0
% 0.61/0.81  #    Propositional unsat core size     : 0
% 0.61/0.81  #    Propositional preprocessing time  : 0.000
% 0.61/0.81  #    Propositional encoding time       : 0.000
% 0.61/0.81  #    Propositional solver time         : 0.000
% 0.61/0.81  #    Success case prop preproc time    : 0.000
% 0.61/0.81  #    Success case prop encoding time   : 0.000
% 0.61/0.81  #    Success case prop solver time     : 0.000
% 0.61/0.81  # Current number of processed clauses  : 346
% 0.61/0.81  #    Positive orientable unit clauses  : 95
% 0.61/0.81  #    Positive unorientable unit clauses: 3
% 0.61/0.81  #    Negative unit clauses             : 0
% 0.61/0.81  #    Non-unit-clauses                  : 248
% 0.61/0.81  # Current number of unprocessed clauses: 44756
% 0.61/0.81  # ...number of literals in the above   : 96567
% 0.61/0.81  # Current number of archived formulas  : 0
% 0.61/0.81  # Current number of archived clauses   : 285
% 0.61/0.81  # Clause-clause subsumption calls (NU) : 23583
% 0.61/0.81  # Rec. Clause-clause subsumption calls : 18254
% 0.61/0.81  # Non-unit clause-clause subsumptions  : 1057
% 0.61/0.81  # Unit Clause-clause subsumption calls : 1116
% 0.61/0.81  # Rewrite failures with RHS unbound    : 0
% 0.61/0.81  # BW rewrite match attempts            : 705
% 0.61/0.81  # BW rewrite match successes           : 195
% 0.61/0.81  # Condensation attempts                : 0
% 0.61/0.81  # Condensation successes               : 0
% 0.61/0.81  # Termbank termtop insertions          : 838680
% 0.61/0.82  
% 0.61/0.82  # -------------------------------------------------
% 0.61/0.82  # User time                : 0.445 s
% 0.61/0.82  # System time              : 0.030 s
% 0.61/0.82  # Total time               : 0.476 s
% 0.61/0.82  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
