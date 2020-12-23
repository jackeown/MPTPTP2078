%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:53:34 EST 2020

% Result     : Theorem 0.70s
% Output     : CNFRefutation 0.70s
% Verified   : 
% Statistics : Number of formulae       :  118 (4479 expanded)
%              Number of clauses        :   81 (1870 expanded)
%              Number of leaves         :   18 (1304 expanded)
%              Depth                    :   16
%              Number of atoms          :  191 (9208 expanded)
%              Number of equality atoms :   90 (2286 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    8 (   1 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t94_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,X1) = k5_relat_1(k6_relat_1(X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(fc24_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(k6_relat_1(X1))
      & v4_relat_1(k6_relat_1(X1),X1)
      & v5_relat_1(k6_relat_1(X1),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc24_relat_1)).

fof(dt_k5_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X2) )
     => v1_relat_1(k5_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(t54_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k4_relat_1(k5_relat_1(X1,X2)) = k5_relat_1(k4_relat_1(X2),k4_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relat_1)).

fof(t123_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k8_relat_1(X1,X2) = k5_relat_1(X2,k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

fof(t72_relat_1,axiom,(
    ! [X1] : k4_relat_1(k6_relat_1(X1)) = k6_relat_1(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_relat_1)).

fof(t140_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => k7_relat_1(k8_relat_1(X1,X3),X2) = k8_relat_1(X1,k7_relat_1(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t140_relat_1)).

fof(t88_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k7_relat_1(X2,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).

fof(t98_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,k1_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).

fof(t71_relat_1,axiom,(
    ! [X1] :
      ( k1_relat_1(k6_relat_1(X1)) = X1
      & k2_relat_1(k6_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t100_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => k7_relat_1(k7_relat_1(X3,X1),X2) = k7_relat_1(X3,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t125_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k2_relat_1(X2),X1)
       => k8_relat_1(X1,X2) = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).

fof(t25_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => ( r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
              & r1_tarski(k2_relat_1(X1),k2_relat_1(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

fof(t103_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r1_tarski(X1,X2)
       => k7_relat_1(k7_relat_1(X3,X2),X1) = k7_relat_1(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_relat_1)).

fof(t43_funct_1,conjecture,(
    ! [X1,X2] : k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)) = k6_relat_1(k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

fof(c_0_18,plain,(
    ! [X38,X39] :
      ( ~ v1_relat_1(X39)
      | k7_relat_1(X39,X38) = k5_relat_1(k6_relat_1(X38),X39) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).

fof(c_0_19,plain,(
    ! [X41] :
      ( v1_relat_1(k6_relat_1(X41))
      & v4_relat_1(k6_relat_1(X41),X41)
      & v5_relat_1(k6_relat_1(X41),X41) ) ),
    inference(variable_rename,[status(thm)],[fc24_relat_1])).

fof(c_0_20,plain,(
    ! [X11,X12] :
      ( ~ v1_relat_1(X11)
      | ~ v1_relat_1(X12)
      | v1_relat_1(k5_relat_1(X11,X12)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_relat_1])])).

cnf(c_0_21,plain,
    ( k7_relat_1(X1,X2) = k5_relat_1(k6_relat_1(X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_22,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_23,plain,(
    ! [X28,X29] :
      ( ~ v1_relat_1(X28)
      | ~ v1_relat_1(X29)
      | k4_relat_1(k5_relat_1(X28,X29)) = k5_relat_1(k4_relat_1(X29),k4_relat_1(X28)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t54_relat_1])])])).

fof(c_0_24,plain,(
    ! [X19,X20] :
      ( ~ v1_relat_1(X20)
      | k8_relat_1(X19,X20) = k5_relat_1(X20,k6_relat_1(X19)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t123_relat_1])])).

fof(c_0_25,plain,(
    ! [X34] : k4_relat_1(k6_relat_1(X34)) = k6_relat_1(X34) ),
    inference(variable_rename,[status(thm)],[t72_relat_1])).

fof(c_0_26,plain,(
    ! [X23,X24,X25] :
      ( ~ v1_relat_1(X25)
      | k7_relat_1(k8_relat_1(X23,X25),X24) = k8_relat_1(X23,k7_relat_1(X25,X24)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t140_relat_1])])).

cnf(c_0_27,plain,
    ( v1_relat_1(k5_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,plain,
    ( k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) = k7_relat_1(k6_relat_1(X2),X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_29,plain,
    ( k4_relat_1(k5_relat_1(X1,X2)) = k5_relat_1(k4_relat_1(X2),k4_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,plain,
    ( k8_relat_1(X2,X1) = k5_relat_1(X1,k6_relat_1(X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,plain,
    ( k4_relat_1(k6_relat_1(X1)) = k6_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_32,plain,
    ( k7_relat_1(k8_relat_1(X2,X1),X3) = k8_relat_1(X2,k7_relat_1(X1,X3))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_33,plain,
    ( v1_relat_1(k7_relat_1(k6_relat_1(X1),X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_22]),c_0_22])])).

fof(c_0_34,plain,(
    ! [X36,X37] :
      ( ~ v1_relat_1(X37)
      | r1_tarski(k7_relat_1(X37,X36),X37) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t88_relat_1])])).

fof(c_0_35,plain,(
    ! [X40] :
      ( ~ v1_relat_1(X40)
      | k7_relat_1(X40,k1_relat_1(X40)) = X40 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t98_relat_1])])).

fof(c_0_36,plain,(
    ! [X33] :
      ( k1_relat_1(k6_relat_1(X33)) = X33
      & k2_relat_1(k6_relat_1(X33)) = X33 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

fof(c_0_37,plain,(
    ! [X9,X10] : k1_setfam_1(k2_tarski(X9,X10)) = k3_xboole_0(X9,X10) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_38,plain,(
    ! [X4,X5] : k1_enumset1(X4,X4,X5) = k2_tarski(X4,X5) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

cnf(c_0_39,plain,
    ( k4_relat_1(k8_relat_1(X1,X2)) = k5_relat_1(k6_relat_1(X1),k4_relat_1(X2))
    | ~ v1_relat_1(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31]),c_0_22])])).

cnf(c_0_40,plain,
    ( k8_relat_1(X1,k7_relat_1(k6_relat_1(X2),X3)) = k7_relat_1(k8_relat_1(X1,k6_relat_1(X2)),X3) ),
    inference(spm,[status(thm)],[c_0_32,c_0_22])).

cnf(c_0_41,plain,
    ( k4_relat_1(k7_relat_1(k6_relat_1(X1),X2)) = k7_relat_1(k6_relat_1(X2),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_28]),c_0_31]),c_0_31]),c_0_28]),c_0_22]),c_0_22])])).

cnf(c_0_42,plain,
    ( k5_relat_1(k6_relat_1(X1),k7_relat_1(k6_relat_1(X2),X3)) = k7_relat_1(k7_relat_1(k6_relat_1(X2),X3),X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_33])).

cnf(c_0_43,plain,
    ( k8_relat_1(X1,k6_relat_1(X2)) = k7_relat_1(k6_relat_1(X1),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_30]),c_0_22]),c_0_22])])).

cnf(c_0_44,plain,
    ( v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_21]),c_0_22])])).

cnf(c_0_45,plain,
    ( r1_tarski(k7_relat_1(X1,X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_46,plain,
    ( k7_relat_1(X1,k1_relat_1(X1)) = X1
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_47,plain,
    ( k1_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

fof(c_0_48,plain,(
    ! [X13,X14,X15] :
      ( ~ v1_relat_1(X15)
      | k7_relat_1(k7_relat_1(X15,X13),X14) = k7_relat_1(X15,k3_xboole_0(X13,X14)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t100_relat_1])])).

cnf(c_0_49,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_50,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

fof(c_0_51,plain,(
    ! [X6,X7,X8] : k2_enumset1(X6,X6,X7,X8) = k1_enumset1(X6,X7,X8) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

cnf(c_0_52,plain,
    ( k4_relat_1(k7_relat_1(X1,X2)) = k5_relat_1(k4_relat_1(X1),k6_relat_1(X2))
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_21]),c_0_31]),c_0_22])])).

cnf(c_0_53,plain,
    ( k4_relat_1(k7_relat_1(k8_relat_1(X1,k6_relat_1(X2)),X3)) = k7_relat_1(k7_relat_1(k6_relat_1(X3),X2),X1) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_41]),c_0_33])]),c_0_42])).

cnf(c_0_54,plain,
    ( k4_relat_1(k8_relat_1(X1,k6_relat_1(X2))) = k7_relat_1(k6_relat_1(X2),X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_43])).

cnf(c_0_55,plain,
    ( v1_relat_1(k8_relat_1(X1,k6_relat_1(X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_43]),c_0_22])])).

fof(c_0_56,plain,(
    ! [X21,X22] :
      ( ~ v1_relat_1(X22)
      | ~ r1_tarski(k2_relat_1(X22),X21)
      | k8_relat_1(X21,X22) = X22 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t125_relat_1])])).

fof(c_0_57,plain,(
    ! [X26,X27] :
      ( ( r1_tarski(k1_relat_1(X26),k1_relat_1(X27))
        | ~ r1_tarski(X26,X27)
        | ~ v1_relat_1(X27)
        | ~ v1_relat_1(X26) )
      & ( r1_tarski(k2_relat_1(X26),k2_relat_1(X27))
        | ~ r1_tarski(X26,X27)
        | ~ v1_relat_1(X27)
        | ~ v1_relat_1(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_relat_1])])])])).

cnf(c_0_58,plain,
    ( r1_tarski(k7_relat_1(k6_relat_1(X1),X2),k6_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_22])).

cnf(c_0_59,plain,
    ( k7_relat_1(k6_relat_1(X1),X1) = k6_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_22]),c_0_47])).

cnf(c_0_60,plain,
    ( k7_relat_1(k7_relat_1(X1,X2),X3) = k7_relat_1(X1,k3_xboole_0(X2,X3))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_61,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_62,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_63,plain,
    ( k5_relat_1(k7_relat_1(k6_relat_1(X1),X2),k6_relat_1(X3)) = k7_relat_1(k7_relat_1(k6_relat_1(X3),X1),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_54]),c_0_55])])).

cnf(c_0_64,plain,
    ( k8_relat_1(X2,X1) = X1
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_65,plain,
    ( k2_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_66,plain,
    ( r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
    | ~ r1_tarski(X1,X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_67,plain,
    ( r1_tarski(k8_relat_1(X1,k6_relat_1(X2)),k6_relat_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_43]),c_0_22])])).

cnf(c_0_68,plain,
    ( v1_relat_1(k8_relat_1(X1,X2))
    | ~ v1_relat_1(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_30]),c_0_22])])).

fof(c_0_69,plain,(
    ! [X16,X17,X18] :
      ( ~ v1_relat_1(X18)
      | ~ r1_tarski(X16,X17)
      | k7_relat_1(k7_relat_1(X18,X17),X16) = k7_relat_1(X18,X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t103_relat_1])])).

cnf(c_0_70,plain,
    ( r1_tarski(k2_relat_1(X1),k2_relat_1(X2))
    | ~ r1_tarski(X1,X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_71,plain,
    ( r1_tarski(k6_relat_1(X1),k6_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_72,plain,
    ( k7_relat_1(k7_relat_1(X1,X2),X3) = k7_relat_1(X1,k1_setfam_1(k2_enumset1(X2,X2,X2,X3)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_60,c_0_61]),c_0_62])).

cnf(c_0_73,plain,
    ( k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X3)) = k7_relat_1(k7_relat_1(k6_relat_1(X3),X2),X1) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_42]),c_0_41]),c_0_31]),c_0_33]),c_0_22])]),c_0_63])).

cnf(c_0_74,plain,
    ( k8_relat_1(X1,k6_relat_1(X2)) = k6_relat_1(X2)
    | ~ r1_tarski(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_22])])).

cnf(c_0_75,plain,
    ( r1_tarski(k1_relat_1(k8_relat_1(X1,k6_relat_1(X2))),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_47]),c_0_22]),c_0_55])])).

cnf(c_0_76,plain,
    ( v1_relat_1(k7_relat_1(k8_relat_1(X1,k6_relat_1(X2)),X3)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_40]),c_0_33])])).

fof(c_0_77,negated_conjecture,(
    ~ ! [X1,X2] : k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)) = k6_relat_1(k3_xboole_0(X1,X2)) ),
    inference(assume_negation,[status(cth)],[t43_funct_1])).

cnf(c_0_78,plain,
    ( k7_relat_1(k7_relat_1(X1,X3),X2) = k7_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_79,plain,
    ( r1_tarski(X1,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_65]),c_0_65]),c_0_22])])).

cnf(c_0_80,plain,
    ( r1_tarski(k2_relat_1(k8_relat_1(X1,k6_relat_1(X2))),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_67]),c_0_65]),c_0_22]),c_0_55])])).

cnf(c_0_81,plain,
    ( k7_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X1,X1,X1,X2))),X3) = k7_relat_1(k7_relat_1(k6_relat_1(X2),X1),X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_72]),c_0_73]),c_0_22])])).

cnf(c_0_82,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X1),X2)),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_58]),c_0_65]),c_0_22])]),c_0_33])])).

cnf(c_0_83,plain,
    ( k6_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X2)))) = k7_relat_1(k6_relat_1(X1),k1_relat_1(k8_relat_1(X1,k6_relat_1(X2)))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_43])).

cnf(c_0_84,plain,
    ( v1_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X3)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_30]),c_0_28]),c_0_22])])).

fof(c_0_85,negated_conjecture,(
    k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0)) != k6_relat_1(k3_xboole_0(esk1_0,esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_77])])])).

cnf(c_0_86,plain,
    ( k7_relat_1(k7_relat_1(X1,X2),X2) = k7_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_78,c_0_79])).

cnf(c_0_87,plain,
    ( k8_relat_1(X1,k8_relat_1(X1,k6_relat_1(X2))) = k8_relat_1(X1,k6_relat_1(X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_80]),c_0_55])])).

cnf(c_0_88,plain,
    ( k8_relat_1(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),k6_relat_1(X3)) = k7_relat_1(k7_relat_1(k6_relat_1(X2),X1),X3) ),
    inference(spm,[status(thm)],[c_0_43,c_0_81])).

cnf(c_0_89,plain,
    ( k8_relat_1(X1,k7_relat_1(k7_relat_1(k6_relat_1(X2),X3),X4)) = k7_relat_1(k7_relat_1(k8_relat_1(X1,k6_relat_1(X2)),X3),X4) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_40])).

cnf(c_0_90,plain,
    ( k7_relat_1(k8_relat_1(X1,k6_relat_1(X2)),X2) = k8_relat_1(X1,k6_relat_1(X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_59]),c_0_22])])).

cnf(c_0_91,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X3)),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_72]),c_0_22])])).

cnf(c_0_92,plain,
    ( k7_relat_1(k7_relat_1(X1,X2),k1_relat_1(k7_relat_1(X1,X2))) = k7_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_46,c_0_44])).

cnf(c_0_93,plain,
    ( k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X1),X2))) = k7_relat_1(k6_relat_1(X1),k1_relat_1(k7_relat_1(k6_relat_1(X1),X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_30]),c_0_28]),c_0_28]),c_0_22])])).

cnf(c_0_94,plain,
    ( k5_relat_1(k6_relat_1(X1),k7_relat_1(k7_relat_1(k6_relat_1(X2),X3),X4)) = k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X2),X3),X4),X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_84])).

cnf(c_0_95,negated_conjecture,
    ( k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0)) != k6_relat_1(k3_xboole_0(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_85])).

cnf(c_0_96,plain,
    ( k7_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X3),X4),X4) = k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X3),X4) ),
    inference(spm,[status(thm)],[c_0_86,c_0_84])).

cnf(c_0_97,plain,
    ( k7_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X1),X2),X3) = k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_88]),c_0_89]),c_0_88])).

cnf(c_0_98,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X2) = k7_relat_1(k6_relat_1(X1),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_30]),c_0_28]),c_0_28]),c_0_22])])).

cnf(c_0_99,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X3),X4)),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_72]),c_0_22])])).

cnf(c_0_100,plain,
    ( k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X1),k1_relat_1(k7_relat_1(k6_relat_1(X1),X2))),X2),X1) = k7_relat_1(k6_relat_1(X2),X1) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_92]),c_0_41]),c_0_22])]),c_0_93])).

cnf(c_0_101,plain,
    ( k5_relat_1(k6_relat_1(X1),k7_relat_1(k8_relat_1(X2,k6_relat_1(X3)),X4)) = k7_relat_1(k7_relat_1(k8_relat_1(X2,k6_relat_1(X3)),X4),X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_76])).

cnf(c_0_102,plain,
    ( k4_relat_1(k7_relat_1(k7_relat_1(k8_relat_1(X1,k6_relat_1(X2)),X3),X4)) = k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X4),X3),X2),X1) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_89]),c_0_73]),c_0_84])]),c_0_94])).

cnf(c_0_103,negated_conjecture,
    ( k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0)) != k6_relat_1(k1_setfam_1(k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_95,c_0_61]),c_0_62])).

cnf(c_0_104,plain,
    ( k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X1),X2) = k7_relat_1(k6_relat_1(X1),X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_97]),c_0_98])).

cnf(c_0_105,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X1),X2)),X2) ),
    inference(spm,[status(thm)],[c_0_99,c_0_100])).

cnf(c_0_106,plain,
    ( k5_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X3),k6_relat_1(X4)) = k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X4),X1),X2),X3) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_101]),c_0_53]),c_0_31]),c_0_76]),c_0_22])]),c_0_102])).

cnf(c_0_107,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),k1_relat_1(k7_relat_1(k6_relat_1(X1),X2))) = k7_relat_1(k6_relat_1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_46,c_0_33])).

cnf(c_0_108,negated_conjecture,
    ( k6_relat_1(k1_setfam_1(k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0))) != k7_relat_1(k6_relat_1(esk1_0),esk2_0) ),
    inference(rw,[status(thm)],[c_0_103,c_0_28])).

cnf(c_0_109,plain,
    ( k7_relat_1(k7_relat_1(k8_relat_1(X1,k6_relat_1(X2)),X1),X2) = k8_relat_1(X1,k6_relat_1(X2)) ),
    inference(spm,[status(thm)],[c_0_104,c_0_43])).

cnf(c_0_110,plain,
    ( k7_relat_1(k8_relat_1(X1,k6_relat_1(X2)),X1) = k7_relat_1(k6_relat_1(X2),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_105]),c_0_40]),c_0_33])])).

cnf(c_0_111,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X1) = k7_relat_1(k6_relat_1(X1),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_100]),c_0_41]),c_0_73]),c_0_106]),c_0_107]),c_0_84])])).

cnf(c_0_112,negated_conjecture,
    ( k6_relat_1(k1_setfam_1(k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0))) != k8_relat_1(esk1_0,k6_relat_1(esk2_0)) ),
    inference(rw,[status(thm)],[c_0_108,c_0_43])).

cnf(c_0_113,plain,
    ( k8_relat_1(X1,k6_relat_1(X2)) = k7_relat_1(k6_relat_1(X2),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_109,c_0_110]),c_0_111])).

cnf(c_0_114,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),k1_setfam_1(k2_enumset1(X2,X2,X2,X3))) = k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_98]),c_0_33])])).

cnf(c_0_115,negated_conjecture,
    ( k6_relat_1(k1_setfam_1(k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0))) != k7_relat_1(k6_relat_1(esk2_0),esk1_0) ),
    inference(rw,[status(thm)],[c_0_112,c_0_113])).

cnf(c_0_116,plain,
    ( k6_relat_1(k1_setfam_1(k2_enumset1(X1,X1,X1,X2))) = k7_relat_1(k6_relat_1(X2),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_81]),c_0_114]),c_0_111])).

cnf(c_0_117,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_115,c_0_116])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.33  % Computer   : n005.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % WCLimit    : 600
% 0.14/0.33  % DateTime   : Tue Dec  1 17:21:02 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.70/0.87  # AutoSched0-Mode selected heuristic H_____042_B03_F1_AE_Q4_SP_S2S
% 0.70/0.87  # and selection function SelectNewComplexAHP.
% 0.70/0.87  #
% 0.70/0.87  # Preprocessing time       : 0.027 s
% 0.70/0.87  
% 0.70/0.87  # Proof found!
% 0.70/0.87  # SZS status Theorem
% 0.70/0.87  # SZS output start CNFRefutation
% 0.70/0.87  fof(t94_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k7_relat_1(X2,X1)=k5_relat_1(k6_relat_1(X1),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 0.70/0.87  fof(fc24_relat_1, axiom, ![X1]:((v1_relat_1(k6_relat_1(X1))&v4_relat_1(k6_relat_1(X1),X1))&v5_relat_1(k6_relat_1(X1),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc24_relat_1)).
% 0.70/0.87  fof(dt_k5_relat_1, axiom, ![X1, X2]:((v1_relat_1(X1)&v1_relat_1(X2))=>v1_relat_1(k5_relat_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 0.70/0.87  fof(t54_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>k4_relat_1(k5_relat_1(X1,X2))=k5_relat_1(k4_relat_1(X2),k4_relat_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_relat_1)).
% 0.70/0.87  fof(t123_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k8_relat_1(X1,X2)=k5_relat_1(X2,k6_relat_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_relat_1)).
% 0.70/0.87  fof(t72_relat_1, axiom, ![X1]:k4_relat_1(k6_relat_1(X1))=k6_relat_1(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_relat_1)).
% 0.70/0.87  fof(t140_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>k7_relat_1(k8_relat_1(X1,X3),X2)=k8_relat_1(X1,k7_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t140_relat_1)).
% 0.70/0.87  fof(t88_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k7_relat_1(X2,X1),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_relat_1)).
% 0.70/0.87  fof(t98_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k7_relat_1(X1,k1_relat_1(X1))=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_relat_1)).
% 0.70/0.87  fof(t71_relat_1, axiom, ![X1]:(k1_relat_1(k6_relat_1(X1))=X1&k2_relat_1(k6_relat_1(X1))=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 0.70/0.87  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.70/0.87  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.70/0.87  fof(t100_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>k7_relat_1(k7_relat_1(X3,X1),X2)=k7_relat_1(X3,k3_xboole_0(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_relat_1)).
% 0.70/0.87  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.70/0.87  fof(t125_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k2_relat_1(X2),X1)=>k8_relat_1(X1,X2)=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_relat_1)).
% 0.70/0.87  fof(t25_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_tarski(X1,X2)=>(r1_tarski(k1_relat_1(X1),k1_relat_1(X2))&r1_tarski(k2_relat_1(X1),k2_relat_1(X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_relat_1)).
% 0.70/0.87  fof(t103_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r1_tarski(X1,X2)=>k7_relat_1(k7_relat_1(X3,X2),X1)=k7_relat_1(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t103_relat_1)).
% 0.70/0.87  fof(t43_funct_1, conjecture, ![X1, X2]:k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))=k6_relat_1(k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_funct_1)).
% 0.70/0.87  fof(c_0_18, plain, ![X38, X39]:(~v1_relat_1(X39)|k7_relat_1(X39,X38)=k5_relat_1(k6_relat_1(X38),X39)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).
% 0.70/0.87  fof(c_0_19, plain, ![X41]:((v1_relat_1(k6_relat_1(X41))&v4_relat_1(k6_relat_1(X41),X41))&v5_relat_1(k6_relat_1(X41),X41)), inference(variable_rename,[status(thm)],[fc24_relat_1])).
% 0.70/0.87  fof(c_0_20, plain, ![X11, X12]:(~v1_relat_1(X11)|~v1_relat_1(X12)|v1_relat_1(k5_relat_1(X11,X12))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_relat_1])])).
% 0.70/0.87  cnf(c_0_21, plain, (k7_relat_1(X1,X2)=k5_relat_1(k6_relat_1(X2),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.70/0.87  cnf(c_0_22, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.70/0.87  fof(c_0_23, plain, ![X28, X29]:(~v1_relat_1(X28)|(~v1_relat_1(X29)|k4_relat_1(k5_relat_1(X28,X29))=k5_relat_1(k4_relat_1(X29),k4_relat_1(X28)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t54_relat_1])])])).
% 0.70/0.87  fof(c_0_24, plain, ![X19, X20]:(~v1_relat_1(X20)|k8_relat_1(X19,X20)=k5_relat_1(X20,k6_relat_1(X19))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t123_relat_1])])).
% 0.70/0.87  fof(c_0_25, plain, ![X34]:k4_relat_1(k6_relat_1(X34))=k6_relat_1(X34), inference(variable_rename,[status(thm)],[t72_relat_1])).
% 0.70/0.87  fof(c_0_26, plain, ![X23, X24, X25]:(~v1_relat_1(X25)|k7_relat_1(k8_relat_1(X23,X25),X24)=k8_relat_1(X23,k7_relat_1(X25,X24))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t140_relat_1])])).
% 0.70/0.87  cnf(c_0_27, plain, (v1_relat_1(k5_relat_1(X1,X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.70/0.87  cnf(c_0_28, plain, (k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))=k7_relat_1(k6_relat_1(X2),X1)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.70/0.87  cnf(c_0_29, plain, (k4_relat_1(k5_relat_1(X1,X2))=k5_relat_1(k4_relat_1(X2),k4_relat_1(X1))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.70/0.87  cnf(c_0_30, plain, (k8_relat_1(X2,X1)=k5_relat_1(X1,k6_relat_1(X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.70/0.87  cnf(c_0_31, plain, (k4_relat_1(k6_relat_1(X1))=k6_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.70/0.87  cnf(c_0_32, plain, (k7_relat_1(k8_relat_1(X2,X1),X3)=k8_relat_1(X2,k7_relat_1(X1,X3))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.70/0.87  cnf(c_0_33, plain, (v1_relat_1(k7_relat_1(k6_relat_1(X1),X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_22]), c_0_22])])).
% 0.70/0.87  fof(c_0_34, plain, ![X36, X37]:(~v1_relat_1(X37)|r1_tarski(k7_relat_1(X37,X36),X37)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t88_relat_1])])).
% 0.70/0.87  fof(c_0_35, plain, ![X40]:(~v1_relat_1(X40)|k7_relat_1(X40,k1_relat_1(X40))=X40), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t98_relat_1])])).
% 0.70/0.87  fof(c_0_36, plain, ![X33]:(k1_relat_1(k6_relat_1(X33))=X33&k2_relat_1(k6_relat_1(X33))=X33), inference(variable_rename,[status(thm)],[t71_relat_1])).
% 0.70/0.87  fof(c_0_37, plain, ![X9, X10]:k1_setfam_1(k2_tarski(X9,X10))=k3_xboole_0(X9,X10), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.70/0.87  fof(c_0_38, plain, ![X4, X5]:k1_enumset1(X4,X4,X5)=k2_tarski(X4,X5), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.70/0.87  cnf(c_0_39, plain, (k4_relat_1(k8_relat_1(X1,X2))=k5_relat_1(k6_relat_1(X1),k4_relat_1(X2))|~v1_relat_1(X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_31]), c_0_22])])).
% 0.70/0.87  cnf(c_0_40, plain, (k8_relat_1(X1,k7_relat_1(k6_relat_1(X2),X3))=k7_relat_1(k8_relat_1(X1,k6_relat_1(X2)),X3)), inference(spm,[status(thm)],[c_0_32, c_0_22])).
% 0.70/0.87  cnf(c_0_41, plain, (k4_relat_1(k7_relat_1(k6_relat_1(X1),X2))=k7_relat_1(k6_relat_1(X2),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_28]), c_0_31]), c_0_31]), c_0_28]), c_0_22]), c_0_22])])).
% 0.70/0.87  cnf(c_0_42, plain, (k5_relat_1(k6_relat_1(X1),k7_relat_1(k6_relat_1(X2),X3))=k7_relat_1(k7_relat_1(k6_relat_1(X2),X3),X1)), inference(spm,[status(thm)],[c_0_21, c_0_33])).
% 0.70/0.87  cnf(c_0_43, plain, (k8_relat_1(X1,k6_relat_1(X2))=k7_relat_1(k6_relat_1(X1),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_30]), c_0_22]), c_0_22])])).
% 0.70/0.87  cnf(c_0_44, plain, (v1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_21]), c_0_22])])).
% 0.70/0.87  cnf(c_0_45, plain, (r1_tarski(k7_relat_1(X1,X2),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.70/0.87  cnf(c_0_46, plain, (k7_relat_1(X1,k1_relat_1(X1))=X1|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.70/0.87  cnf(c_0_47, plain, (k1_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.70/0.87  fof(c_0_48, plain, ![X13, X14, X15]:(~v1_relat_1(X15)|k7_relat_1(k7_relat_1(X15,X13),X14)=k7_relat_1(X15,k3_xboole_0(X13,X14))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t100_relat_1])])).
% 0.70/0.87  cnf(c_0_49, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.70/0.87  cnf(c_0_50, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.70/0.87  fof(c_0_51, plain, ![X6, X7, X8]:k2_enumset1(X6,X6,X7,X8)=k1_enumset1(X6,X7,X8), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.70/0.87  cnf(c_0_52, plain, (k4_relat_1(k7_relat_1(X1,X2))=k5_relat_1(k4_relat_1(X1),k6_relat_1(X2))|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_21]), c_0_31]), c_0_22])])).
% 0.70/0.87  cnf(c_0_53, plain, (k4_relat_1(k7_relat_1(k8_relat_1(X1,k6_relat_1(X2)),X3))=k7_relat_1(k7_relat_1(k6_relat_1(X3),X2),X1)), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_41]), c_0_33])]), c_0_42])).
% 0.70/0.87  cnf(c_0_54, plain, (k4_relat_1(k8_relat_1(X1,k6_relat_1(X2)))=k7_relat_1(k6_relat_1(X2),X1)), inference(spm,[status(thm)],[c_0_41, c_0_43])).
% 0.70/0.87  cnf(c_0_55, plain, (v1_relat_1(k8_relat_1(X1,k6_relat_1(X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_43]), c_0_22])])).
% 0.70/0.87  fof(c_0_56, plain, ![X21, X22]:(~v1_relat_1(X22)|(~r1_tarski(k2_relat_1(X22),X21)|k8_relat_1(X21,X22)=X22)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t125_relat_1])])).
% 0.70/0.87  fof(c_0_57, plain, ![X26, X27]:((r1_tarski(k1_relat_1(X26),k1_relat_1(X27))|~r1_tarski(X26,X27)|~v1_relat_1(X27)|~v1_relat_1(X26))&(r1_tarski(k2_relat_1(X26),k2_relat_1(X27))|~r1_tarski(X26,X27)|~v1_relat_1(X27)|~v1_relat_1(X26))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_relat_1])])])])).
% 0.70/0.87  cnf(c_0_58, plain, (r1_tarski(k7_relat_1(k6_relat_1(X1),X2),k6_relat_1(X1))), inference(spm,[status(thm)],[c_0_45, c_0_22])).
% 0.70/0.87  cnf(c_0_59, plain, (k7_relat_1(k6_relat_1(X1),X1)=k6_relat_1(X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_22]), c_0_47])).
% 0.70/0.87  cnf(c_0_60, plain, (k7_relat_1(k7_relat_1(X1,X2),X3)=k7_relat_1(X1,k3_xboole_0(X2,X3))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.70/0.87  cnf(c_0_61, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_49, c_0_50])).
% 0.70/0.87  cnf(c_0_62, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.70/0.87  cnf(c_0_63, plain, (k5_relat_1(k7_relat_1(k6_relat_1(X1),X2),k6_relat_1(X3))=k7_relat_1(k7_relat_1(k6_relat_1(X3),X1),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_54]), c_0_55])])).
% 0.70/0.87  cnf(c_0_64, plain, (k8_relat_1(X2,X1)=X1|~v1_relat_1(X1)|~r1_tarski(k2_relat_1(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.70/0.87  cnf(c_0_65, plain, (k2_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.70/0.87  cnf(c_0_66, plain, (r1_tarski(k1_relat_1(X1),k1_relat_1(X2))|~r1_tarski(X1,X2)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.70/0.87  cnf(c_0_67, plain, (r1_tarski(k8_relat_1(X1,k6_relat_1(X2)),k6_relat_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_43]), c_0_22])])).
% 0.70/0.87  cnf(c_0_68, plain, (v1_relat_1(k8_relat_1(X1,X2))|~v1_relat_1(X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_30]), c_0_22])])).
% 0.70/0.87  fof(c_0_69, plain, ![X16, X17, X18]:(~v1_relat_1(X18)|(~r1_tarski(X16,X17)|k7_relat_1(k7_relat_1(X18,X17),X16)=k7_relat_1(X18,X16))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t103_relat_1])])).
% 0.70/0.87  cnf(c_0_70, plain, (r1_tarski(k2_relat_1(X1),k2_relat_1(X2))|~r1_tarski(X1,X2)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.70/0.87  cnf(c_0_71, plain, (r1_tarski(k6_relat_1(X1),k6_relat_1(X1))), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.70/0.87  cnf(c_0_72, plain, (k7_relat_1(k7_relat_1(X1,X2),X3)=k7_relat_1(X1,k1_setfam_1(k2_enumset1(X2,X2,X2,X3)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_60, c_0_61]), c_0_62])).
% 0.70/0.87  cnf(c_0_73, plain, (k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X3))=k7_relat_1(k7_relat_1(k6_relat_1(X3),X2),X1)), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_42]), c_0_41]), c_0_31]), c_0_33]), c_0_22])]), c_0_63])).
% 0.70/0.87  cnf(c_0_74, plain, (k8_relat_1(X1,k6_relat_1(X2))=k6_relat_1(X2)|~r1_tarski(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_22])])).
% 0.70/0.87  cnf(c_0_75, plain, (r1_tarski(k1_relat_1(k8_relat_1(X1,k6_relat_1(X2))),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_47]), c_0_22]), c_0_55])])).
% 0.70/0.87  cnf(c_0_76, plain, (v1_relat_1(k7_relat_1(k8_relat_1(X1,k6_relat_1(X2)),X3))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_40]), c_0_33])])).
% 0.70/0.87  fof(c_0_77, negated_conjecture, ~(![X1, X2]:k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))=k6_relat_1(k3_xboole_0(X1,X2))), inference(assume_negation,[status(cth)],[t43_funct_1])).
% 0.70/0.87  cnf(c_0_78, plain, (k7_relat_1(k7_relat_1(X1,X3),X2)=k7_relat_1(X1,X2)|~v1_relat_1(X1)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_69])).
% 0.70/0.87  cnf(c_0_79, plain, (r1_tarski(X1,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_71]), c_0_65]), c_0_65]), c_0_22])])).
% 0.70/0.87  cnf(c_0_80, plain, (r1_tarski(k2_relat_1(k8_relat_1(X1,k6_relat_1(X2))),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_67]), c_0_65]), c_0_22]), c_0_55])])).
% 0.70/0.87  cnf(c_0_81, plain, (k7_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X1,X1,X1,X2))),X3)=k7_relat_1(k7_relat_1(k6_relat_1(X2),X1),X3)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_72]), c_0_73]), c_0_22])])).
% 0.70/0.87  cnf(c_0_82, plain, (r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X1),X2)),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_58]), c_0_65]), c_0_22])]), c_0_33])])).
% 0.70/0.87  cnf(c_0_83, plain, (k6_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X2))))=k7_relat_1(k6_relat_1(X1),k1_relat_1(k8_relat_1(X1,k6_relat_1(X2))))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_75]), c_0_43])).
% 0.70/0.87  cnf(c_0_84, plain, (v1_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X3))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_30]), c_0_28]), c_0_22])])).
% 0.70/0.87  fof(c_0_85, negated_conjecture, k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0))!=k6_relat_1(k3_xboole_0(esk1_0,esk2_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_77])])])).
% 0.70/0.87  cnf(c_0_86, plain, (k7_relat_1(k7_relat_1(X1,X2),X2)=k7_relat_1(X1,X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_78, c_0_79])).
% 0.70/0.87  cnf(c_0_87, plain, (k8_relat_1(X1,k8_relat_1(X1,k6_relat_1(X2)))=k8_relat_1(X1,k6_relat_1(X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_80]), c_0_55])])).
% 0.70/0.87  cnf(c_0_88, plain, (k8_relat_1(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),k6_relat_1(X3))=k7_relat_1(k7_relat_1(k6_relat_1(X2),X1),X3)), inference(spm,[status(thm)],[c_0_43, c_0_81])).
% 0.70/0.87  cnf(c_0_89, plain, (k8_relat_1(X1,k7_relat_1(k7_relat_1(k6_relat_1(X2),X3),X4))=k7_relat_1(k7_relat_1(k8_relat_1(X1,k6_relat_1(X2)),X3),X4)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_40])).
% 0.70/0.87  cnf(c_0_90, plain, (k7_relat_1(k8_relat_1(X1,k6_relat_1(X2)),X2)=k8_relat_1(X1,k6_relat_1(X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_59]), c_0_22])])).
% 0.70/0.87  cnf(c_0_91, plain, (r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X3)),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_72]), c_0_22])])).
% 0.70/0.87  cnf(c_0_92, plain, (k7_relat_1(k7_relat_1(X1,X2),k1_relat_1(k7_relat_1(X1,X2)))=k7_relat_1(X1,X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_46, c_0_44])).
% 0.70/0.87  cnf(c_0_93, plain, (k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X1),X2)))=k7_relat_1(k6_relat_1(X1),k1_relat_1(k7_relat_1(k6_relat_1(X1),X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_30]), c_0_28]), c_0_28]), c_0_22])])).
% 0.70/0.87  cnf(c_0_94, plain, (k5_relat_1(k6_relat_1(X1),k7_relat_1(k7_relat_1(k6_relat_1(X2),X3),X4))=k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X2),X3),X4),X1)), inference(spm,[status(thm)],[c_0_21, c_0_84])).
% 0.70/0.87  cnf(c_0_95, negated_conjecture, (k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0))!=k6_relat_1(k3_xboole_0(esk1_0,esk2_0))), inference(split_conjunct,[status(thm)],[c_0_85])).
% 0.70/0.87  cnf(c_0_96, plain, (k7_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X3),X4),X4)=k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X3),X4)), inference(spm,[status(thm)],[c_0_86, c_0_84])).
% 0.70/0.87  cnf(c_0_97, plain, (k7_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X1),X2),X3)=k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_88]), c_0_89]), c_0_88])).
% 0.70/0.87  cnf(c_0_98, plain, (k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X2)=k7_relat_1(k6_relat_1(X1),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_30]), c_0_28]), c_0_28]), c_0_22])])).
% 0.70/0.87  cnf(c_0_99, plain, (r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X3),X4)),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_72]), c_0_22])])).
% 0.70/0.87  cnf(c_0_100, plain, (k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X1),k1_relat_1(k7_relat_1(k6_relat_1(X1),X2))),X2),X1)=k7_relat_1(k6_relat_1(X2),X1)), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_92]), c_0_41]), c_0_22])]), c_0_93])).
% 0.70/0.87  cnf(c_0_101, plain, (k5_relat_1(k6_relat_1(X1),k7_relat_1(k8_relat_1(X2,k6_relat_1(X3)),X4))=k7_relat_1(k7_relat_1(k8_relat_1(X2,k6_relat_1(X3)),X4),X1)), inference(spm,[status(thm)],[c_0_21, c_0_76])).
% 0.70/0.87  cnf(c_0_102, plain, (k4_relat_1(k7_relat_1(k7_relat_1(k8_relat_1(X1,k6_relat_1(X2)),X3),X4))=k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X4),X3),X2),X1)), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_89]), c_0_73]), c_0_84])]), c_0_94])).
% 0.70/0.87  cnf(c_0_103, negated_conjecture, (k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0))!=k6_relat_1(k1_setfam_1(k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_95, c_0_61]), c_0_62])).
% 0.70/0.87  cnf(c_0_104, plain, (k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X1),X2)=k7_relat_1(k6_relat_1(X1),X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_97]), c_0_98])).
% 0.70/0.87  cnf(c_0_105, plain, (r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X1),X2)),X2)), inference(spm,[status(thm)],[c_0_99, c_0_100])).
% 0.70/0.87  cnf(c_0_106, plain, (k5_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X3),k6_relat_1(X4))=k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X4),X1),X2),X3)), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_101]), c_0_53]), c_0_31]), c_0_76]), c_0_22])]), c_0_102])).
% 0.70/0.87  cnf(c_0_107, plain, (k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),k1_relat_1(k7_relat_1(k6_relat_1(X1),X2)))=k7_relat_1(k6_relat_1(X1),X2)), inference(spm,[status(thm)],[c_0_46, c_0_33])).
% 0.70/0.87  cnf(c_0_108, negated_conjecture, (k6_relat_1(k1_setfam_1(k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0)))!=k7_relat_1(k6_relat_1(esk1_0),esk2_0)), inference(rw,[status(thm)],[c_0_103, c_0_28])).
% 0.70/0.87  cnf(c_0_109, plain, (k7_relat_1(k7_relat_1(k8_relat_1(X1,k6_relat_1(X2)),X1),X2)=k8_relat_1(X1,k6_relat_1(X2))), inference(spm,[status(thm)],[c_0_104, c_0_43])).
% 0.70/0.87  cnf(c_0_110, plain, (k7_relat_1(k8_relat_1(X1,k6_relat_1(X2)),X1)=k7_relat_1(k6_relat_1(X2),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_105]), c_0_40]), c_0_33])])).
% 0.70/0.87  cnf(c_0_111, plain, (k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X1)=k7_relat_1(k6_relat_1(X1),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_100]), c_0_41]), c_0_73]), c_0_106]), c_0_107]), c_0_84])])).
% 0.70/0.87  cnf(c_0_112, negated_conjecture, (k6_relat_1(k1_setfam_1(k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0)))!=k8_relat_1(esk1_0,k6_relat_1(esk2_0))), inference(rw,[status(thm)],[c_0_108, c_0_43])).
% 0.70/0.87  cnf(c_0_113, plain, (k8_relat_1(X1,k6_relat_1(X2))=k7_relat_1(k6_relat_1(X2),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_109, c_0_110]), c_0_111])).
% 0.70/0.87  cnf(c_0_114, plain, (k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),k1_setfam_1(k2_enumset1(X2,X2,X2,X3)))=k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X3)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_98]), c_0_33])])).
% 0.70/0.87  cnf(c_0_115, negated_conjecture, (k6_relat_1(k1_setfam_1(k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0)))!=k7_relat_1(k6_relat_1(esk2_0),esk1_0)), inference(rw,[status(thm)],[c_0_112, c_0_113])).
% 0.70/0.87  cnf(c_0_116, plain, (k6_relat_1(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)))=k7_relat_1(k6_relat_1(X2),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_81]), c_0_114]), c_0_111])).
% 0.70/0.87  cnf(c_0_117, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_115, c_0_116])]), ['proof']).
% 0.70/0.87  # SZS output end CNFRefutation
% 0.70/0.87  # Proof object total steps             : 118
% 0.70/0.87  # Proof object clause steps            : 81
% 0.70/0.87  # Proof object formula steps           : 37
% 0.70/0.87  # Proof object conjectures             : 9
% 0.70/0.87  # Proof object clause conjectures      : 6
% 0.70/0.87  # Proof object formula conjectures     : 3
% 0.70/0.87  # Proof object initial clauses used    : 20
% 0.70/0.87  # Proof object initial formulas used   : 18
% 0.70/0.87  # Proof object generating inferences   : 53
% 0.70/0.87  # Proof object simplifying inferences  : 127
% 0.70/0.87  # Training examples: 0 positive, 0 negative
% 0.70/0.87  # Parsed axioms                        : 20
% 0.70/0.87  # Removed by relevancy pruning/SinE    : 0
% 0.70/0.87  # Initial clauses                      : 24
% 0.70/0.87  # Removed in clause preprocessing      : 3
% 0.70/0.87  # Initial clauses in saturation        : 21
% 0.70/0.87  # Processed clauses                    : 3221
% 0.70/0.87  # ...of these trivial                  : 555
% 0.70/0.87  # ...subsumed                          : 2003
% 0.70/0.87  # ...remaining for further processing  : 663
% 0.70/0.87  # Other redundant clauses eliminated   : 0
% 0.70/0.87  # Clauses deleted for lack of memory   : 0
% 0.70/0.87  # Backward-subsumed                    : 45
% 0.70/0.87  # Backward-rewritten                   : 229
% 0.70/0.87  # Generated clauses                    : 59297
% 0.70/0.87  # ...of the previous two non-trivial   : 50583
% 0.70/0.87  # Contextual simplify-reflections      : 0
% 0.70/0.87  # Paramodulations                      : 59297
% 0.70/0.87  # Factorizations                       : 0
% 0.70/0.87  # Equation resolutions                 : 0
% 0.70/0.87  # Propositional unsat checks           : 0
% 0.70/0.87  #    Propositional check models        : 0
% 0.70/0.87  #    Propositional check unsatisfiable : 0
% 0.70/0.87  #    Propositional clauses             : 0
% 0.70/0.87  #    Propositional clauses after purity: 0
% 0.70/0.87  #    Propositional unsat core size     : 0
% 0.70/0.87  #    Propositional preprocessing time  : 0.000
% 0.70/0.87  #    Propositional encoding time       : 0.000
% 0.70/0.87  #    Propositional solver time         : 0.000
% 0.70/0.87  #    Success case prop preproc time    : 0.000
% 0.70/0.87  #    Success case prop encoding time   : 0.000
% 0.70/0.87  #    Success case prop solver time     : 0.000
% 0.70/0.87  # Current number of processed clauses  : 389
% 0.70/0.87  #    Positive orientable unit clauses  : 99
% 0.70/0.87  #    Positive unorientable unit clauses: 5
% 0.70/0.87  #    Negative unit clauses             : 0
% 0.70/0.87  #    Non-unit-clauses                  : 285
% 0.70/0.87  # Current number of unprocessed clauses: 46932
% 0.70/0.87  # ...number of literals in the above   : 114978
% 0.70/0.87  # Current number of archived formulas  : 0
% 0.70/0.87  # Current number of archived clauses   : 277
% 0.70/0.87  # Clause-clause subsumption calls (NU) : 19761
% 0.70/0.87  # Rec. Clause-clause subsumption calls : 18266
% 0.70/0.87  # Non-unit clause-clause subsumptions  : 1983
% 0.70/0.87  # Unit Clause-clause subsumption calls : 396
% 0.70/0.87  # Rewrite failures with RHS unbound    : 0
% 0.70/0.87  # BW rewrite match attempts            : 1227
% 0.70/0.87  # BW rewrite match successes           : 240
% 0.70/0.87  # Condensation attempts                : 0
% 0.70/0.87  # Condensation successes               : 0
% 0.70/0.87  # Termbank termtop insertions          : 980328
% 0.70/0.88  
% 0.70/0.88  # -------------------------------------------------
% 0.70/0.88  # User time                : 0.510 s
% 0.70/0.88  # System time              : 0.020 s
% 0.70/0.88  # Total time               : 0.530 s
% 0.70/0.88  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
