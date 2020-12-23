%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:53:27 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  122 (49139 expanded)
%              Number of clauses        :   83 (21282 expanded)
%              Number of leaves         :   19 (13928 expanded)
%              Depth                    :   21
%              Number of atoms          :  199 (71571 expanded)
%              Number of equality atoms :   92 (30842 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    8 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t76_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k5_relat_1(X2,k6_relat_1(X1)),X2)
        & r1_tarski(k5_relat_1(k6_relat_1(X1),X2),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_relat_1)).

fof(t94_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,X1) = k5_relat_1(k6_relat_1(X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(fc1_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_relat_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t124_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k8_relat_1(X1,X2) = k3_xboole_0(X2,k2_zfmisc_1(k1_relat_1(X2),X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t124_relat_1)).

fof(dt_k6_relat_1,axiom,(
    ! [X1] : v1_relat_1(k6_relat_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(t123_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k8_relat_1(X1,X2) = k5_relat_1(X2,k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

fof(t25_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => ( r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
              & r1_tarski(k2_relat_1(X1),k2_relat_1(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

fof(t71_relat_1,axiom,(
    ! [X1] :
      ( k1_relat_1(k6_relat_1(X1)) = X1
      & k2_relat_1(k6_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(t54_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k4_relat_1(k5_relat_1(X1,X2)) = k5_relat_1(k4_relat_1(X2),k4_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relat_1)).

fof(t72_relat_1,axiom,(
    ! [X1] : k4_relat_1(k6_relat_1(X1)) = k6_relat_1(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_relat_1)).

fof(t112_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => k7_relat_1(k5_relat_1(X2,X3),X1) = k5_relat_1(k7_relat_1(X2,X1),X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_relat_1)).

fof(t97_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k1_relat_1(X2),X1)
       => k7_relat_1(X2,X1) = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

fof(t98_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,k1_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).

fof(t100_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => k7_relat_1(k7_relat_1(X3,X1),X2) = k7_relat_1(X3,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).

fof(t43_funct_1,conjecture,(
    ! [X1,X2] : k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)) = k6_relat_1(k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(c_0_19,plain,(
    ! [X13,X14] : k1_setfam_1(k2_tarski(X13,X14)) = k3_xboole_0(X13,X14) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_20,plain,(
    ! [X8,X9] : k1_enumset1(X8,X8,X9) = k2_tarski(X8,X9) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_21,plain,(
    ! [X34,X35] :
      ( ( r1_tarski(k5_relat_1(X35,k6_relat_1(X34)),X35)
        | ~ v1_relat_1(X35) )
      & ( r1_tarski(k5_relat_1(k6_relat_1(X34),X35),X35)
        | ~ v1_relat_1(X35) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t76_relat_1])])])).

fof(c_0_22,plain,(
    ! [X36,X37] :
      ( ~ v1_relat_1(X37)
      | k7_relat_1(X37,X36) = k5_relat_1(k6_relat_1(X36),X37) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).

fof(c_0_23,plain,(
    ! [X16,X17] :
      ( ~ v1_relat_1(X16)
      | v1_relat_1(k3_xboole_0(X16,X17)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_relat_1])])).

cnf(c_0_24,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_26,plain,(
    ! [X10,X11,X12] : k2_enumset1(X10,X10,X11,X12) = k1_enumset1(X10,X11,X12) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_27,plain,(
    ! [X26,X27] :
      ( ~ v1_relat_1(X27)
      | k8_relat_1(X26,X27) = k3_xboole_0(X27,k2_zfmisc_1(k1_relat_1(X27),X26)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t124_relat_1])])).

cnf(c_0_28,plain,
    ( r1_tarski(k5_relat_1(k6_relat_1(X1),X2),X2)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,plain,
    ( k7_relat_1(X1,X2) = k5_relat_1(k6_relat_1(X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_30,plain,(
    ! [X15] : v1_relat_1(k6_relat_1(X15)) ),
    inference(variable_rename,[status(thm)],[dt_k6_relat_1])).

cnf(c_0_31,plain,
    ( v1_relat_1(k3_xboole_0(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_32,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_33,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_34,plain,
    ( k8_relat_1(X2,X1) = k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_35,plain,(
    ! [X24,X25] :
      ( ~ v1_relat_1(X25)
      | k8_relat_1(X24,X25) = k5_relat_1(X25,k6_relat_1(X24)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t123_relat_1])])).

fof(c_0_36,plain,(
    ! [X28,X29] :
      ( ( r1_tarski(k1_relat_1(X28),k1_relat_1(X29))
        | ~ r1_tarski(X28,X29)
        | ~ v1_relat_1(X29)
        | ~ v1_relat_1(X28) )
      & ( r1_tarski(k2_relat_1(X28),k2_relat_1(X29))
        | ~ r1_tarski(X28,X29)
        | ~ v1_relat_1(X29)
        | ~ v1_relat_1(X28) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_relat_1])])])])).

cnf(c_0_37,plain,
    ( r1_tarski(k7_relat_1(X1,X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_38,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_39,plain,(
    ! [X32] :
      ( k1_relat_1(k6_relat_1(X32)) = X32
      & k2_relat_1(k6_relat_1(X32)) = X32 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

cnf(c_0_40,plain,
    ( v1_relat_1(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_32]),c_0_33])).

cnf(c_0_41,plain,
    ( k8_relat_1(X2,X1) = k1_setfam_1(k2_enumset1(X1,X1,X1,k2_zfmisc_1(k1_relat_1(X1),X2)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_32]),c_0_33])).

cnf(c_0_42,plain,
    ( k8_relat_1(X2,X1) = k5_relat_1(X1,k6_relat_1(X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_43,plain,
    ( r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
    | ~ r1_tarski(X1,X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_44,plain,
    ( r1_tarski(k7_relat_1(k6_relat_1(X1),X2),k6_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_45,plain,
    ( k1_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_46,plain,
    ( v1_relat_1(k8_relat_1(X1,X2))
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_47,plain,
    ( k7_relat_1(k6_relat_1(X1),X2) = k8_relat_1(X1,k6_relat_1(X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_29]),c_0_38]),c_0_38])])).

fof(c_0_48,plain,(
    ! [X30,X31] :
      ( ~ v1_relat_1(X30)
      | ~ v1_relat_1(X31)
      | k4_relat_1(k5_relat_1(X30,X31)) = k5_relat_1(k4_relat_1(X31),k4_relat_1(X30)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t54_relat_1])])])).

fof(c_0_49,plain,(
    ! [X33] : k4_relat_1(k6_relat_1(X33)) = k6_relat_1(X33) ),
    inference(variable_rename,[status(thm)],[t72_relat_1])).

fof(c_0_50,plain,(
    ! [X21,X22,X23] :
      ( ~ v1_relat_1(X22)
      | ~ v1_relat_1(X23)
      | k7_relat_1(k5_relat_1(X22,X23),X21) = k5_relat_1(k7_relat_1(X22,X21),X23) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t112_relat_1])])])).

cnf(c_0_51,plain,
    ( k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) = k8_relat_1(X2,k6_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_38])).

fof(c_0_52,plain,(
    ! [X38,X39] :
      ( ~ v1_relat_1(X39)
      | ~ r1_tarski(k1_relat_1(X39),X38)
      | k7_relat_1(X39,X38) = X39 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t97_relat_1])])).

cnf(c_0_53,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X1),X2)),X1)
    | ~ v1_relat_1(k7_relat_1(k6_relat_1(X1),X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45]),c_0_38])])).

cnf(c_0_54,plain,
    ( v1_relat_1(k7_relat_1(k6_relat_1(X1),X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_38])])).

cnf(c_0_55,plain,
    ( k4_relat_1(k5_relat_1(X1,X2)) = k5_relat_1(k4_relat_1(X2),k4_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_56,plain,
    ( k4_relat_1(k6_relat_1(X1)) = k6_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_57,plain,
    ( k7_relat_1(k5_relat_1(X1,X2),X3) = k5_relat_1(k7_relat_1(X1,X3),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_58,plain,
    ( r1_tarski(k8_relat_1(X1,k6_relat_1(X2)),k6_relat_1(X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_38]),c_0_51])).

cnf(c_0_59,plain,
    ( k7_relat_1(X1,X2) = X1
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_60,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X1),X2)),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_53,c_0_54])])).

cnf(c_0_61,plain,
    ( k4_relat_1(k8_relat_1(X1,k6_relat_1(X2))) = k8_relat_1(X2,k6_relat_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_51]),c_0_56]),c_0_56]),c_0_51]),c_0_38]),c_0_38])])).

cnf(c_0_62,plain,
    ( v1_relat_1(k8_relat_1(X1,k6_relat_1(X2))) ),
    inference(spm,[status(thm)],[c_0_54,c_0_47])).

cnf(c_0_63,plain,
    ( k5_relat_1(k7_relat_1(k6_relat_1(X1),X2),X3) = k7_relat_1(k5_relat_1(k6_relat_1(X1),X3),X2)
    | ~ v1_relat_1(X3) ),
    inference(spm,[status(thm)],[c_0_57,c_0_38])).

cnf(c_0_64,plain,
    ( r1_tarski(k1_relat_1(k8_relat_1(X1,k6_relat_1(X2))),X1)
    | ~ v1_relat_1(k8_relat_1(X1,k6_relat_1(X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_58]),c_0_45]),c_0_38])])).

cnf(c_0_65,plain,
    ( k4_relat_1(k7_relat_1(X1,X2)) = k5_relat_1(k4_relat_1(X1),k6_relat_1(X2))
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_29]),c_0_56]),c_0_38])])).

cnf(c_0_66,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X1) = k7_relat_1(k6_relat_1(X1),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_54])])).

cnf(c_0_67,plain,
    ( k4_relat_1(k7_relat_1(k6_relat_1(X1),X2)) = k8_relat_1(X2,k6_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_61,c_0_47])).

cnf(c_0_68,plain,
    ( k5_relat_1(k8_relat_1(X1,k6_relat_1(X2)),k6_relat_1(X3)) = k8_relat_1(X3,k8_relat_1(X1,k6_relat_1(X2))) ),
    inference(spm,[status(thm)],[c_0_42,c_0_62])).

cnf(c_0_69,plain,
    ( k5_relat_1(k7_relat_1(k6_relat_1(X1),X2),k6_relat_1(X3)) = k7_relat_1(k8_relat_1(X3,k6_relat_1(X1)),X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_38]),c_0_51])).

cnf(c_0_70,plain,
    ( r1_tarski(k1_relat_1(k8_relat_1(X1,k6_relat_1(X2))),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_64,c_0_62])])).

cnf(c_0_71,plain,
    ( k8_relat_1(X1,k8_relat_1(X2,k6_relat_1(X1))) = k8_relat_1(X2,k6_relat_1(X1)) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_67]),c_0_67]),c_0_54])]),c_0_68])).

cnf(c_0_72,plain,
    ( k8_relat_1(X1,k7_relat_1(k6_relat_1(X2),X3)) = k7_relat_1(k8_relat_1(X1,k6_relat_1(X2)),X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_54]),c_0_69])).

cnf(c_0_73,plain,
    ( k7_relat_1(k8_relat_1(X1,k6_relat_1(X2)),X1) = k8_relat_1(X1,k6_relat_1(X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_70]),c_0_62])])).

cnf(c_0_74,plain,
    ( k8_relat_1(X1,k6_relat_1(X2)) = k7_relat_1(k6_relat_1(X2),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_47]),c_0_72]),c_0_73])).

cnf(c_0_75,plain,
    ( r1_tarski(k5_relat_1(X1,k6_relat_1(X2)),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_76,plain,(
    ! [X40] :
      ( ~ v1_relat_1(X40)
      | k7_relat_1(X40,k1_relat_1(X40)) = X40 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t98_relat_1])])).

cnf(c_0_77,plain,
    ( k4_relat_1(k7_relat_1(k6_relat_1(X1),X2)) = k7_relat_1(k6_relat_1(X1),X2) ),
    inference(rw,[status(thm)],[c_0_67,c_0_74])).

cnf(c_0_78,plain,
    ( r1_tarski(k7_relat_1(k6_relat_1(X1),X2),k6_relat_1(X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_29]),c_0_38]),c_0_38])])).

fof(c_0_79,plain,(
    ! [X18,X19,X20] :
      ( ~ v1_relat_1(X20)
      | k7_relat_1(k7_relat_1(X20,X18),X19) = k7_relat_1(X20,k3_xboole_0(X18,X19)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t100_relat_1])])).

cnf(c_0_80,plain,
    ( k7_relat_1(X1,k1_relat_1(X1)) = X1
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_76])).

cnf(c_0_81,plain,
    ( r1_tarski(k7_relat_1(k5_relat_1(X1,k6_relat_1(X2)),X3),k7_relat_1(X1,X3))
    | ~ v1_relat_1(k7_relat_1(X1,X3))
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_57]),c_0_38])])).

cnf(c_0_82,plain,
    ( k7_relat_1(k6_relat_1(X1),X2) = k7_relat_1(k6_relat_1(X2),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_74]),c_0_74]),c_0_77])).

cnf(c_0_83,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X1),X2)),X2)
    | ~ v1_relat_1(k7_relat_1(k6_relat_1(X1),X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_78]),c_0_45]),c_0_38])])).

cnf(c_0_84,plain,
    ( k7_relat_1(k7_relat_1(X1,X2),X3) = k7_relat_1(X1,k3_xboole_0(X2,X3))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_79])).

cnf(c_0_85,plain,
    ( k5_relat_1(k6_relat_1(X1),k7_relat_1(k6_relat_1(X2),X3)) = k7_relat_1(k7_relat_1(k6_relat_1(X2),X3),X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_54])).

cnf(c_0_86,plain,
    ( k8_relat_1(X1,k7_relat_1(k6_relat_1(X2),X3)) = k7_relat_1(k7_relat_1(k6_relat_1(X2),X1),X3) ),
    inference(rw,[status(thm)],[c_0_72,c_0_74])).

cnf(c_0_87,plain,
    ( k7_relat_1(k6_relat_1(X1),X1) = k6_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_38]),c_0_45])).

cnf(c_0_88,plain,
    ( r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X3),k7_relat_1(k6_relat_1(X3),X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_82]),c_0_51]),c_0_74]),c_0_54]),c_0_38])])).

cnf(c_0_89,plain,
    ( k7_relat_1(k6_relat_1(X1),X2) = k6_relat_1(X1)
    | ~ r1_tarski(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_45]),c_0_38])])).

cnf(c_0_90,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X1),X2)),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_83,c_0_54])])).

cnf(c_0_91,plain,
    ( k7_relat_1(k7_relat_1(X1,X2),X3) = k7_relat_1(X1,k1_setfam_1(k2_enumset1(X2,X2,X2,X3)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_84,c_0_32]),c_0_33])).

cnf(c_0_92,plain,
    ( k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X3)) = k7_relat_1(k7_relat_1(k6_relat_1(X1),X3),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_85]),c_0_67]),c_0_56]),c_0_54]),c_0_38])]),c_0_68]),c_0_74]),c_0_86])).

fof(c_0_93,negated_conjecture,(
    ~ ! [X1,X2] : k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)) = k6_relat_1(k3_xboole_0(X1,X2)) ),
    inference(assume_negation,[status(cth)],[t43_funct_1])).

cnf(c_0_94,plain,
    ( k7_relat_1(k5_relat_1(k6_relat_1(X1),X2),X1) = k5_relat_1(k6_relat_1(X1),X2)
    | ~ v1_relat_1(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_87]),c_0_38])])).

cnf(c_0_95,plain,
    ( r1_tarski(k7_relat_1(k6_relat_1(X1),X2),k7_relat_1(k6_relat_1(X2),X1)) ),
    inference(spm,[status(thm)],[c_0_88,c_0_87])).

cnf(c_0_96,plain,
    ( k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X1),X2))) = k7_relat_1(k6_relat_1(X2),k1_relat_1(k7_relat_1(k6_relat_1(X1),X2))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_90]),c_0_82])).

cnf(c_0_97,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X3) = k7_relat_1(k7_relat_1(k6_relat_1(X1),X3),X2) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_91]),c_0_38])]),c_0_92])).

fof(c_0_98,negated_conjecture,(
    k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0)) != k6_relat_1(k3_xboole_0(esk1_0,esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_93])])])).

cnf(c_0_99,plain,
    ( k7_relat_1(k7_relat_1(X1,X2),X2) = k7_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_94,c_0_29])).

cnf(c_0_100,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X1),X2)),k1_relat_1(k7_relat_1(k6_relat_1(X2),X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_95]),c_0_54]),c_0_54])])).

cnf(c_0_101,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),k1_relat_1(k7_relat_1(k6_relat_1(X2),X1))) = k7_relat_1(k6_relat_1(X1),k1_relat_1(k7_relat_1(k6_relat_1(X2),X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_60]),c_0_96]),c_0_97]),c_0_96])).

cnf(c_0_102,negated_conjecture,
    ( k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0)) != k6_relat_1(k3_xboole_0(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_98])).

fof(c_0_103,plain,(
    ! [X6,X7] : k2_tarski(X6,X7) = k2_tarski(X7,X6) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

cnf(c_0_104,plain,
    ( k7_relat_1(k7_relat_1(X1,X2),k1_setfam_1(k2_enumset1(X2,X2,X2,X3))) = k7_relat_1(k7_relat_1(X1,X2),X3)
    | ~ v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_91,c_0_99])).

cnf(c_0_105,plain,
    ( k7_relat_1(k8_relat_1(X1,k6_relat_1(X2)),X2) = k8_relat_1(X1,k6_relat_1(X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_87]),c_0_51])).

cnf(c_0_106,plain,
    ( k7_relat_1(k6_relat_1(X1),k1_relat_1(k7_relat_1(k6_relat_1(X2),X1))) = k7_relat_1(k6_relat_1(X1),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_100]),c_0_101]),c_0_54])])).

cnf(c_0_107,negated_conjecture,
    ( k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0)) != k6_relat_1(k1_setfam_1(k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_102,c_0_32]),c_0_33])).

cnf(c_0_108,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_103])).

cnf(c_0_109,plain,
    ( k7_relat_1(k6_relat_1(X1),k1_setfam_1(k2_enumset1(X1,X1,X1,X2))) = k7_relat_1(k6_relat_1(X1),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_87]),c_0_38])])).

cnf(c_0_110,plain,
    ( k7_relat_1(k7_relat_1(k7_relat_1(X1,X2),X3),X4) = k7_relat_1(X1,k1_setfam_1(k2_enumset1(k1_setfam_1(k2_enumset1(X2,X2,X2,X3)),k1_setfam_1(k2_enumset1(X2,X2,X2,X3)),k1_setfam_1(k2_enumset1(X2,X2,X2,X3)),X4)))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_91,c_0_91])).

cnf(c_0_111,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X2) = k7_relat_1(k6_relat_1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_105,c_0_47])).

cnf(c_0_112,plain,
    ( k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X1),X2))) = k7_relat_1(k6_relat_1(X2),X1) ),
    inference(rw,[status(thm)],[c_0_96,c_0_106])).

cnf(c_0_113,negated_conjecture,
    ( k6_relat_1(k1_setfam_1(k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0))) != k8_relat_1(esk1_0,k6_relat_1(esk2_0)) ),
    inference(rw,[status(thm)],[c_0_107,c_0_51])).

cnf(c_0_114,plain,
    ( k2_enumset1(X1,X1,X1,X2) = k2_enumset1(X2,X2,X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_108,c_0_25]),c_0_25]),c_0_33]),c_0_33])).

cnf(c_0_115,plain,
    ( k7_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X1,X1,X1,X2))),X3) = k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_110]),c_0_82]),c_0_109]),c_0_111]),c_0_38])])).

cnf(c_0_116,plain,
    ( k6_relat_1(k1_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X3))) = k7_relat_1(k6_relat_1(X3),k1_relat_1(k7_relat_1(k6_relat_1(X2),X1))) ),
    inference(spm,[status(thm)],[c_0_112,c_0_112])).

cnf(c_0_117,negated_conjecture,
    ( k6_relat_1(k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,esk1_0))) != k8_relat_1(esk1_0,k6_relat_1(esk2_0)) ),
    inference(rw,[status(thm)],[c_0_113,c_0_114])).

cnf(c_0_118,plain,
    ( k7_relat_1(k6_relat_1(X1),k1_setfam_1(k2_enumset1(X2,X2,X2,X3))) = k7_relat_1(k6_relat_1(X1),k1_relat_1(k7_relat_1(k6_relat_1(X3),X2))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112,c_0_115]),c_0_116])).

cnf(c_0_119,negated_conjecture,
    ( k6_relat_1(k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,esk1_0))) != k7_relat_1(k6_relat_1(esk2_0),esk1_0) ),
    inference(rw,[status(thm)],[c_0_117,c_0_74])).

cnf(c_0_120,plain,
    ( k6_relat_1(k1_setfam_1(k2_enumset1(X1,X1,X1,X2))) = k7_relat_1(k6_relat_1(X1),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_118]),c_0_115]),c_0_101]),c_0_106])).

cnf(c_0_121,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_119,c_0_120])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:36:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.58  # AutoSched0-Mode selected heuristic H_____042_B03_F1_AE_Q4_SP_S2S
% 0.19/0.58  # and selection function SelectNewComplexAHP.
% 0.19/0.58  #
% 0.19/0.58  # Preprocessing time       : 0.027 s
% 0.19/0.58  
% 0.19/0.58  # Proof found!
% 0.19/0.58  # SZS status Theorem
% 0.19/0.58  # SZS output start CNFRefutation
% 0.19/0.58  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.19/0.58  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.19/0.58  fof(t76_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k5_relat_1(X2,k6_relat_1(X1)),X2)&r1_tarski(k5_relat_1(k6_relat_1(X1),X2),X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_relat_1)).
% 0.19/0.58  fof(t94_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k7_relat_1(X2,X1)=k5_relat_1(k6_relat_1(X1),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 0.19/0.58  fof(fc1_relat_1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k3_xboole_0(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_relat_1)).
% 0.19/0.58  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.19/0.58  fof(t124_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k8_relat_1(X1,X2)=k3_xboole_0(X2,k2_zfmisc_1(k1_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t124_relat_1)).
% 0.19/0.58  fof(dt_k6_relat_1, axiom, ![X1]:v1_relat_1(k6_relat_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 0.19/0.58  fof(t123_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k8_relat_1(X1,X2)=k5_relat_1(X2,k6_relat_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_relat_1)).
% 0.19/0.58  fof(t25_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_tarski(X1,X2)=>(r1_tarski(k1_relat_1(X1),k1_relat_1(X2))&r1_tarski(k2_relat_1(X1),k2_relat_1(X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_relat_1)).
% 0.19/0.58  fof(t71_relat_1, axiom, ![X1]:(k1_relat_1(k6_relat_1(X1))=X1&k2_relat_1(k6_relat_1(X1))=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 0.19/0.58  fof(t54_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>k4_relat_1(k5_relat_1(X1,X2))=k5_relat_1(k4_relat_1(X2),k4_relat_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_relat_1)).
% 0.19/0.58  fof(t72_relat_1, axiom, ![X1]:k4_relat_1(k6_relat_1(X1))=k6_relat_1(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_relat_1)).
% 0.19/0.58  fof(t112_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>k7_relat_1(k5_relat_1(X2,X3),X1)=k5_relat_1(k7_relat_1(X2,X1),X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t112_relat_1)).
% 0.19/0.58  fof(t97_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k1_relat_1(X2),X1)=>k7_relat_1(X2,X1)=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 0.19/0.58  fof(t98_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k7_relat_1(X1,k1_relat_1(X1))=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_relat_1)).
% 0.19/0.58  fof(t100_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>k7_relat_1(k7_relat_1(X3,X1),X2)=k7_relat_1(X3,k3_xboole_0(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_relat_1)).
% 0.19/0.58  fof(t43_funct_1, conjecture, ![X1, X2]:k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))=k6_relat_1(k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_funct_1)).
% 0.19/0.58  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 0.19/0.58  fof(c_0_19, plain, ![X13, X14]:k1_setfam_1(k2_tarski(X13,X14))=k3_xboole_0(X13,X14), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.19/0.58  fof(c_0_20, plain, ![X8, X9]:k1_enumset1(X8,X8,X9)=k2_tarski(X8,X9), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.19/0.58  fof(c_0_21, plain, ![X34, X35]:((r1_tarski(k5_relat_1(X35,k6_relat_1(X34)),X35)|~v1_relat_1(X35))&(r1_tarski(k5_relat_1(k6_relat_1(X34),X35),X35)|~v1_relat_1(X35))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t76_relat_1])])])).
% 0.19/0.58  fof(c_0_22, plain, ![X36, X37]:(~v1_relat_1(X37)|k7_relat_1(X37,X36)=k5_relat_1(k6_relat_1(X36),X37)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).
% 0.19/0.58  fof(c_0_23, plain, ![X16, X17]:(~v1_relat_1(X16)|v1_relat_1(k3_xboole_0(X16,X17))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_relat_1])])).
% 0.19/0.58  cnf(c_0_24, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.58  cnf(c_0_25, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.58  fof(c_0_26, plain, ![X10, X11, X12]:k2_enumset1(X10,X10,X11,X12)=k1_enumset1(X10,X11,X12), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.19/0.58  fof(c_0_27, plain, ![X26, X27]:(~v1_relat_1(X27)|k8_relat_1(X26,X27)=k3_xboole_0(X27,k2_zfmisc_1(k1_relat_1(X27),X26))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t124_relat_1])])).
% 0.19/0.58  cnf(c_0_28, plain, (r1_tarski(k5_relat_1(k6_relat_1(X1),X2),X2)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.58  cnf(c_0_29, plain, (k7_relat_1(X1,X2)=k5_relat_1(k6_relat_1(X2),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.58  fof(c_0_30, plain, ![X15]:v1_relat_1(k6_relat_1(X15)), inference(variable_rename,[status(thm)],[dt_k6_relat_1])).
% 0.19/0.58  cnf(c_0_31, plain, (v1_relat_1(k3_xboole_0(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.58  cnf(c_0_32, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_24, c_0_25])).
% 0.19/0.58  cnf(c_0_33, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.58  cnf(c_0_34, plain, (k8_relat_1(X2,X1)=k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.58  fof(c_0_35, plain, ![X24, X25]:(~v1_relat_1(X25)|k8_relat_1(X24,X25)=k5_relat_1(X25,k6_relat_1(X24))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t123_relat_1])])).
% 0.19/0.58  fof(c_0_36, plain, ![X28, X29]:((r1_tarski(k1_relat_1(X28),k1_relat_1(X29))|~r1_tarski(X28,X29)|~v1_relat_1(X29)|~v1_relat_1(X28))&(r1_tarski(k2_relat_1(X28),k2_relat_1(X29))|~r1_tarski(X28,X29)|~v1_relat_1(X29)|~v1_relat_1(X28))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_relat_1])])])])).
% 0.19/0.58  cnf(c_0_37, plain, (r1_tarski(k7_relat_1(X1,X2),X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.19/0.58  cnf(c_0_38, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.58  fof(c_0_39, plain, ![X32]:(k1_relat_1(k6_relat_1(X32))=X32&k2_relat_1(k6_relat_1(X32))=X32), inference(variable_rename,[status(thm)],[t71_relat_1])).
% 0.19/0.58  cnf(c_0_40, plain, (v1_relat_1(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_32]), c_0_33])).
% 0.19/0.58  cnf(c_0_41, plain, (k8_relat_1(X2,X1)=k1_setfam_1(k2_enumset1(X1,X1,X1,k2_zfmisc_1(k1_relat_1(X1),X2)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_32]), c_0_33])).
% 0.19/0.58  cnf(c_0_42, plain, (k8_relat_1(X2,X1)=k5_relat_1(X1,k6_relat_1(X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.19/0.58  cnf(c_0_43, plain, (r1_tarski(k1_relat_1(X1),k1_relat_1(X2))|~r1_tarski(X1,X2)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.19/0.58  cnf(c_0_44, plain, (r1_tarski(k7_relat_1(k6_relat_1(X1),X2),k6_relat_1(X1))), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.19/0.58  cnf(c_0_45, plain, (k1_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.19/0.58  cnf(c_0_46, plain, (v1_relat_1(k8_relat_1(X1,X2))|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.19/0.58  cnf(c_0_47, plain, (k7_relat_1(k6_relat_1(X1),X2)=k8_relat_1(X1,k6_relat_1(X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_29]), c_0_38]), c_0_38])])).
% 0.19/0.58  fof(c_0_48, plain, ![X30, X31]:(~v1_relat_1(X30)|(~v1_relat_1(X31)|k4_relat_1(k5_relat_1(X30,X31))=k5_relat_1(k4_relat_1(X31),k4_relat_1(X30)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t54_relat_1])])])).
% 0.19/0.58  fof(c_0_49, plain, ![X33]:k4_relat_1(k6_relat_1(X33))=k6_relat_1(X33), inference(variable_rename,[status(thm)],[t72_relat_1])).
% 0.19/0.58  fof(c_0_50, plain, ![X21, X22, X23]:(~v1_relat_1(X22)|(~v1_relat_1(X23)|k7_relat_1(k5_relat_1(X22,X23),X21)=k5_relat_1(k7_relat_1(X22,X21),X23))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t112_relat_1])])])).
% 0.19/0.58  cnf(c_0_51, plain, (k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))=k8_relat_1(X2,k6_relat_1(X1))), inference(spm,[status(thm)],[c_0_42, c_0_38])).
% 0.19/0.58  fof(c_0_52, plain, ![X38, X39]:(~v1_relat_1(X39)|(~r1_tarski(k1_relat_1(X39),X38)|k7_relat_1(X39,X38)=X39)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t97_relat_1])])).
% 0.19/0.58  cnf(c_0_53, plain, (r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X1),X2)),X1)|~v1_relat_1(k7_relat_1(k6_relat_1(X1),X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_45]), c_0_38])])).
% 0.19/0.58  cnf(c_0_54, plain, (v1_relat_1(k7_relat_1(k6_relat_1(X1),X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_38])])).
% 0.19/0.58  cnf(c_0_55, plain, (k4_relat_1(k5_relat_1(X1,X2))=k5_relat_1(k4_relat_1(X2),k4_relat_1(X1))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.19/0.58  cnf(c_0_56, plain, (k4_relat_1(k6_relat_1(X1))=k6_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.19/0.58  cnf(c_0_57, plain, (k7_relat_1(k5_relat_1(X1,X2),X3)=k5_relat_1(k7_relat_1(X1,X3),X2)|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.19/0.58  cnf(c_0_58, plain, (r1_tarski(k8_relat_1(X1,k6_relat_1(X2)),k6_relat_1(X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_38]), c_0_51])).
% 0.19/0.58  cnf(c_0_59, plain, (k7_relat_1(X1,X2)=X1|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.19/0.58  cnf(c_0_60, plain, (r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X1),X2)),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_53, c_0_54])])).
% 0.19/0.58  cnf(c_0_61, plain, (k4_relat_1(k8_relat_1(X1,k6_relat_1(X2)))=k8_relat_1(X2,k6_relat_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_51]), c_0_56]), c_0_56]), c_0_51]), c_0_38]), c_0_38])])).
% 0.19/0.58  cnf(c_0_62, plain, (v1_relat_1(k8_relat_1(X1,k6_relat_1(X2)))), inference(spm,[status(thm)],[c_0_54, c_0_47])).
% 0.19/0.58  cnf(c_0_63, plain, (k5_relat_1(k7_relat_1(k6_relat_1(X1),X2),X3)=k7_relat_1(k5_relat_1(k6_relat_1(X1),X3),X2)|~v1_relat_1(X3)), inference(spm,[status(thm)],[c_0_57, c_0_38])).
% 0.19/0.58  cnf(c_0_64, plain, (r1_tarski(k1_relat_1(k8_relat_1(X1,k6_relat_1(X2))),X1)|~v1_relat_1(k8_relat_1(X1,k6_relat_1(X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_58]), c_0_45]), c_0_38])])).
% 0.19/0.58  cnf(c_0_65, plain, (k4_relat_1(k7_relat_1(X1,X2))=k5_relat_1(k4_relat_1(X1),k6_relat_1(X2))|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_29]), c_0_56]), c_0_38])])).
% 0.19/0.58  cnf(c_0_66, plain, (k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X1)=k7_relat_1(k6_relat_1(X1),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_54])])).
% 0.19/0.58  cnf(c_0_67, plain, (k4_relat_1(k7_relat_1(k6_relat_1(X1),X2))=k8_relat_1(X2,k6_relat_1(X1))), inference(spm,[status(thm)],[c_0_61, c_0_47])).
% 0.19/0.58  cnf(c_0_68, plain, (k5_relat_1(k8_relat_1(X1,k6_relat_1(X2)),k6_relat_1(X3))=k8_relat_1(X3,k8_relat_1(X1,k6_relat_1(X2)))), inference(spm,[status(thm)],[c_0_42, c_0_62])).
% 0.19/0.58  cnf(c_0_69, plain, (k5_relat_1(k7_relat_1(k6_relat_1(X1),X2),k6_relat_1(X3))=k7_relat_1(k8_relat_1(X3,k6_relat_1(X1)),X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_38]), c_0_51])).
% 0.19/0.58  cnf(c_0_70, plain, (r1_tarski(k1_relat_1(k8_relat_1(X1,k6_relat_1(X2))),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_64, c_0_62])])).
% 0.19/0.58  cnf(c_0_71, plain, (k8_relat_1(X1,k8_relat_1(X2,k6_relat_1(X1)))=k8_relat_1(X2,k6_relat_1(X1))), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_67]), c_0_67]), c_0_54])]), c_0_68])).
% 0.19/0.58  cnf(c_0_72, plain, (k8_relat_1(X1,k7_relat_1(k6_relat_1(X2),X3))=k7_relat_1(k8_relat_1(X1,k6_relat_1(X2)),X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_54]), c_0_69])).
% 0.19/0.58  cnf(c_0_73, plain, (k7_relat_1(k8_relat_1(X1,k6_relat_1(X2)),X1)=k8_relat_1(X1,k6_relat_1(X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_70]), c_0_62])])).
% 0.19/0.58  cnf(c_0_74, plain, (k8_relat_1(X1,k6_relat_1(X2))=k7_relat_1(k6_relat_1(X2),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_47]), c_0_72]), c_0_73])).
% 0.19/0.58  cnf(c_0_75, plain, (r1_tarski(k5_relat_1(X1,k6_relat_1(X2)),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.58  fof(c_0_76, plain, ![X40]:(~v1_relat_1(X40)|k7_relat_1(X40,k1_relat_1(X40))=X40), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t98_relat_1])])).
% 0.19/0.58  cnf(c_0_77, plain, (k4_relat_1(k7_relat_1(k6_relat_1(X1),X2))=k7_relat_1(k6_relat_1(X1),X2)), inference(rw,[status(thm)],[c_0_67, c_0_74])).
% 0.19/0.58  cnf(c_0_78, plain, (r1_tarski(k7_relat_1(k6_relat_1(X1),X2),k6_relat_1(X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_29]), c_0_38]), c_0_38])])).
% 0.19/0.58  fof(c_0_79, plain, ![X18, X19, X20]:(~v1_relat_1(X20)|k7_relat_1(k7_relat_1(X20,X18),X19)=k7_relat_1(X20,k3_xboole_0(X18,X19))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t100_relat_1])])).
% 0.19/0.58  cnf(c_0_80, plain, (k7_relat_1(X1,k1_relat_1(X1))=X1|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_76])).
% 0.19/0.58  cnf(c_0_81, plain, (r1_tarski(k7_relat_1(k5_relat_1(X1,k6_relat_1(X2)),X3),k7_relat_1(X1,X3))|~v1_relat_1(k7_relat_1(X1,X3))|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_57]), c_0_38])])).
% 0.19/0.58  cnf(c_0_82, plain, (k7_relat_1(k6_relat_1(X1),X2)=k7_relat_1(k6_relat_1(X2),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61, c_0_74]), c_0_74]), c_0_77])).
% 0.19/0.58  cnf(c_0_83, plain, (r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X1),X2)),X2)|~v1_relat_1(k7_relat_1(k6_relat_1(X1),X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_78]), c_0_45]), c_0_38])])).
% 0.19/0.58  cnf(c_0_84, plain, (k7_relat_1(k7_relat_1(X1,X2),X3)=k7_relat_1(X1,k3_xboole_0(X2,X3))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_79])).
% 0.19/0.58  cnf(c_0_85, plain, (k5_relat_1(k6_relat_1(X1),k7_relat_1(k6_relat_1(X2),X3))=k7_relat_1(k7_relat_1(k6_relat_1(X2),X3),X1)), inference(spm,[status(thm)],[c_0_29, c_0_54])).
% 0.19/0.58  cnf(c_0_86, plain, (k8_relat_1(X1,k7_relat_1(k6_relat_1(X2),X3))=k7_relat_1(k7_relat_1(k6_relat_1(X2),X1),X3)), inference(rw,[status(thm)],[c_0_72, c_0_74])).
% 0.19/0.58  cnf(c_0_87, plain, (k7_relat_1(k6_relat_1(X1),X1)=k6_relat_1(X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_38]), c_0_45])).
% 0.19/0.58  cnf(c_0_88, plain, (r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X3),k7_relat_1(k6_relat_1(X3),X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_82]), c_0_51]), c_0_74]), c_0_54]), c_0_38])])).
% 0.19/0.58  cnf(c_0_89, plain, (k7_relat_1(k6_relat_1(X1),X2)=k6_relat_1(X1)|~r1_tarski(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_45]), c_0_38])])).
% 0.19/0.58  cnf(c_0_90, plain, (r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X1),X2)),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_83, c_0_54])])).
% 0.19/0.58  cnf(c_0_91, plain, (k7_relat_1(k7_relat_1(X1,X2),X3)=k7_relat_1(X1,k1_setfam_1(k2_enumset1(X2,X2,X2,X3)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_84, c_0_32]), c_0_33])).
% 0.19/0.58  cnf(c_0_92, plain, (k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X3))=k7_relat_1(k7_relat_1(k6_relat_1(X1),X3),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_85]), c_0_67]), c_0_56]), c_0_54]), c_0_38])]), c_0_68]), c_0_74]), c_0_86])).
% 0.19/0.58  fof(c_0_93, negated_conjecture, ~(![X1, X2]:k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))=k6_relat_1(k3_xboole_0(X1,X2))), inference(assume_negation,[status(cth)],[t43_funct_1])).
% 0.19/0.58  cnf(c_0_94, plain, (k7_relat_1(k5_relat_1(k6_relat_1(X1),X2),X1)=k5_relat_1(k6_relat_1(X1),X2)|~v1_relat_1(X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_87]), c_0_38])])).
% 0.19/0.58  cnf(c_0_95, plain, (r1_tarski(k7_relat_1(k6_relat_1(X1),X2),k7_relat_1(k6_relat_1(X2),X1))), inference(spm,[status(thm)],[c_0_88, c_0_87])).
% 0.19/0.58  cnf(c_0_96, plain, (k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X1),X2)))=k7_relat_1(k6_relat_1(X2),k1_relat_1(k7_relat_1(k6_relat_1(X1),X2)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_90]), c_0_82])).
% 0.19/0.58  cnf(c_0_97, plain, (k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X3)=k7_relat_1(k7_relat_1(k6_relat_1(X1),X3),X2)), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_91]), c_0_38])]), c_0_92])).
% 0.19/0.58  fof(c_0_98, negated_conjecture, k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0))!=k6_relat_1(k3_xboole_0(esk1_0,esk2_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_93])])])).
% 0.19/0.58  cnf(c_0_99, plain, (k7_relat_1(k7_relat_1(X1,X2),X2)=k7_relat_1(X1,X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_94, c_0_29])).
% 0.19/0.58  cnf(c_0_100, plain, (r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X1),X2)),k1_relat_1(k7_relat_1(k6_relat_1(X2),X1)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_95]), c_0_54]), c_0_54])])).
% 0.19/0.58  cnf(c_0_101, plain, (k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),k1_relat_1(k7_relat_1(k6_relat_1(X2),X1)))=k7_relat_1(k6_relat_1(X1),k1_relat_1(k7_relat_1(k6_relat_1(X2),X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_60]), c_0_96]), c_0_97]), c_0_96])).
% 0.19/0.58  cnf(c_0_102, negated_conjecture, (k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0))!=k6_relat_1(k3_xboole_0(esk1_0,esk2_0))), inference(split_conjunct,[status(thm)],[c_0_98])).
% 0.19/0.58  fof(c_0_103, plain, ![X6, X7]:k2_tarski(X6,X7)=k2_tarski(X7,X6), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 0.19/0.58  cnf(c_0_104, plain, (k7_relat_1(k7_relat_1(X1,X2),k1_setfam_1(k2_enumset1(X2,X2,X2,X3)))=k7_relat_1(k7_relat_1(X1,X2),X3)|~v1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_91, c_0_99])).
% 0.19/0.58  cnf(c_0_105, plain, (k7_relat_1(k8_relat_1(X1,k6_relat_1(X2)),X2)=k8_relat_1(X1,k6_relat_1(X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_87]), c_0_51])).
% 0.19/0.58  cnf(c_0_106, plain, (k7_relat_1(k6_relat_1(X1),k1_relat_1(k7_relat_1(k6_relat_1(X2),X1)))=k7_relat_1(k6_relat_1(X1),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_100]), c_0_101]), c_0_54])])).
% 0.19/0.58  cnf(c_0_107, negated_conjecture, (k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0))!=k6_relat_1(k1_setfam_1(k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_102, c_0_32]), c_0_33])).
% 0.19/0.58  cnf(c_0_108, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_103])).
% 0.19/0.58  cnf(c_0_109, plain, (k7_relat_1(k6_relat_1(X1),k1_setfam_1(k2_enumset1(X1,X1,X1,X2)))=k7_relat_1(k6_relat_1(X1),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104, c_0_87]), c_0_38])])).
% 0.19/0.58  cnf(c_0_110, plain, (k7_relat_1(k7_relat_1(k7_relat_1(X1,X2),X3),X4)=k7_relat_1(X1,k1_setfam_1(k2_enumset1(k1_setfam_1(k2_enumset1(X2,X2,X2,X3)),k1_setfam_1(k2_enumset1(X2,X2,X2,X3)),k1_setfam_1(k2_enumset1(X2,X2,X2,X3)),X4)))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_91, c_0_91])).
% 0.19/0.58  cnf(c_0_111, plain, (k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X2)=k7_relat_1(k6_relat_1(X1),X2)), inference(spm,[status(thm)],[c_0_105, c_0_47])).
% 0.19/0.58  cnf(c_0_112, plain, (k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X1),X2)))=k7_relat_1(k6_relat_1(X2),X1)), inference(rw,[status(thm)],[c_0_96, c_0_106])).
% 0.19/0.58  cnf(c_0_113, negated_conjecture, (k6_relat_1(k1_setfam_1(k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0)))!=k8_relat_1(esk1_0,k6_relat_1(esk2_0))), inference(rw,[status(thm)],[c_0_107, c_0_51])).
% 0.19/0.58  cnf(c_0_114, plain, (k2_enumset1(X1,X1,X1,X2)=k2_enumset1(X2,X2,X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_108, c_0_25]), c_0_25]), c_0_33]), c_0_33])).
% 0.19/0.58  cnf(c_0_115, plain, (k7_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X1,X1,X1,X2))),X3)=k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X3)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109, c_0_110]), c_0_82]), c_0_109]), c_0_111]), c_0_38])])).
% 0.19/0.58  cnf(c_0_116, plain, (k6_relat_1(k1_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X3)))=k7_relat_1(k6_relat_1(X3),k1_relat_1(k7_relat_1(k6_relat_1(X2),X1)))), inference(spm,[status(thm)],[c_0_112, c_0_112])).
% 0.19/0.58  cnf(c_0_117, negated_conjecture, (k6_relat_1(k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,esk1_0)))!=k8_relat_1(esk1_0,k6_relat_1(esk2_0))), inference(rw,[status(thm)],[c_0_113, c_0_114])).
% 0.19/0.58  cnf(c_0_118, plain, (k7_relat_1(k6_relat_1(X1),k1_setfam_1(k2_enumset1(X2,X2,X2,X3)))=k7_relat_1(k6_relat_1(X1),k1_relat_1(k7_relat_1(k6_relat_1(X3),X2)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112, c_0_115]), c_0_116])).
% 0.19/0.58  cnf(c_0_119, negated_conjecture, (k6_relat_1(k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,esk1_0)))!=k7_relat_1(k6_relat_1(esk2_0),esk1_0)), inference(rw,[status(thm)],[c_0_117, c_0_74])).
% 0.19/0.58  cnf(c_0_120, plain, (k6_relat_1(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)))=k7_relat_1(k6_relat_1(X1),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_118]), c_0_115]), c_0_101]), c_0_106])).
% 0.19/0.58  cnf(c_0_121, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_119, c_0_120])]), ['proof']).
% 0.19/0.58  # SZS output end CNFRefutation
% 0.19/0.58  # Proof object total steps             : 122
% 0.19/0.58  # Proof object clause steps            : 83
% 0.19/0.58  # Proof object formula steps           : 39
% 0.19/0.58  # Proof object conjectures             : 9
% 0.19/0.58  # Proof object clause conjectures      : 6
% 0.19/0.58  # Proof object formula conjectures     : 3
% 0.19/0.58  # Proof object initial clauses used    : 20
% 0.19/0.58  # Proof object initial formulas used   : 19
% 0.19/0.58  # Proof object generating inferences   : 46
% 0.19/0.58  # Proof object simplifying inferences  : 115
% 0.19/0.58  # Training examples: 0 positive, 0 negative
% 0.19/0.58  # Parsed axioms                        : 20
% 0.19/0.58  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.58  # Initial clauses                      : 23
% 0.19/0.58  # Removed in clause preprocessing      : 3
% 0.19/0.58  # Initial clauses in saturation        : 20
% 0.19/0.58  # Processed clauses                    : 1622
% 0.19/0.58  # ...of these trivial                  : 292
% 0.19/0.58  # ...subsumed                          : 846
% 0.19/0.58  # ...remaining for further processing  : 484
% 0.19/0.58  # Other redundant clauses eliminated   : 0
% 0.19/0.58  # Clauses deleted for lack of memory   : 0
% 0.19/0.58  # Backward-subsumed                    : 39
% 0.19/0.58  # Backward-rewritten                   : 97
% 0.19/0.58  # Generated clauses                    : 22577
% 0.19/0.58  # ...of the previous two non-trivial   : 18518
% 0.19/0.58  # Contextual simplify-reflections      : 0
% 0.19/0.58  # Paramodulations                      : 22577
% 0.19/0.58  # Factorizations                       : 0
% 0.19/0.58  # Equation resolutions                 : 0
% 0.19/0.58  # Propositional unsat checks           : 0
% 0.19/0.58  #    Propositional check models        : 0
% 0.19/0.58  #    Propositional check unsatisfiable : 0
% 0.19/0.58  #    Propositional clauses             : 0
% 0.19/0.58  #    Propositional clauses after purity: 0
% 0.19/0.58  #    Propositional unsat core size     : 0
% 0.19/0.58  #    Propositional preprocessing time  : 0.000
% 0.19/0.58  #    Propositional encoding time       : 0.000
% 0.19/0.58  #    Propositional solver time         : 0.000
% 0.19/0.58  #    Success case prop preproc time    : 0.000
% 0.19/0.58  #    Success case prop encoding time   : 0.000
% 0.19/0.58  #    Success case prop solver time     : 0.000
% 0.19/0.58  # Current number of processed clauses  : 348
% 0.19/0.58  #    Positive orientable unit clauses  : 115
% 0.19/0.58  #    Positive unorientable unit clauses: 7
% 0.19/0.58  #    Negative unit clauses             : 0
% 0.19/0.58  #    Non-unit-clauses                  : 226
% 0.19/0.58  # Current number of unprocessed clauses: 16228
% 0.19/0.58  # ...number of literals in the above   : 31286
% 0.19/0.58  # Current number of archived formulas  : 0
% 0.19/0.58  # Current number of archived clauses   : 139
% 0.19/0.58  # Clause-clause subsumption calls (NU) : 11663
% 0.19/0.58  # Rec. Clause-clause subsumption calls : 10490
% 0.19/0.58  # Non-unit clause-clause subsumptions  : 793
% 0.19/0.58  # Unit Clause-clause subsumption calls : 87
% 0.19/0.58  # Rewrite failures with RHS unbound    : 0
% 0.19/0.58  # BW rewrite match attempts            : 769
% 0.19/0.58  # BW rewrite match successes           : 169
% 0.19/0.58  # Condensation attempts                : 0
% 0.19/0.58  # Condensation successes               : 0
% 0.19/0.58  # Termbank termtop insertions          : 347414
% 0.19/0.58  
% 0.19/0.58  # -------------------------------------------------
% 0.19/0.58  # User time                : 0.224 s
% 0.19/0.58  # System time              : 0.015 s
% 0.19/0.58  # Total time               : 0.239 s
% 0.19/0.58  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
