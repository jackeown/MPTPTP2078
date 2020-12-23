%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:54:48 EST 2020

% Result     : Theorem 0.78s
% Output     : CNFRefutation 0.78s
% Verified   : 
% Statistics : Number of formulae       :  113 (1158 expanded)
%              Number of clauses        :   74 ( 507 expanded)
%              Number of leaves         :   19 ( 318 expanded)
%              Depth                    :   17
%              Number of atoms          :  231 (2047 expanded)
%              Number of equality atoms :   80 ( 901 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t146_funct_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X1,k1_relat_1(X2))
       => r1_tarski(X1,k10_relat_1(X2,k9_relat_1(X2,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(t139_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => k10_relat_1(k7_relat_1(X3,X1),X2) = k3_xboole_0(X1,k10_relat_1(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).

fof(t87_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k1_relat_1(k7_relat_1(X2,X1)),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t169_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,k2_relat_1(X1)) = k1_relat_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

fof(t189_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k7_relat_1(X1,k1_relat_1(X2)) = k7_relat_1(X1,k1_relat_1(k7_relat_1(X2,k1_relat_1(X1)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t189_relat_1)).

fof(t71_relat_1,axiom,(
    ! [X1] :
      ( k1_relat_1(k6_relat_1(X1)) = X1
      & k2_relat_1(k6_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(dt_k6_relat_1,axiom,(
    ! [X1] : v1_relat_1(k6_relat_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(dt_k7_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k7_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

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

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t146_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,k1_relat_1(X1)) = k2_relat_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

fof(t162_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2,X3] :
          ( r1_tarski(X2,X3)
         => k9_relat_1(k7_relat_1(X1,X3),X2) = k9_relat_1(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_relat_1)).

fof(c_0_19,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X1,k1_relat_1(X2))
         => r1_tarski(X1,k10_relat_1(X2,k9_relat_1(X2,X1))) ) ) ),
    inference(assume_negation,[status(cth)],[t146_funct_1])).

fof(c_0_20,plain,(
    ! [X16,X17] : k1_setfam_1(k2_tarski(X16,X17)) = k3_xboole_0(X16,X17) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_21,plain,(
    ! [X14,X15] : k1_enumset1(X14,X14,X15) = k2_tarski(X14,X15) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_22,plain,(
    ! [X11,X12,X13] :
      ( ~ r1_tarski(X11,X12)
      | ~ r1_tarski(X12,X13)
      | r1_tarski(X11,X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

fof(c_0_23,negated_conjecture,
    ( v1_relat_1(esk2_0)
    & r1_tarski(esk1_0,k1_relat_1(esk2_0))
    & ~ r1_tarski(esk1_0,k10_relat_1(esk2_0,k9_relat_1(esk2_0,esk1_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).

fof(c_0_24,plain,(
    ! [X4] : k3_xboole_0(X4,X4) = X4 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

cnf(c_0_25,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_27,plain,(
    ! [X34,X35,X36] :
      ( ~ v1_relat_1(X36)
      | k10_relat_1(k7_relat_1(X36,X34),X35) = k3_xboole_0(X34,k10_relat_1(X36,X35)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t139_funct_1])])).

cnf(c_0_28,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,negated_conjecture,
    ( r1_tarski(esk1_0,k1_relat_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_30,plain,(
    ! [X29,X30] :
      ( ~ v1_relat_1(X30)
      | r1_tarski(k1_relat_1(k7_relat_1(X30,X29)),X29) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t87_relat_1])])).

cnf(c_0_31,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_32,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_33,plain,
    ( k10_relat_1(k7_relat_1(X1,X2),X3) = k3_xboole_0(X2,k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_34,negated_conjecture,
    ( r1_tarski(X1,k1_relat_1(esk2_0))
    | ~ r1_tarski(X1,esk1_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_35,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_36,plain,(
    ! [X9,X10] : k4_xboole_0(X9,X10) = k5_xboole_0(X9,k3_xboole_0(X9,X10)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_37,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X1)) = X1 ),
    inference(rw,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_38,plain,
    ( k10_relat_1(k7_relat_1(X1,X2),X3) = k1_setfam_1(k1_enumset1(X2,X2,k10_relat_1(X1,X3)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_33,c_0_32])).

fof(c_0_39,plain,(
    ! [X25] :
      ( ~ v1_relat_1(X25)
      | k10_relat_1(X25,k2_relat_1(X25)) = k1_relat_1(X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t169_relat_1])])).

cnf(c_0_40,negated_conjecture,
    ( r1_tarski(X1,k1_relat_1(esk2_0))
    | ~ r1_tarski(X2,esk1_0)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_28,c_0_34])).

fof(c_0_41,plain,(
    ! [X26,X27] :
      ( ~ v1_relat_1(X26)
      | ~ v1_relat_1(X27)
      | k7_relat_1(X26,k1_relat_1(X27)) = k7_relat_1(X26,k1_relat_1(k7_relat_1(X27,k1_relat_1(X26)))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t189_relat_1])])])).

fof(c_0_42,plain,(
    ! [X28] :
      ( k1_relat_1(k6_relat_1(X28)) = X28
      & k2_relat_1(k6_relat_1(X28)) = X28 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

fof(c_0_43,plain,(
    ! [X18] : v1_relat_1(k6_relat_1(X18)) ),
    inference(variable_rename,[status(thm)],[dt_k6_relat_1])).

cnf(c_0_44,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_relat_1(X3)
    | ~ r1_tarski(X1,k1_relat_1(k7_relat_1(X3,X2))) ),
    inference(spm,[status(thm)],[c_0_28,c_0_35])).

fof(c_0_45,plain,(
    ! [X7,X8] :
      ( ( k4_xboole_0(X7,X8) != k1_xboole_0
        | r1_tarski(X7,X8) )
      & ( ~ r1_tarski(X7,X8)
        | k4_xboole_0(X7,X8) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

cnf(c_0_46,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_47,plain,
    ( k10_relat_1(k7_relat_1(X1,k10_relat_1(X1,X2)),X2) = k10_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_48,plain,
    ( k10_relat_1(X1,k2_relat_1(X1)) = k1_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

fof(c_0_49,plain,(
    ! [X19,X20] :
      ( ~ v1_relat_1(X19)
      | v1_relat_1(k7_relat_1(X19,X20)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).

cnf(c_0_50,negated_conjecture,
    ( r1_tarski(X1,k1_relat_1(esk2_0))
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,k1_relat_1(k7_relat_1(X2,esk1_0))) ),
    inference(spm,[status(thm)],[c_0_40,c_0_35])).

cnf(c_0_51,plain,
    ( k7_relat_1(X1,k1_relat_1(X2)) = k7_relat_1(X1,k1_relat_1(k7_relat_1(X2,k1_relat_1(X1))))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_52,plain,
    ( k1_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_53,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_54,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X1,k1_relat_1(k7_relat_1(X2,X3)))),X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_35])).

cnf(c_0_55,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_56,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2))) ),
    inference(rw,[status(thm)],[c_0_46,c_0_32])).

cnf(c_0_57,plain,
    ( k10_relat_1(k7_relat_1(X1,k1_relat_1(X1)),k2_relat_1(X1)) = k1_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_58,plain,
    ( v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

fof(c_0_59,plain,(
    ! [X31,X32] :
      ( ~ v1_relat_1(X32)
      | ~ r1_tarski(k1_relat_1(X32),X31)
      | k7_relat_1(X32,X31) = X32 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t97_relat_1])])).

cnf(c_0_60,negated_conjecture,
    ( r1_tarski(k1_relat_1(k7_relat_1(X1,k1_relat_1(k7_relat_1(X2,esk1_0)))),k1_relat_1(esk2_0))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_50,c_0_35])).

cnf(c_0_61,plain,
    ( k7_relat_1(k6_relat_1(X1),k1_relat_1(k7_relat_1(X2,X1))) = k7_relat_1(k6_relat_1(X1),k1_relat_1(X2))
    | ~ v1_relat_1(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_53])])).

fof(c_0_62,plain,(
    ! [X33] :
      ( ~ v1_relat_1(X33)
      | k7_relat_1(X33,k1_relat_1(X33)) = X33 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t98_relat_1])])).

cnf(c_0_63,plain,
    ( k2_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_64,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X4)
    | ~ r1_tarski(X1,k1_relat_1(k7_relat_1(X4,k1_relat_1(k7_relat_1(X3,X2))))) ),
    inference(spm,[status(thm)],[c_0_28,c_0_54])).

fof(c_0_65,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | X5 != X6 )
      & ( r1_tarski(X6,X5)
        | X5 != X6 )
      & ( ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X5)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_66,plain,
    ( r1_tarski(X1,X2)
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_67,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2))) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_68,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,k1_relat_1(X2))) = k10_relat_1(k7_relat_1(k7_relat_1(X2,k1_relat_1(X2)),X1),k2_relat_1(X2))
    | ~ v1_relat_1(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_57]),c_0_58])).

cnf(c_0_69,plain,
    ( k7_relat_1(X1,X2) = X1
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_70,negated_conjecture,
    ( r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(esk1_0),k1_relat_1(X1))),k1_relat_1(esk2_0))
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_53])])).

cnf(c_0_71,plain,
    ( k7_relat_1(X1,k1_relat_1(X1)) = X1
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_72,plain,
    ( k10_relat_1(k6_relat_1(X1),X1) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_63]),c_0_52]),c_0_53])])).

cnf(c_0_73,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_relat_1(X3)
    | ~ r1_tarski(X1,k1_relat_1(k7_relat_1(k6_relat_1(X2),k1_relat_1(X3)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_61]),c_0_53])])).

cnf(c_0_74,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_75,plain,
    ( r1_tarski(X1,X2)
    | k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2))) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_66,c_0_56])).

cnf(c_0_76,plain,
    ( k5_xboole_0(X1,k10_relat_1(k7_relat_1(X2,X1),X3)) = k1_xboole_0
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,k10_relat_1(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_67,c_0_38])).

cnf(c_0_77,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,k1_relat_1(X2))) = k10_relat_1(k7_relat_1(X2,k1_relat_1(X2)),k2_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(k1_relat_1(k7_relat_1(X2,k1_relat_1(X2))),X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_58])).

cnf(c_0_78,negated_conjecture,
    ( r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(esk1_0),X1)),k1_relat_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_52]),c_0_53])])).

cnf(c_0_79,plain,
    ( k7_relat_1(k6_relat_1(X1),X1) = k6_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_52]),c_0_53])])).

cnf(c_0_80,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k10_relat_1(k7_relat_1(k6_relat_1(X2),X1),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_72]),c_0_53])])).

cnf(c_0_81,plain,
    ( v1_relat_1(k7_relat_1(k6_relat_1(X1),k1_relat_1(X2)))
    | ~ v1_relat_1(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_61]),c_0_53])])).

cnf(c_0_82,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k1_relat_1(k7_relat_1(k6_relat_1(X2),X3))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_52]),c_0_53])])).

cnf(c_0_83,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_74])).

cnf(c_0_84,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_85,plain,
    ( r1_tarski(X1,k10_relat_1(X2,X3))
    | k5_xboole_0(X1,k10_relat_1(k7_relat_1(X2,X1),X3)) != k1_xboole_0
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_75,c_0_38])).

cnf(c_0_86,plain,
    ( k5_xboole_0(k1_relat_1(X1),k10_relat_1(X1,X2)) = k1_xboole_0
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),k10_relat_1(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_76,c_0_71])).

cnf(c_0_87,negated_conjecture,
    ( k10_relat_1(k7_relat_1(k6_relat_1(esk1_0),k1_relat_1(esk2_0)),esk1_0) = esk1_0 ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_52]),c_0_52]),c_0_79]),c_0_63]),c_0_72]),c_0_53])]),c_0_80])).

cnf(c_0_88,plain,
    ( v1_relat_1(k7_relat_1(k6_relat_1(X1),X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_52]),c_0_53])])).

cnf(c_0_89,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X1),X2)),X1) ),
    inference(spm,[status(thm)],[c_0_82,c_0_83])).

cnf(c_0_90,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = X2
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,k1_relat_1(k7_relat_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_84,c_0_35])).

cnf(c_0_91,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X1,k1_relat_1(X2))),k1_relat_1(k7_relat_1(X2,k1_relat_1(X1))))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_35,c_0_51])).

cnf(c_0_92,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X1,k1_relat_1(X2))),k10_relat_1(X2,X3))
    | k5_xboole_0(k1_relat_1(k7_relat_1(X1,k1_relat_1(X2))),k10_relat_1(k7_relat_1(X2,k1_relat_1(X1)),X3)) != k1_xboole_0
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_85,c_0_51])).

cnf(c_0_93,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_94,negated_conjecture,
    ( k5_xboole_0(k1_relat_1(k7_relat_1(k6_relat_1(esk1_0),k1_relat_1(esk2_0))),esk1_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_87]),c_0_88]),c_0_89])])).

cnf(c_0_95,plain,
    ( k1_relat_1(k7_relat_1(X1,k1_relat_1(X2))) = k1_relat_1(k7_relat_1(X2,k1_relat_1(X1)))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_51]),c_0_91])).

cnf(c_0_96,negated_conjecture,
    ( r1_tarski(k1_relat_1(k7_relat_1(esk2_0,esk1_0)),esk1_0)
    | k5_xboole_0(k1_relat_1(k7_relat_1(esk2_0,esk1_0)),esk1_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_87]),c_0_52]),c_0_72]),c_0_52]),c_0_53]),c_0_93])])).

cnf(c_0_97,negated_conjecture,
    ( k5_xboole_0(k1_relat_1(k7_relat_1(esk2_0,esk1_0)),esk1_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_95]),c_0_52]),c_0_93]),c_0_53])])).

fof(c_0_98,plain,(
    ! [X21] :
      ( ~ v1_relat_1(X21)
      | k9_relat_1(X21,k1_relat_1(X21)) = k2_relat_1(X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_relat_1])])).

fof(c_0_99,plain,(
    ! [X22,X23,X24] :
      ( ~ v1_relat_1(X22)
      | ~ r1_tarski(X23,X24)
      | k9_relat_1(k7_relat_1(X22,X24),X23) = k9_relat_1(X22,X23) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t162_relat_1])])])).

cnf(c_0_100,negated_conjecture,
    ( r1_tarski(k1_relat_1(k7_relat_1(esk2_0,esk1_0)),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_96,c_0_97])])).

cnf(c_0_101,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X1),k1_relat_1(X2))),k1_relat_1(k7_relat_1(X2,X1)))
    | ~ v1_relat_1(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_52]),c_0_53])])).

cnf(c_0_102,plain,
    ( k9_relat_1(X1,k1_relat_1(X1)) = k2_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_98])).

cnf(c_0_103,plain,
    ( k9_relat_1(k7_relat_1(X1,X3),X2) = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_99])).

cnf(c_0_104,negated_conjecture,
    ( k1_relat_1(k7_relat_1(esk2_0,esk1_0)) = esk1_0
    | ~ r1_tarski(esk1_0,k1_relat_1(k7_relat_1(esk2_0,esk1_0))) ),
    inference(spm,[status(thm)],[c_0_84,c_0_100])).

cnf(c_0_105,plain,
    ( r1_tarski(X1,k1_relat_1(k7_relat_1(X2,X1)))
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,k1_relat_1(X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_69]),c_0_52]),c_0_53]),c_0_52])])).

cnf(c_0_106,plain,
    ( k9_relat_1(X1,k1_relat_1(k7_relat_1(X1,X2))) = k2_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_103]),c_0_35]),c_0_58])).

cnf(c_0_107,negated_conjecture,
    ( k1_relat_1(k7_relat_1(esk2_0,esk1_0)) = esk1_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_105]),c_0_93]),c_0_29])])).

cnf(c_0_108,plain,
    ( r1_tarski(X1,k10_relat_1(X2,k2_relat_1(k7_relat_1(X2,X1))))
    | k5_xboole_0(X1,k1_relat_1(k7_relat_1(X2,X1))) != k1_xboole_0
    | ~ v1_relat_1(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_48]),c_0_58])).

cnf(c_0_109,negated_conjecture,
    ( k2_relat_1(k7_relat_1(esk2_0,esk1_0)) = k9_relat_1(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_107]),c_0_93])])).

cnf(c_0_110,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_37]),c_0_83])])).

cnf(c_0_111,negated_conjecture,
    ( ~ r1_tarski(esk1_0,k10_relat_1(esk2_0,k9_relat_1(esk2_0,esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_112,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_109]),c_0_107]),c_0_110]),c_0_93])]),c_0_111]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n011.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:35:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.78/0.98  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.78/0.98  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.78/0.98  #
% 0.78/0.98  # Preprocessing time       : 0.041 s
% 0.78/0.98  # Presaturation interreduction done
% 0.78/0.98  
% 0.78/0.98  # Proof found!
% 0.78/0.98  # SZS status Theorem
% 0.78/0.98  # SZS output start CNFRefutation
% 0.78/0.98  fof(t146_funct_1, conjecture, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(X1,k1_relat_1(X2))=>r1_tarski(X1,k10_relat_1(X2,k9_relat_1(X2,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_funct_1)).
% 0.78/0.98  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.78/0.98  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.78/0.98  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 0.78/0.98  fof(idempotence_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 0.78/0.98  fof(t139_funct_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>k10_relat_1(k7_relat_1(X3,X1),X2)=k3_xboole_0(X1,k10_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t139_funct_1)).
% 0.78/0.98  fof(t87_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k1_relat_1(k7_relat_1(X2,X1)),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 0.78/0.98  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.78/0.98  fof(t169_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k10_relat_1(X1,k2_relat_1(X1))=k1_relat_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 0.78/0.98  fof(t189_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>k7_relat_1(X1,k1_relat_1(X2))=k7_relat_1(X1,k1_relat_1(k7_relat_1(X2,k1_relat_1(X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t189_relat_1)).
% 0.78/0.98  fof(t71_relat_1, axiom, ![X1]:(k1_relat_1(k6_relat_1(X1))=X1&k2_relat_1(k6_relat_1(X1))=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 0.78/0.98  fof(dt_k6_relat_1, axiom, ![X1]:v1_relat_1(k6_relat_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 0.78/0.98  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.78/0.98  fof(dt_k7_relat_1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k7_relat_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 0.78/0.98  fof(t97_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k1_relat_1(X2),X1)=>k7_relat_1(X2,X1)=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 0.78/0.98  fof(t98_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k7_relat_1(X1,k1_relat_1(X1))=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_relat_1)).
% 0.78/0.98  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.78/0.98  fof(t146_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k9_relat_1(X1,k1_relat_1(X1))=k2_relat_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 0.78/0.98  fof(t162_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2, X3]:(r1_tarski(X2,X3)=>k9_relat_1(k7_relat_1(X1,X3),X2)=k9_relat_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t162_relat_1)).
% 0.78/0.98  fof(c_0_19, negated_conjecture, ~(![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(X1,k1_relat_1(X2))=>r1_tarski(X1,k10_relat_1(X2,k9_relat_1(X2,X1)))))), inference(assume_negation,[status(cth)],[t146_funct_1])).
% 0.78/0.98  fof(c_0_20, plain, ![X16, X17]:k1_setfam_1(k2_tarski(X16,X17))=k3_xboole_0(X16,X17), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.78/0.98  fof(c_0_21, plain, ![X14, X15]:k1_enumset1(X14,X14,X15)=k2_tarski(X14,X15), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.78/0.98  fof(c_0_22, plain, ![X11, X12, X13]:(~r1_tarski(X11,X12)|~r1_tarski(X12,X13)|r1_tarski(X11,X13)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 0.78/0.98  fof(c_0_23, negated_conjecture, (v1_relat_1(esk2_0)&(r1_tarski(esk1_0,k1_relat_1(esk2_0))&~r1_tarski(esk1_0,k10_relat_1(esk2_0,k9_relat_1(esk2_0,esk1_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).
% 0.78/0.98  fof(c_0_24, plain, ![X4]:k3_xboole_0(X4,X4)=X4, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).
% 0.78/0.98  cnf(c_0_25, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.78/0.98  cnf(c_0_26, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.78/0.98  fof(c_0_27, plain, ![X34, X35, X36]:(~v1_relat_1(X36)|k10_relat_1(k7_relat_1(X36,X34),X35)=k3_xboole_0(X34,k10_relat_1(X36,X35))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t139_funct_1])])).
% 0.78/0.98  cnf(c_0_28, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.78/0.98  cnf(c_0_29, negated_conjecture, (r1_tarski(esk1_0,k1_relat_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.78/0.98  fof(c_0_30, plain, ![X29, X30]:(~v1_relat_1(X30)|r1_tarski(k1_relat_1(k7_relat_1(X30,X29)),X29)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t87_relat_1])])).
% 0.78/0.98  cnf(c_0_31, plain, (k3_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.78/0.98  cnf(c_0_32, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_25, c_0_26])).
% 0.78/0.98  cnf(c_0_33, plain, (k10_relat_1(k7_relat_1(X1,X2),X3)=k3_xboole_0(X2,k10_relat_1(X1,X3))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.78/0.98  cnf(c_0_34, negated_conjecture, (r1_tarski(X1,k1_relat_1(esk2_0))|~r1_tarski(X1,esk1_0)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.78/0.98  cnf(c_0_35, plain, (r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.78/0.98  fof(c_0_36, plain, ![X9, X10]:k4_xboole_0(X9,X10)=k5_xboole_0(X9,k3_xboole_0(X9,X10)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.78/0.98  cnf(c_0_37, plain, (k1_setfam_1(k1_enumset1(X1,X1,X1))=X1), inference(rw,[status(thm)],[c_0_31, c_0_32])).
% 0.78/0.98  cnf(c_0_38, plain, (k10_relat_1(k7_relat_1(X1,X2),X3)=k1_setfam_1(k1_enumset1(X2,X2,k10_relat_1(X1,X3)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_33, c_0_32])).
% 0.78/0.98  fof(c_0_39, plain, ![X25]:(~v1_relat_1(X25)|k10_relat_1(X25,k2_relat_1(X25))=k1_relat_1(X25)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t169_relat_1])])).
% 0.78/0.98  cnf(c_0_40, negated_conjecture, (r1_tarski(X1,k1_relat_1(esk2_0))|~r1_tarski(X2,esk1_0)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_28, c_0_34])).
% 0.78/0.98  fof(c_0_41, plain, ![X26, X27]:(~v1_relat_1(X26)|(~v1_relat_1(X27)|k7_relat_1(X26,k1_relat_1(X27))=k7_relat_1(X26,k1_relat_1(k7_relat_1(X27,k1_relat_1(X26)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t189_relat_1])])])).
% 0.78/0.98  fof(c_0_42, plain, ![X28]:(k1_relat_1(k6_relat_1(X28))=X28&k2_relat_1(k6_relat_1(X28))=X28), inference(variable_rename,[status(thm)],[t71_relat_1])).
% 0.78/0.98  fof(c_0_43, plain, ![X18]:v1_relat_1(k6_relat_1(X18)), inference(variable_rename,[status(thm)],[dt_k6_relat_1])).
% 0.78/0.98  cnf(c_0_44, plain, (r1_tarski(X1,X2)|~v1_relat_1(X3)|~r1_tarski(X1,k1_relat_1(k7_relat_1(X3,X2)))), inference(spm,[status(thm)],[c_0_28, c_0_35])).
% 0.78/0.98  fof(c_0_45, plain, ![X7, X8]:((k4_xboole_0(X7,X8)!=k1_xboole_0|r1_tarski(X7,X8))&(~r1_tarski(X7,X8)|k4_xboole_0(X7,X8)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.78/0.98  cnf(c_0_46, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.78/0.98  cnf(c_0_47, plain, (k10_relat_1(k7_relat_1(X1,k10_relat_1(X1,X2)),X2)=k10_relat_1(X1,X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.78/0.98  cnf(c_0_48, plain, (k10_relat_1(X1,k2_relat_1(X1))=k1_relat_1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.78/0.98  fof(c_0_49, plain, ![X19, X20]:(~v1_relat_1(X19)|v1_relat_1(k7_relat_1(X19,X20))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).
% 0.78/0.98  cnf(c_0_50, negated_conjecture, (r1_tarski(X1,k1_relat_1(esk2_0))|~v1_relat_1(X2)|~r1_tarski(X1,k1_relat_1(k7_relat_1(X2,esk1_0)))), inference(spm,[status(thm)],[c_0_40, c_0_35])).
% 0.78/0.98  cnf(c_0_51, plain, (k7_relat_1(X1,k1_relat_1(X2))=k7_relat_1(X1,k1_relat_1(k7_relat_1(X2,k1_relat_1(X1))))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.78/0.98  cnf(c_0_52, plain, (k1_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.78/0.98  cnf(c_0_53, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.78/0.98  cnf(c_0_54, plain, (r1_tarski(k1_relat_1(k7_relat_1(X1,k1_relat_1(k7_relat_1(X2,X3)))),X3)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_44, c_0_35])).
% 0.78/0.98  cnf(c_0_55, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.78/0.98  cnf(c_0_56, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2)))), inference(rw,[status(thm)],[c_0_46, c_0_32])).
% 0.78/0.98  cnf(c_0_57, plain, (k10_relat_1(k7_relat_1(X1,k1_relat_1(X1)),k2_relat_1(X1))=k1_relat_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.78/0.98  cnf(c_0_58, plain, (v1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.78/0.98  fof(c_0_59, plain, ![X31, X32]:(~v1_relat_1(X32)|(~r1_tarski(k1_relat_1(X32),X31)|k7_relat_1(X32,X31)=X32)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t97_relat_1])])).
% 0.78/0.98  cnf(c_0_60, negated_conjecture, (r1_tarski(k1_relat_1(k7_relat_1(X1,k1_relat_1(k7_relat_1(X2,esk1_0)))),k1_relat_1(esk2_0))|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_50, c_0_35])).
% 0.78/0.98  cnf(c_0_61, plain, (k7_relat_1(k6_relat_1(X1),k1_relat_1(k7_relat_1(X2,X1)))=k7_relat_1(k6_relat_1(X1),k1_relat_1(X2))|~v1_relat_1(X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_53])])).
% 0.78/0.98  fof(c_0_62, plain, ![X33]:(~v1_relat_1(X33)|k7_relat_1(X33,k1_relat_1(X33))=X33), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t98_relat_1])])).
% 0.78/0.98  cnf(c_0_63, plain, (k2_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.78/0.98  cnf(c_0_64, plain, (r1_tarski(X1,X2)|~v1_relat_1(X3)|~v1_relat_1(X4)|~r1_tarski(X1,k1_relat_1(k7_relat_1(X4,k1_relat_1(k7_relat_1(X3,X2)))))), inference(spm,[status(thm)],[c_0_28, c_0_54])).
% 0.78/0.98  fof(c_0_65, plain, ![X5, X6]:(((r1_tarski(X5,X6)|X5!=X6)&(r1_tarski(X6,X5)|X5!=X6))&(~r1_tarski(X5,X6)|~r1_tarski(X6,X5)|X5=X6)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.78/0.98  cnf(c_0_66, plain, (r1_tarski(X1,X2)|k4_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.78/0.98  cnf(c_0_67, plain, (k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2)))=k1_xboole_0|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_55, c_0_56])).
% 0.78/0.98  cnf(c_0_68, plain, (k1_setfam_1(k1_enumset1(X1,X1,k1_relat_1(X2)))=k10_relat_1(k7_relat_1(k7_relat_1(X2,k1_relat_1(X2)),X1),k2_relat_1(X2))|~v1_relat_1(X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_57]), c_0_58])).
% 0.78/0.98  cnf(c_0_69, plain, (k7_relat_1(X1,X2)=X1|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.78/0.98  cnf(c_0_70, negated_conjecture, (r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(esk1_0),k1_relat_1(X1))),k1_relat_1(esk2_0))|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_53])])).
% 0.78/0.98  cnf(c_0_71, plain, (k7_relat_1(X1,k1_relat_1(X1))=X1|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.78/0.98  cnf(c_0_72, plain, (k10_relat_1(k6_relat_1(X1),X1)=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_63]), c_0_52]), c_0_53])])).
% 0.78/0.98  cnf(c_0_73, plain, (r1_tarski(X1,X2)|~v1_relat_1(X3)|~r1_tarski(X1,k1_relat_1(k7_relat_1(k6_relat_1(X2),k1_relat_1(X3))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_61]), c_0_53])])).
% 0.78/0.98  cnf(c_0_74, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.78/0.98  cnf(c_0_75, plain, (r1_tarski(X1,X2)|k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2)))!=k1_xboole_0), inference(rw,[status(thm)],[c_0_66, c_0_56])).
% 0.78/0.98  cnf(c_0_76, plain, (k5_xboole_0(X1,k10_relat_1(k7_relat_1(X2,X1),X3))=k1_xboole_0|~v1_relat_1(X2)|~r1_tarski(X1,k10_relat_1(X2,X3))), inference(spm,[status(thm)],[c_0_67, c_0_38])).
% 0.78/0.98  cnf(c_0_77, plain, (k1_setfam_1(k1_enumset1(X1,X1,k1_relat_1(X2)))=k10_relat_1(k7_relat_1(X2,k1_relat_1(X2)),k2_relat_1(X2))|~v1_relat_1(X2)|~r1_tarski(k1_relat_1(k7_relat_1(X2,k1_relat_1(X2))),X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_58])).
% 0.78/0.98  cnf(c_0_78, negated_conjecture, (r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(esk1_0),X1)),k1_relat_1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_52]), c_0_53])])).
% 0.78/0.98  cnf(c_0_79, plain, (k7_relat_1(k6_relat_1(X1),X1)=k6_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_52]), c_0_53])])).
% 0.78/0.98  cnf(c_0_80, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k10_relat_1(k7_relat_1(k6_relat_1(X2),X1),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_72]), c_0_53])])).
% 0.78/0.98  cnf(c_0_81, plain, (v1_relat_1(k7_relat_1(k6_relat_1(X1),k1_relat_1(X2)))|~v1_relat_1(X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_61]), c_0_53])])).
% 0.78/0.98  cnf(c_0_82, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k1_relat_1(k7_relat_1(k6_relat_1(X2),X3)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_52]), c_0_53])])).
% 0.78/0.98  cnf(c_0_83, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_74])).
% 0.78/0.98  cnf(c_0_84, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.78/0.98  cnf(c_0_85, plain, (r1_tarski(X1,k10_relat_1(X2,X3))|k5_xboole_0(X1,k10_relat_1(k7_relat_1(X2,X1),X3))!=k1_xboole_0|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_75, c_0_38])).
% 0.78/0.98  cnf(c_0_86, plain, (k5_xboole_0(k1_relat_1(X1),k10_relat_1(X1,X2))=k1_xboole_0|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),k10_relat_1(X1,X2))), inference(spm,[status(thm)],[c_0_76, c_0_71])).
% 0.78/0.98  cnf(c_0_87, negated_conjecture, (k10_relat_1(k7_relat_1(k6_relat_1(esk1_0),k1_relat_1(esk2_0)),esk1_0)=esk1_0), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_78]), c_0_52]), c_0_52]), c_0_79]), c_0_63]), c_0_72]), c_0_53])]), c_0_80])).
% 0.78/0.98  cnf(c_0_88, plain, (v1_relat_1(k7_relat_1(k6_relat_1(X1),X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_52]), c_0_53])])).
% 0.78/0.98  cnf(c_0_89, plain, (r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X1),X2)),X1)), inference(spm,[status(thm)],[c_0_82, c_0_83])).
% 0.78/0.98  cnf(c_0_90, plain, (k1_relat_1(k7_relat_1(X1,X2))=X2|~v1_relat_1(X1)|~r1_tarski(X2,k1_relat_1(k7_relat_1(X1,X2)))), inference(spm,[status(thm)],[c_0_84, c_0_35])).
% 0.78/0.98  cnf(c_0_91, plain, (r1_tarski(k1_relat_1(k7_relat_1(X1,k1_relat_1(X2))),k1_relat_1(k7_relat_1(X2,k1_relat_1(X1))))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_35, c_0_51])).
% 0.78/0.98  cnf(c_0_92, plain, (r1_tarski(k1_relat_1(k7_relat_1(X1,k1_relat_1(X2))),k10_relat_1(X2,X3))|k5_xboole_0(k1_relat_1(k7_relat_1(X1,k1_relat_1(X2))),k10_relat_1(k7_relat_1(X2,k1_relat_1(X1)),X3))!=k1_xboole_0|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_85, c_0_51])).
% 0.78/0.98  cnf(c_0_93, negated_conjecture, (v1_relat_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.78/0.98  cnf(c_0_94, negated_conjecture, (k5_xboole_0(k1_relat_1(k7_relat_1(k6_relat_1(esk1_0),k1_relat_1(esk2_0))),esk1_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_87]), c_0_88]), c_0_89])])).
% 0.78/0.98  cnf(c_0_95, plain, (k1_relat_1(k7_relat_1(X1,k1_relat_1(X2)))=k1_relat_1(k7_relat_1(X2,k1_relat_1(X1)))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_51]), c_0_91])).
% 0.78/0.98  cnf(c_0_96, negated_conjecture, (r1_tarski(k1_relat_1(k7_relat_1(esk2_0,esk1_0)),esk1_0)|k5_xboole_0(k1_relat_1(k7_relat_1(esk2_0,esk1_0)),esk1_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_87]), c_0_52]), c_0_72]), c_0_52]), c_0_53]), c_0_93])])).
% 0.78/0.98  cnf(c_0_97, negated_conjecture, (k5_xboole_0(k1_relat_1(k7_relat_1(esk2_0,esk1_0)),esk1_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_95]), c_0_52]), c_0_93]), c_0_53])])).
% 0.78/0.98  fof(c_0_98, plain, ![X21]:(~v1_relat_1(X21)|k9_relat_1(X21,k1_relat_1(X21))=k2_relat_1(X21)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_relat_1])])).
% 0.78/0.98  fof(c_0_99, plain, ![X22, X23, X24]:(~v1_relat_1(X22)|(~r1_tarski(X23,X24)|k9_relat_1(k7_relat_1(X22,X24),X23)=k9_relat_1(X22,X23))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t162_relat_1])])])).
% 0.78/0.98  cnf(c_0_100, negated_conjecture, (r1_tarski(k1_relat_1(k7_relat_1(esk2_0,esk1_0)),esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_96, c_0_97])])).
% 0.78/0.98  cnf(c_0_101, plain, (r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X1),k1_relat_1(X2))),k1_relat_1(k7_relat_1(X2,X1)))|~v1_relat_1(X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_52]), c_0_53])])).
% 0.78/0.98  cnf(c_0_102, plain, (k9_relat_1(X1,k1_relat_1(X1))=k2_relat_1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_98])).
% 0.78/0.98  cnf(c_0_103, plain, (k9_relat_1(k7_relat_1(X1,X3),X2)=k9_relat_1(X1,X2)|~v1_relat_1(X1)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_99])).
% 0.78/0.98  cnf(c_0_104, negated_conjecture, (k1_relat_1(k7_relat_1(esk2_0,esk1_0))=esk1_0|~r1_tarski(esk1_0,k1_relat_1(k7_relat_1(esk2_0,esk1_0)))), inference(spm,[status(thm)],[c_0_84, c_0_100])).
% 0.78/0.98  cnf(c_0_105, plain, (r1_tarski(X1,k1_relat_1(k7_relat_1(X2,X1)))|~v1_relat_1(X2)|~r1_tarski(X1,k1_relat_1(X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101, c_0_69]), c_0_52]), c_0_53]), c_0_52])])).
% 0.78/0.98  cnf(c_0_106, plain, (k9_relat_1(X1,k1_relat_1(k7_relat_1(X1,X2)))=k2_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_102, c_0_103]), c_0_35]), c_0_58])).
% 0.78/0.98  cnf(c_0_107, negated_conjecture, (k1_relat_1(k7_relat_1(esk2_0,esk1_0))=esk1_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104, c_0_105]), c_0_93]), c_0_29])])).
% 0.78/0.98  cnf(c_0_108, plain, (r1_tarski(X1,k10_relat_1(X2,k2_relat_1(k7_relat_1(X2,X1))))|k5_xboole_0(X1,k1_relat_1(k7_relat_1(X2,X1)))!=k1_xboole_0|~v1_relat_1(X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_48]), c_0_58])).
% 0.78/0.98  cnf(c_0_109, negated_conjecture, (k2_relat_1(k7_relat_1(esk2_0,esk1_0))=k9_relat_1(esk2_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106, c_0_107]), c_0_93])])).
% 0.78/0.98  cnf(c_0_110, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_37]), c_0_83])])).
% 0.78/0.98  cnf(c_0_111, negated_conjecture, (~r1_tarski(esk1_0,k10_relat_1(esk2_0,k9_relat_1(esk2_0,esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.78/0.98  cnf(c_0_112, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108, c_0_109]), c_0_107]), c_0_110]), c_0_93])]), c_0_111]), ['proof']).
% 0.78/0.98  # SZS output end CNFRefutation
% 0.78/0.98  # Proof object total steps             : 113
% 0.78/0.98  # Proof object clause steps            : 74
% 0.78/0.98  # Proof object formula steps           : 39
% 0.78/0.98  # Proof object conjectures             : 21
% 0.78/0.98  # Proof object clause conjectures      : 18
% 0.78/0.98  # Proof object formula conjectures     : 3
% 0.78/0.98  # Proof object initial clauses used    : 24
% 0.78/0.98  # Proof object initial formulas used   : 19
% 0.78/0.98  # Proof object generating inferences   : 42
% 0.78/0.98  # Proof object simplifying inferences  : 75
% 0.78/0.98  # Training examples: 0 positive, 0 negative
% 0.78/0.98  # Parsed axioms                        : 19
% 0.78/0.98  # Removed by relevancy pruning/SinE    : 0
% 0.78/0.98  # Initial clauses                      : 25
% 0.78/0.98  # Removed in clause preprocessing      : 3
% 0.78/0.98  # Initial clauses in saturation        : 22
% 0.78/0.98  # Processed clauses                    : 4704
% 0.78/0.98  # ...of these trivial                  : 14
% 0.78/0.98  # ...subsumed                          : 4002
% 0.78/0.98  # ...remaining for further processing  : 688
% 0.78/0.98  # Other redundant clauses eliminated   : 2
% 0.78/0.98  # Clauses deleted for lack of memory   : 0
% 0.78/0.98  # Backward-subsumed                    : 37
% 0.78/0.98  # Backward-rewritten                   : 11
% 0.78/0.98  # Generated clauses                    : 41995
% 0.78/0.98  # ...of the previous two non-trivial   : 39263
% 0.78/0.98  # Contextual simplify-reflections      : 128
% 0.78/0.98  # Paramodulations                      : 41993
% 0.78/0.98  # Factorizations                       : 0
% 0.78/0.98  # Equation resolutions                 : 2
% 0.78/0.98  # Propositional unsat checks           : 0
% 0.78/0.98  #    Propositional check models        : 0
% 0.78/0.98  #    Propositional check unsatisfiable : 0
% 0.78/0.98  #    Propositional clauses             : 0
% 0.78/0.98  #    Propositional clauses after purity: 0
% 0.78/0.98  #    Propositional unsat core size     : 0
% 0.78/0.98  #    Propositional preprocessing time  : 0.000
% 0.78/0.98  #    Propositional encoding time       : 0.000
% 0.78/0.98  #    Propositional solver time         : 0.000
% 0.78/0.98  #    Success case prop preproc time    : 0.000
% 0.78/0.98  #    Success case prop encoding time   : 0.000
% 0.78/0.98  #    Success case prop solver time     : 0.000
% 0.78/0.98  # Current number of processed clauses  : 617
% 0.78/0.98  #    Positive orientable unit clauses  : 47
% 0.78/0.98  #    Positive unorientable unit clauses: 3
% 0.78/0.98  #    Negative unit clauses             : 3
% 0.78/0.98  #    Non-unit-clauses                  : 564
% 0.78/0.98  # Current number of unprocessed clauses: 34430
% 0.78/0.98  # ...number of literals in the above   : 144747
% 0.78/0.98  # Current number of archived formulas  : 0
% 0.78/0.98  # Current number of archived clauses   : 72
% 0.78/0.98  # Clause-clause subsumption calls (NU) : 72195
% 0.78/0.98  # Rec. Clause-clause subsumption calls : 36784
% 0.78/0.98  # Non-unit clause-clause subsumptions  : 2977
% 0.78/0.98  # Unit Clause-clause subsumption calls : 476
% 0.78/0.98  # Rewrite failures with RHS unbound    : 0
% 0.78/0.98  # BW rewrite match attempts            : 358
% 0.78/0.98  # BW rewrite match successes           : 18
% 0.78/0.98  # Condensation attempts                : 0
% 0.78/0.98  # Condensation successes               : 0
% 0.78/0.98  # Termbank termtop insertions          : 966756
% 0.78/0.98  
% 0.78/0.98  # -------------------------------------------------
% 0.78/0.98  # User time                : 0.584 s
% 0.78/0.98  # System time              : 0.027 s
% 0.78/0.98  # Total time               : 0.611 s
% 0.78/0.98  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
