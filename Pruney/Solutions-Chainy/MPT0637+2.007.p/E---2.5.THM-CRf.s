%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:53:25 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   87 (1136 expanded)
%              Number of clauses        :   52 ( 509 expanded)
%              Number of leaves         :   17 ( 313 expanded)
%              Depth                    :   17
%              Number of atoms          :  155 (1685 expanded)
%              Number of equality atoms :   68 ( 840 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(fc1_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_relat_1)).

fof(t100_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => k7_relat_1(k7_relat_1(X3,X1),X2) = k7_relat_1(X3,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).

fof(t192_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,X1) = k7_relat_1(X2,k3_xboole_0(k1_relat_1(X2),X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t192_relat_1)).

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

fof(t71_relat_1,axiom,(
    ! [X1] :
      ( k1_relat_1(k6_relat_1(X1)) = X1
      & k2_relat_1(k6_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(dt_k6_relat_1,axiom,(
    ! [X1] : v1_relat_1(k6_relat_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(t80_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k5_relat_1(X1,k6_relat_1(k2_relat_1(X1))) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

fof(t55_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( v1_relat_1(X3)
             => k5_relat_1(k5_relat_1(X1,X2),X3) = k5_relat_1(X1,k5_relat_1(X2,X3)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).

fof(t43_funct_1,conjecture,(
    ! [X1,X2] : k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)) = k6_relat_1(k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

fof(t77_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k1_relat_1(X2),X1)
       => k5_relat_1(k6_relat_1(X1),X2) = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(c_0_17,plain,(
    ! [X14,X15] : k1_setfam_1(k2_tarski(X14,X15)) = k3_xboole_0(X14,X15) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_18,plain,(
    ! [X12,X13] : k1_enumset1(X12,X12,X13) = k2_tarski(X12,X13) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_19,plain,(
    ! [X8,X9] :
      ( ~ r1_tarski(X8,X9)
      | k3_xboole_0(X8,X9) = X8 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_20,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_21,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_22,plain,(
    ! [X10,X11] : k2_tarski(X10,X11) = k2_tarski(X11,X10) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

fof(c_0_23,plain,(
    ! [X17,X18] :
      ( ~ v1_relat_1(X17)
      | v1_relat_1(k3_xboole_0(X17,X18)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_relat_1])])).

cnf(c_0_24,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_26,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_27,plain,
    ( v1_relat_1(k3_xboole_0(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_28,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_29,plain,
    ( k1_enumset1(X1,X1,X2) = k1_enumset1(X2,X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_21]),c_0_21])).

fof(c_0_30,plain,(
    ! [X19,X20,X21] :
      ( ~ v1_relat_1(X21)
      | k7_relat_1(k7_relat_1(X21,X19),X20) = k7_relat_1(X21,k3_xboole_0(X19,X20)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t100_relat_1])])).

fof(c_0_31,plain,(
    ! [X22,X23] :
      ( ~ v1_relat_1(X23)
      | k7_relat_1(X23,X22) = k7_relat_1(X23,k3_xboole_0(k1_relat_1(X23),X22)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t192_relat_1])])).

cnf(c_0_32,plain,
    ( v1_relat_1(k1_setfam_1(k1_enumset1(X1,X1,X2)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_27,c_0_25])).

cnf(c_0_33,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = X2
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

fof(c_0_34,plain,(
    ! [X28,X29] :
      ( ( r1_tarski(k5_relat_1(X29,k6_relat_1(X28)),X29)
        | ~ v1_relat_1(X29) )
      & ( r1_tarski(k5_relat_1(k6_relat_1(X28),X29),X29)
        | ~ v1_relat_1(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t76_relat_1])])])).

fof(c_0_35,plain,(
    ! [X33,X34] :
      ( ~ v1_relat_1(X34)
      | k7_relat_1(X34,X33) = k5_relat_1(k6_relat_1(X33),X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).

cnf(c_0_36,plain,
    ( k7_relat_1(k7_relat_1(X1,X2),X3) = k7_relat_1(X1,k3_xboole_0(X2,X3))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_37,plain,
    ( k7_relat_1(X1,X2) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_38,plain,(
    ! [X27] :
      ( k1_relat_1(k6_relat_1(X27)) = X27
      & k2_relat_1(k6_relat_1(X27)) = X27 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

fof(c_0_39,plain,(
    ! [X16] : v1_relat_1(k6_relat_1(X16)) ),
    inference(variable_rename,[status(thm)],[dt_k6_relat_1])).

cnf(c_0_40,plain,
    ( v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_41,plain,
    ( r1_tarski(k5_relat_1(X1,k6_relat_1(X2)),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_42,plain,
    ( k7_relat_1(X1,X2) = k5_relat_1(k6_relat_1(X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_43,plain,
    ( k7_relat_1(k7_relat_1(X1,X2),X3) = k7_relat_1(X1,k1_setfam_1(k1_enumset1(X2,X2,X3)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_36,c_0_25])).

cnf(c_0_44,plain,
    ( k7_relat_1(X1,X2) = k7_relat_1(X1,k1_setfam_1(k1_enumset1(k1_relat_1(X1),k1_relat_1(X1),X2)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_37,c_0_25])).

cnf(c_0_45,plain,
    ( k1_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_46,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

fof(c_0_47,plain,(
    ! [X32] :
      ( ~ v1_relat_1(X32)
      | k5_relat_1(X32,k6_relat_1(k2_relat_1(X32))) = X32 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t80_relat_1])])).

cnf(c_0_48,plain,
    ( v1_relat_1(k5_relat_1(X1,k6_relat_1(X2)))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_49,plain,
    ( k5_relat_1(k6_relat_1(k1_setfam_1(k1_enumset1(X1,X1,X2))),X3) = k7_relat_1(k7_relat_1(X3,X1),X2)
    | ~ v1_relat_1(X3) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_50,plain,
    ( k7_relat_1(k6_relat_1(X1),k1_setfam_1(k1_enumset1(X1,X1,X2))) = k7_relat_1(k6_relat_1(X1),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_46])])).

fof(c_0_51,plain,(
    ! [X24,X25,X26] :
      ( ~ v1_relat_1(X24)
      | ~ v1_relat_1(X25)
      | ~ v1_relat_1(X26)
      | k5_relat_1(k5_relat_1(X24,X25),X26) = k5_relat_1(X24,k5_relat_1(X25,X26)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_relat_1])])])).

cnf(c_0_52,plain,
    ( k5_relat_1(X1,k6_relat_1(k2_relat_1(X1))) = X1
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_53,plain,
    ( k2_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_54,plain,
    ( k7_relat_1(X1,k1_setfam_1(k1_enumset1(X2,X2,X3))) = k7_relat_1(k7_relat_1(X1,X3),X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_29])).

cnf(c_0_55,plain,
    ( v1_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X3)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_46]),c_0_46])])).

cnf(c_0_56,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(X1),X1),X2) = k7_relat_1(k6_relat_1(X1),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_50]),c_0_46])])).

cnf(c_0_57,plain,
    ( k5_relat_1(k5_relat_1(X1,X2),X3) = k5_relat_1(X1,k5_relat_1(X2,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_58,plain,
    ( k5_relat_1(k6_relat_1(X1),k6_relat_1(X1)) = k6_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_46])])).

cnf(c_0_59,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X1) = k7_relat_1(k6_relat_1(X1),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_54]),c_0_46])])).

cnf(c_0_60,plain,
    ( v1_relat_1(k7_relat_1(k6_relat_1(X1),X2)) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_61,plain,
    ( r1_tarski(k5_relat_1(X1,k5_relat_1(X2,k6_relat_1(X3))),k5_relat_1(X1,X2))
    | ~ v1_relat_1(k5_relat_1(X1,X2))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_57]),c_0_46])])).

cnf(c_0_62,plain,
    ( k5_relat_1(k6_relat_1(X1),k5_relat_1(k6_relat_1(X1),X2)) = k5_relat_1(k6_relat_1(X1),X2)
    | ~ v1_relat_1(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_46])])).

cnf(c_0_63,plain,
    ( k5_relat_1(k6_relat_1(X1),k7_relat_1(k6_relat_1(X1),X2)) = k7_relat_1(k6_relat_1(X1),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_59]),c_0_60])])).

cnf(c_0_64,plain,
    ( r1_tarski(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)),k6_relat_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_58]),c_0_58]),c_0_46]),c_0_46]),c_0_46])])).

fof(c_0_65,negated_conjecture,(
    ~ ! [X1,X2] : k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)) = k6_relat_1(k3_xboole_0(X1,X2)) ),
    inference(assume_negation,[status(cth)],[t43_funct_1])).

fof(c_0_66,plain,(
    ! [X30,X31] :
      ( ~ v1_relat_1(X31)
      | ~ r1_tarski(k1_relat_1(X31),X30)
      | k5_relat_1(k6_relat_1(X30),X31) = X31 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t77_relat_1])])).

fof(c_0_67,plain,(
    ! [X4,X5] :
      ( ( r1_tarski(X4,X5)
        | X4 != X5 )
      & ( r1_tarski(X5,X4)
        | X4 != X5 )
      & ( ~ r1_tarski(X4,X5)
        | ~ r1_tarski(X5,X4)
        | X4 = X5 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_68,plain,
    ( k5_relat_1(k6_relat_1(X1),k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))) = k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_42]),c_0_46])])).

cnf(c_0_69,plain,
    ( v1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_64]),c_0_46])])).

fof(c_0_70,negated_conjecture,(
    k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0)) != k6_relat_1(k3_xboole_0(esk1_0,esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_65])])])).

cnf(c_0_71,plain,
    ( k5_relat_1(k6_relat_1(X2),X1) = X1
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_72,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_73,plain,
    ( r1_tarski(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)),k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_68]),c_0_69]),c_0_46]),c_0_46])])).

fof(c_0_74,plain,(
    ! [X6,X7] : r1_tarski(k3_xboole_0(X6,X7),X6) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

cnf(c_0_75,negated_conjecture,
    ( k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0)) != k6_relat_1(k3_xboole_0(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_76,plain,
    ( k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) = k6_relat_1(X2)
    | ~ r1_tarski(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_45]),c_0_46])])).

cnf(c_0_77,plain,
    ( k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) = k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_73])])).

cnf(c_0_78,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

cnf(c_0_79,negated_conjecture,
    ( k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0)) != k6_relat_1(k1_setfam_1(k1_enumset1(esk1_0,esk1_0,esk2_0))) ),
    inference(rw,[status(thm)],[c_0_75,c_0_25])).

cnf(c_0_80,plain,
    ( k5_relat_1(k6_relat_1(k1_setfam_1(k1_enumset1(k1_relat_1(X1),k1_relat_1(X1),X2))),X1) = k7_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_42,c_0_44])).

cnf(c_0_81,plain,
    ( k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) = k6_relat_1(X1)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_76,c_0_77])).

cnf(c_0_82,plain,
    ( r1_tarski(k1_setfam_1(k1_enumset1(X1,X1,X2)),X1) ),
    inference(rw,[status(thm)],[c_0_78,c_0_25])).

cnf(c_0_83,negated_conjecture,
    ( k6_relat_1(k1_setfam_1(k1_enumset1(esk2_0,esk2_0,esk1_0))) != k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0)) ),
    inference(rw,[status(thm)],[c_0_79,c_0_29])).

cnf(c_0_84,plain,
    ( k6_relat_1(k1_setfam_1(k1_enumset1(X1,X1,X2))) = k7_relat_1(k6_relat_1(X1),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_81]),c_0_45]),c_0_45]),c_0_46]),c_0_45]),c_0_45]),c_0_82])])).

cnf(c_0_85,negated_conjecture,
    ( k7_relat_1(k6_relat_1(esk2_0),esk1_0) != k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0)) ),
    inference(rw,[status(thm)],[c_0_83,c_0_84])).

cnf(c_0_86,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_42]),c_0_46])]),c_0_77]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n025.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 21:00:51 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.40  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.19/0.40  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.40  #
% 0.19/0.40  # Preprocessing time       : 0.027 s
% 0.19/0.40  # Presaturation interreduction done
% 0.19/0.40  
% 0.19/0.40  # Proof found!
% 0.19/0.40  # SZS status Theorem
% 0.19/0.40  # SZS output start CNFRefutation
% 0.19/0.40  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.19/0.40  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.19/0.40  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.19/0.40  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 0.19/0.40  fof(fc1_relat_1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k3_xboole_0(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_relat_1)).
% 0.19/0.40  fof(t100_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>k7_relat_1(k7_relat_1(X3,X1),X2)=k7_relat_1(X3,k3_xboole_0(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_relat_1)).
% 0.19/0.40  fof(t192_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k7_relat_1(X2,X1)=k7_relat_1(X2,k3_xboole_0(k1_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t192_relat_1)).
% 0.19/0.40  fof(t76_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k5_relat_1(X2,k6_relat_1(X1)),X2)&r1_tarski(k5_relat_1(k6_relat_1(X1),X2),X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_relat_1)).
% 0.19/0.40  fof(t94_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k7_relat_1(X2,X1)=k5_relat_1(k6_relat_1(X1),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 0.19/0.40  fof(t71_relat_1, axiom, ![X1]:(k1_relat_1(k6_relat_1(X1))=X1&k2_relat_1(k6_relat_1(X1))=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 0.19/0.40  fof(dt_k6_relat_1, axiom, ![X1]:v1_relat_1(k6_relat_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 0.19/0.40  fof(t80_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k5_relat_1(X1,k6_relat_1(k2_relat_1(X1)))=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_relat_1)).
% 0.19/0.40  fof(t55_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>k5_relat_1(k5_relat_1(X1,X2),X3)=k5_relat_1(X1,k5_relat_1(X2,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_relat_1)).
% 0.19/0.40  fof(t43_funct_1, conjecture, ![X1, X2]:k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))=k6_relat_1(k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_funct_1)).
% 0.19/0.40  fof(t77_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k1_relat_1(X2),X1)=>k5_relat_1(k6_relat_1(X1),X2)=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_relat_1)).
% 0.19/0.40  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.19/0.40  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 0.19/0.40  fof(c_0_17, plain, ![X14, X15]:k1_setfam_1(k2_tarski(X14,X15))=k3_xboole_0(X14,X15), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.19/0.40  fof(c_0_18, plain, ![X12, X13]:k1_enumset1(X12,X12,X13)=k2_tarski(X12,X13), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.19/0.40  fof(c_0_19, plain, ![X8, X9]:(~r1_tarski(X8,X9)|k3_xboole_0(X8,X9)=X8), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.19/0.40  cnf(c_0_20, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.40  cnf(c_0_21, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.40  fof(c_0_22, plain, ![X10, X11]:k2_tarski(X10,X11)=k2_tarski(X11,X10), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 0.19/0.40  fof(c_0_23, plain, ![X17, X18]:(~v1_relat_1(X17)|v1_relat_1(k3_xboole_0(X17,X18))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_relat_1])])).
% 0.19/0.40  cnf(c_0_24, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.40  cnf(c_0_25, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_20, c_0_21])).
% 0.19/0.40  cnf(c_0_26, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.40  cnf(c_0_27, plain, (v1_relat_1(k3_xboole_0(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.40  cnf(c_0_28, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=X1|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_24, c_0_25])).
% 0.19/0.40  cnf(c_0_29, plain, (k1_enumset1(X1,X1,X2)=k1_enumset1(X2,X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26, c_0_21]), c_0_21])).
% 0.19/0.40  fof(c_0_30, plain, ![X19, X20, X21]:(~v1_relat_1(X21)|k7_relat_1(k7_relat_1(X21,X19),X20)=k7_relat_1(X21,k3_xboole_0(X19,X20))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t100_relat_1])])).
% 0.19/0.40  fof(c_0_31, plain, ![X22, X23]:(~v1_relat_1(X23)|k7_relat_1(X23,X22)=k7_relat_1(X23,k3_xboole_0(k1_relat_1(X23),X22))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t192_relat_1])])).
% 0.19/0.40  cnf(c_0_32, plain, (v1_relat_1(k1_setfam_1(k1_enumset1(X1,X1,X2)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_27, c_0_25])).
% 0.19/0.40  cnf(c_0_33, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=X2|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.19/0.40  fof(c_0_34, plain, ![X28, X29]:((r1_tarski(k5_relat_1(X29,k6_relat_1(X28)),X29)|~v1_relat_1(X29))&(r1_tarski(k5_relat_1(k6_relat_1(X28),X29),X29)|~v1_relat_1(X29))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t76_relat_1])])])).
% 0.19/0.40  fof(c_0_35, plain, ![X33, X34]:(~v1_relat_1(X34)|k7_relat_1(X34,X33)=k5_relat_1(k6_relat_1(X33),X34)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).
% 0.19/0.40  cnf(c_0_36, plain, (k7_relat_1(k7_relat_1(X1,X2),X3)=k7_relat_1(X1,k3_xboole_0(X2,X3))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.40  cnf(c_0_37, plain, (k7_relat_1(X1,X2)=k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.40  fof(c_0_38, plain, ![X27]:(k1_relat_1(k6_relat_1(X27))=X27&k2_relat_1(k6_relat_1(X27))=X27), inference(variable_rename,[status(thm)],[t71_relat_1])).
% 0.19/0.40  fof(c_0_39, plain, ![X16]:v1_relat_1(k6_relat_1(X16)), inference(variable_rename,[status(thm)],[dt_k6_relat_1])).
% 0.19/0.40  cnf(c_0_40, plain, (v1_relat_1(X1)|~v1_relat_1(X2)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.19/0.40  cnf(c_0_41, plain, (r1_tarski(k5_relat_1(X1,k6_relat_1(X2)),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.19/0.40  cnf(c_0_42, plain, (k7_relat_1(X1,X2)=k5_relat_1(k6_relat_1(X2),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.19/0.40  cnf(c_0_43, plain, (k7_relat_1(k7_relat_1(X1,X2),X3)=k7_relat_1(X1,k1_setfam_1(k1_enumset1(X2,X2,X3)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_36, c_0_25])).
% 0.19/0.40  cnf(c_0_44, plain, (k7_relat_1(X1,X2)=k7_relat_1(X1,k1_setfam_1(k1_enumset1(k1_relat_1(X1),k1_relat_1(X1),X2)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_37, c_0_25])).
% 0.19/0.40  cnf(c_0_45, plain, (k1_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.19/0.40  cnf(c_0_46, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.19/0.40  fof(c_0_47, plain, ![X32]:(~v1_relat_1(X32)|k5_relat_1(X32,k6_relat_1(k2_relat_1(X32)))=X32), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t80_relat_1])])).
% 0.19/0.40  cnf(c_0_48, plain, (v1_relat_1(k5_relat_1(X1,k6_relat_1(X2)))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.19/0.40  cnf(c_0_49, plain, (k5_relat_1(k6_relat_1(k1_setfam_1(k1_enumset1(X1,X1,X2))),X3)=k7_relat_1(k7_relat_1(X3,X1),X2)|~v1_relat_1(X3)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.19/0.40  cnf(c_0_50, plain, (k7_relat_1(k6_relat_1(X1),k1_setfam_1(k1_enumset1(X1,X1,X2)))=k7_relat_1(k6_relat_1(X1),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_46])])).
% 0.19/0.40  fof(c_0_51, plain, ![X24, X25, X26]:(~v1_relat_1(X24)|(~v1_relat_1(X25)|(~v1_relat_1(X26)|k5_relat_1(k5_relat_1(X24,X25),X26)=k5_relat_1(X24,k5_relat_1(X25,X26))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_relat_1])])])).
% 0.19/0.40  cnf(c_0_52, plain, (k5_relat_1(X1,k6_relat_1(k2_relat_1(X1)))=X1|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.19/0.40  cnf(c_0_53, plain, (k2_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.19/0.40  cnf(c_0_54, plain, (k7_relat_1(X1,k1_setfam_1(k1_enumset1(X2,X2,X3)))=k7_relat_1(k7_relat_1(X1,X3),X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_43, c_0_29])).
% 0.19/0.40  cnf(c_0_55, plain, (v1_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X3))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_46]), c_0_46])])).
% 0.19/0.40  cnf(c_0_56, plain, (k7_relat_1(k7_relat_1(k6_relat_1(X1),X1),X2)=k7_relat_1(k6_relat_1(X1),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_50]), c_0_46])])).
% 0.19/0.40  cnf(c_0_57, plain, (k5_relat_1(k5_relat_1(X1,X2),X3)=k5_relat_1(X1,k5_relat_1(X2,X3))|~v1_relat_1(X1)|~v1_relat_1(X2)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.19/0.40  cnf(c_0_58, plain, (k5_relat_1(k6_relat_1(X1),k6_relat_1(X1))=k6_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_46])])).
% 0.19/0.40  cnf(c_0_59, plain, (k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X1)=k7_relat_1(k6_relat_1(X1),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_54]), c_0_46])])).
% 0.19/0.40  cnf(c_0_60, plain, (v1_relat_1(k7_relat_1(k6_relat_1(X1),X2))), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.19/0.40  cnf(c_0_61, plain, (r1_tarski(k5_relat_1(X1,k5_relat_1(X2,k6_relat_1(X3))),k5_relat_1(X1,X2))|~v1_relat_1(k5_relat_1(X1,X2))|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_57]), c_0_46])])).
% 0.19/0.40  cnf(c_0_62, plain, (k5_relat_1(k6_relat_1(X1),k5_relat_1(k6_relat_1(X1),X2))=k5_relat_1(k6_relat_1(X1),X2)|~v1_relat_1(X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_46])])).
% 0.19/0.40  cnf(c_0_63, plain, (k5_relat_1(k6_relat_1(X1),k7_relat_1(k6_relat_1(X1),X2))=k7_relat_1(k6_relat_1(X1),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_59]), c_0_60])])).
% 0.19/0.40  cnf(c_0_64, plain, (r1_tarski(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)),k6_relat_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_58]), c_0_58]), c_0_46]), c_0_46]), c_0_46])])).
% 0.19/0.40  fof(c_0_65, negated_conjecture, ~(![X1, X2]:k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))=k6_relat_1(k3_xboole_0(X1,X2))), inference(assume_negation,[status(cth)],[t43_funct_1])).
% 0.19/0.40  fof(c_0_66, plain, ![X30, X31]:(~v1_relat_1(X31)|(~r1_tarski(k1_relat_1(X31),X30)|k5_relat_1(k6_relat_1(X30),X31)=X31)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t77_relat_1])])).
% 0.19/0.40  fof(c_0_67, plain, ![X4, X5]:(((r1_tarski(X4,X5)|X4!=X5)&(r1_tarski(X5,X4)|X4!=X5))&(~r1_tarski(X4,X5)|~r1_tarski(X5,X4)|X4=X5)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.19/0.40  cnf(c_0_68, plain, (k5_relat_1(k6_relat_1(X1),k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)))=k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_42]), c_0_46])])).
% 0.19/0.40  cnf(c_0_69, plain, (v1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_64]), c_0_46])])).
% 0.19/0.40  fof(c_0_70, negated_conjecture, k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0))!=k6_relat_1(k3_xboole_0(esk1_0,esk2_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_65])])])).
% 0.19/0.40  cnf(c_0_71, plain, (k5_relat_1(k6_relat_1(X2),X1)=X1|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_66])).
% 0.19/0.40  cnf(c_0_72, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.19/0.40  cnf(c_0_73, plain, (r1_tarski(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)),k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_68]), c_0_69]), c_0_46]), c_0_46])])).
% 0.19/0.40  fof(c_0_74, plain, ![X6, X7]:r1_tarski(k3_xboole_0(X6,X7),X6), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 0.19/0.40  cnf(c_0_75, negated_conjecture, (k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0))!=k6_relat_1(k3_xboole_0(esk1_0,esk2_0))), inference(split_conjunct,[status(thm)],[c_0_70])).
% 0.19/0.40  cnf(c_0_76, plain, (k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))=k6_relat_1(X2)|~r1_tarski(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_45]), c_0_46])])).
% 0.19/0.40  cnf(c_0_77, plain, (k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))=k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_73]), c_0_73])])).
% 0.19/0.40  cnf(c_0_78, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_74])).
% 0.19/0.40  cnf(c_0_79, negated_conjecture, (k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0))!=k6_relat_1(k1_setfam_1(k1_enumset1(esk1_0,esk1_0,esk2_0)))), inference(rw,[status(thm)],[c_0_75, c_0_25])).
% 0.19/0.40  cnf(c_0_80, plain, (k5_relat_1(k6_relat_1(k1_setfam_1(k1_enumset1(k1_relat_1(X1),k1_relat_1(X1),X2))),X1)=k7_relat_1(X1,X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_42, c_0_44])).
% 0.19/0.40  cnf(c_0_81, plain, (k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))=k6_relat_1(X1)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_76, c_0_77])).
% 0.19/0.40  cnf(c_0_82, plain, (r1_tarski(k1_setfam_1(k1_enumset1(X1,X1,X2)),X1)), inference(rw,[status(thm)],[c_0_78, c_0_25])).
% 0.19/0.40  cnf(c_0_83, negated_conjecture, (k6_relat_1(k1_setfam_1(k1_enumset1(esk2_0,esk2_0,esk1_0)))!=k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0))), inference(rw,[status(thm)],[c_0_79, c_0_29])).
% 0.19/0.40  cnf(c_0_84, plain, (k6_relat_1(k1_setfam_1(k1_enumset1(X1,X1,X2)))=k7_relat_1(k6_relat_1(X1),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_81]), c_0_45]), c_0_45]), c_0_46]), c_0_45]), c_0_45]), c_0_82])])).
% 0.19/0.40  cnf(c_0_85, negated_conjecture, (k7_relat_1(k6_relat_1(esk2_0),esk1_0)!=k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0))), inference(rw,[status(thm)],[c_0_83, c_0_84])).
% 0.19/0.40  cnf(c_0_86, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_42]), c_0_46])]), c_0_77]), ['proof']).
% 0.19/0.40  # SZS output end CNFRefutation
% 0.19/0.40  # Proof object total steps             : 87
% 0.19/0.40  # Proof object clause steps            : 52
% 0.19/0.40  # Proof object formula steps           : 35
% 0.19/0.40  # Proof object conjectures             : 8
% 0.19/0.40  # Proof object clause conjectures      : 5
% 0.19/0.40  # Proof object formula conjectures     : 3
% 0.19/0.40  # Proof object initial clauses used    : 18
% 0.19/0.40  # Proof object initial formulas used   : 17
% 0.19/0.40  # Proof object generating inferences   : 24
% 0.19/0.40  # Proof object simplifying inferences  : 56
% 0.19/0.40  # Training examples: 0 positive, 0 negative
% 0.19/0.40  # Parsed axioms                        : 17
% 0.19/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.40  # Initial clauses                      : 21
% 0.19/0.40  # Removed in clause preprocessing      : 2
% 0.19/0.40  # Initial clauses in saturation        : 19
% 0.19/0.40  # Processed clauses                    : 316
% 0.19/0.40  # ...of these trivial                  : 19
% 0.19/0.40  # ...subsumed                          : 128
% 0.19/0.40  # ...remaining for further processing  : 169
% 0.19/0.40  # Other redundant clauses eliminated   : 2
% 0.19/0.40  # Clauses deleted for lack of memory   : 0
% 0.19/0.40  # Backward-subsumed                    : 4
% 0.19/0.40  # Backward-rewritten                   : 12
% 0.19/0.40  # Generated clauses                    : 2001
% 0.19/0.40  # ...of the previous two non-trivial   : 1519
% 0.19/0.40  # Contextual simplify-reflections      : 1
% 0.19/0.40  # Paramodulations                      : 1999
% 0.19/0.40  # Factorizations                       : 0
% 0.19/0.40  # Equation resolutions                 : 2
% 0.19/0.40  # Propositional unsat checks           : 0
% 0.19/0.40  #    Propositional check models        : 0
% 0.19/0.40  #    Propositional check unsatisfiable : 0
% 0.19/0.40  #    Propositional clauses             : 0
% 0.19/0.40  #    Propositional clauses after purity: 0
% 0.19/0.40  #    Propositional unsat core size     : 0
% 0.19/0.40  #    Propositional preprocessing time  : 0.000
% 0.19/0.40  #    Propositional encoding time       : 0.000
% 0.19/0.40  #    Propositional solver time         : 0.000
% 0.19/0.40  #    Success case prop preproc time    : 0.000
% 0.19/0.40  #    Success case prop encoding time   : 0.000
% 0.19/0.40  #    Success case prop solver time     : 0.000
% 0.19/0.40  # Current number of processed clauses  : 133
% 0.19/0.40  #    Positive orientable unit clauses  : 36
% 0.19/0.40  #    Positive unorientable unit clauses: 2
% 0.19/0.40  #    Negative unit clauses             : 3
% 0.19/0.40  #    Non-unit-clauses                  : 92
% 0.19/0.40  # Current number of unprocessed clauses: 1225
% 0.19/0.40  # ...number of literals in the above   : 3088
% 0.19/0.40  # Current number of archived formulas  : 0
% 0.19/0.40  # Current number of archived clauses   : 36
% 0.19/0.40  # Clause-clause subsumption calls (NU) : 984
% 0.19/0.40  # Rec. Clause-clause subsumption calls : 907
% 0.19/0.40  # Non-unit clause-clause subsumptions  : 133
% 0.19/0.40  # Unit Clause-clause subsumption calls : 15
% 0.19/0.40  # Rewrite failures with RHS unbound    : 0
% 0.19/0.40  # BW rewrite match attempts            : 73
% 0.19/0.40  # BW rewrite match successes           : 48
% 0.19/0.40  # Condensation attempts                : 0
% 0.19/0.40  # Condensation successes               : 0
% 0.19/0.40  # Termbank termtop insertions          : 33657
% 0.19/0.40  
% 0.19/0.40  # -------------------------------------------------
% 0.19/0.40  # User time                : 0.057 s
% 0.19/0.40  # System time              : 0.007 s
% 0.19/0.40  # Total time               : 0.064 s
% 0.19/0.40  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
