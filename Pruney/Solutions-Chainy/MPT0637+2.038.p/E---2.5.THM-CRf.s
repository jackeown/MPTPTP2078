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
% DateTime   : Thu Dec  3 10:53:29 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   92 (2748 expanded)
%              Number of clauses        :   55 (1197 expanded)
%              Number of leaves         :   18 ( 775 expanded)
%              Depth                    :   19
%              Number of atoms          :  164 (4154 expanded)
%              Number of equality atoms :   71 (2161 expanded)
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

fof(fc1_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_relat_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t100_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => k7_relat_1(k7_relat_1(X3,X1),X2) = k7_relat_1(X3,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).

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

fof(t192_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,X1) = k7_relat_1(X2,k3_xboole_0(k1_relat_1(X2),X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t192_relat_1)).

fof(fc3_funct_1,axiom,(
    ! [X1] :
      ( v1_relat_1(k6_relat_1(X1))
      & v1_funct_1(k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(t71_relat_1,axiom,(
    ! [X1] :
      ( k1_relat_1(k6_relat_1(X1)) = X1
      & k2_relat_1(k6_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

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

fof(c_0_18,plain,(
    ! [X17,X18] : k1_setfam_1(k2_tarski(X17,X18)) = k3_xboole_0(X17,X18) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_19,plain,(
    ! [X12,X13] : k1_enumset1(X12,X12,X13) = k2_tarski(X12,X13) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_20,plain,(
    ! [X19,X20] :
      ( ~ v1_relat_1(X19)
      | v1_relat_1(k3_xboole_0(X19,X20)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_relat_1])])).

cnf(c_0_21,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_22,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_23,plain,(
    ! [X14,X15,X16] : k2_enumset1(X14,X14,X15,X16) = k1_enumset1(X14,X15,X16) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_24,plain,(
    ! [X4,X5] : k3_xboole_0(X4,X5) = k3_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_25,plain,
    ( v1_relat_1(k3_xboole_0(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_27,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_28,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_29,plain,(
    ! [X10,X11] :
      ( ~ r1_tarski(X10,X11)
      | k3_xboole_0(X10,X11) = X10 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_30,plain,
    ( v1_relat_1(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_26]),c_0_27])).

cnf(c_0_31,plain,
    ( k1_setfam_1(k2_enumset1(X1,X1,X1,X2)) = k1_setfam_1(k2_enumset1(X2,X2,X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_26]),c_0_26]),c_0_27]),c_0_27])).

cnf(c_0_32,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_33,plain,(
    ! [X21,X22,X23] :
      ( ~ v1_relat_1(X23)
      | k7_relat_1(k7_relat_1(X23,X21),X22) = k7_relat_1(X23,k3_xboole_0(X21,X22)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t100_relat_1])])).

cnf(c_0_34,plain,
    ( v1_relat_1(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)))
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_35,plain,
    ( k1_setfam_1(k2_enumset1(X1,X1,X1,X2)) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_26]),c_0_27])).

fof(c_0_36,plain,(
    ! [X30,X31] :
      ( ( r1_tarski(k5_relat_1(X31,k6_relat_1(X30)),X31)
        | ~ v1_relat_1(X31) )
      & ( r1_tarski(k5_relat_1(k6_relat_1(X30),X31),X31)
        | ~ v1_relat_1(X31) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t76_relat_1])])])).

fof(c_0_37,plain,(
    ! [X35,X36] :
      ( ~ v1_relat_1(X36)
      | k7_relat_1(X36,X35) = k5_relat_1(k6_relat_1(X35),X36) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).

cnf(c_0_38,plain,
    ( k7_relat_1(k7_relat_1(X1,X2),X3) = k7_relat_1(X1,k3_xboole_0(X2,X3))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

fof(c_0_39,plain,(
    ! [X24,X25] :
      ( ~ v1_relat_1(X25)
      | k7_relat_1(X25,X24) = k7_relat_1(X25,k3_xboole_0(k1_relat_1(X25),X24)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t192_relat_1])])).

cnf(c_0_40,plain,
    ( v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_41,plain,
    ( r1_tarski(k5_relat_1(X1,k6_relat_1(X2)),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_42,plain,
    ( k7_relat_1(X1,X2) = k5_relat_1(k6_relat_1(X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_43,plain,
    ( k7_relat_1(k7_relat_1(X1,X2),X3) = k7_relat_1(X1,k1_setfam_1(k2_enumset1(X2,X2,X2,X3)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_26]),c_0_27])).

fof(c_0_44,plain,(
    ! [X37] :
      ( v1_relat_1(k6_relat_1(X37))
      & v1_funct_1(k6_relat_1(X37)) ) ),
    inference(variable_rename,[status(thm)],[fc3_funct_1])).

cnf(c_0_45,plain,
    ( k7_relat_1(X1,X2) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_46,plain,
    ( v1_relat_1(k5_relat_1(X1,k6_relat_1(X2)))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_47,plain,
    ( k5_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X1,X1,X1,X2))),X3) = k7_relat_1(k7_relat_1(X3,X1),X2)
    | ~ v1_relat_1(X3) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_48,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_49,plain,
    ( k7_relat_1(X1,X2) = k7_relat_1(X1,k1_setfam_1(k2_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X2)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_26]),c_0_27])).

fof(c_0_50,plain,(
    ! [X29] :
      ( k1_relat_1(k6_relat_1(X29)) = X29
      & k2_relat_1(k6_relat_1(X29)) = X29 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

cnf(c_0_51,plain,
    ( v1_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X3)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_48]),c_0_48])])).

fof(c_0_52,plain,(
    ! [X34] :
      ( ~ v1_relat_1(X34)
      | k5_relat_1(X34,k6_relat_1(k2_relat_1(X34))) = X34 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t80_relat_1])])).

cnf(c_0_53,plain,
    ( k7_relat_1(k7_relat_1(X1,k1_relat_1(X1)),X2) = k7_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_49])).

cnf(c_0_54,plain,
    ( k1_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_55,plain,
    ( v1_relat_1(k7_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)),X3)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_42]),c_0_48])])).

cnf(c_0_56,plain,
    ( k5_relat_1(X1,k6_relat_1(k2_relat_1(X1))) = X1
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

fof(c_0_57,plain,(
    ! [X26,X27,X28] :
      ( ~ v1_relat_1(X26)
      | ~ v1_relat_1(X27)
      | ~ v1_relat_1(X28)
      | k5_relat_1(k5_relat_1(X26,X27),X28) = k5_relat_1(X26,k5_relat_1(X27,X28)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_relat_1])])])).

cnf(c_0_58,plain,
    ( k2_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_59,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(X1),X1),X2) = k7_relat_1(k6_relat_1(X1),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_48])])).

cnf(c_0_60,plain,
    ( v1_relat_1(k7_relat_1(k6_relat_1(X1),X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_48])])).

cnf(c_0_61,plain,
    ( k5_relat_1(k5_relat_1(X1,X2),X3) = k5_relat_1(X1,k5_relat_1(X2,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_62,plain,
    ( k5_relat_1(k6_relat_1(X1),k6_relat_1(X1)) = k6_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_58]),c_0_48])])).

cnf(c_0_63,plain,
    ( k7_relat_1(X1,k1_setfam_1(k2_enumset1(X2,X2,X2,X3))) = k7_relat_1(k7_relat_1(X1,X3),X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_31])).

cnf(c_0_64,plain,
    ( k5_relat_1(k6_relat_1(X1),k7_relat_1(k6_relat_1(X2),X2)) = k7_relat_1(k6_relat_1(X2),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_59]),c_0_60])])).

cnf(c_0_65,plain,
    ( r1_tarski(k5_relat_1(X1,k5_relat_1(X2,k6_relat_1(X3))),k5_relat_1(X1,X2))
    | ~ v1_relat_1(k5_relat_1(X1,X2))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_61]),c_0_48])])).

cnf(c_0_66,plain,
    ( k5_relat_1(k6_relat_1(X1),k5_relat_1(k6_relat_1(X1),X2)) = k5_relat_1(k6_relat_1(X1),X2)
    | ~ v1_relat_1(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_48])])).

cnf(c_0_67,plain,
    ( k7_relat_1(k7_relat_1(X1,X2),k1_relat_1(X1)) = k7_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_49,c_0_63])).

cnf(c_0_68,plain,
    ( k7_relat_1(k6_relat_1(X1),X2) = k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_42]),c_0_62]),c_0_48])])).

cnf(c_0_69,plain,
    ( r1_tarski(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)),k6_relat_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_62]),c_0_62]),c_0_48]),c_0_48]),c_0_48])])).

cnf(c_0_70,plain,
    ( k7_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)),X2) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_54]),c_0_68]),c_0_68]),c_0_48])])).

cnf(c_0_71,plain,
    ( v1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_69]),c_0_48])])).

fof(c_0_72,negated_conjecture,(
    ~ ! [X1,X2] : k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)) = k6_relat_1(k3_xboole_0(X1,X2)) ),
    inference(assume_negation,[status(cth)],[t43_funct_1])).

fof(c_0_73,plain,(
    ! [X32,X33] :
      ( ~ v1_relat_1(X33)
      | ~ r1_tarski(k1_relat_1(X33),X32)
      | k5_relat_1(k6_relat_1(X32),X33) = X33 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t77_relat_1])])).

fof(c_0_74,plain,(
    ! [X6,X7] :
      ( ( r1_tarski(X6,X7)
        | X6 != X7 )
      & ( r1_tarski(X7,X6)
        | X6 != X7 )
      & ( ~ r1_tarski(X6,X7)
        | ~ r1_tarski(X7,X6)
        | X6 = X7 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_75,plain,
    ( k5_relat_1(k6_relat_1(X1),k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))) = k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_70]),c_0_71])])).

fof(c_0_76,negated_conjecture,(
    k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0)) != k6_relat_1(k3_xboole_0(esk1_0,esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_72])])])).

cnf(c_0_77,plain,
    ( k5_relat_1(k6_relat_1(X2),X1) = X1
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_78,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

cnf(c_0_79,plain,
    ( r1_tarski(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)),k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_75]),c_0_71]),c_0_48]),c_0_48])])).

fof(c_0_80,plain,(
    ! [X8,X9] : r1_tarski(k3_xboole_0(X8,X9),X8) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

cnf(c_0_81,negated_conjecture,
    ( k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0)) != k6_relat_1(k3_xboole_0(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_76])).

cnf(c_0_82,plain,
    ( k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) = k6_relat_1(X2)
    | ~ r1_tarski(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_54]),c_0_48])])).

cnf(c_0_83,plain,
    ( k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) = k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_79])])).

cnf(c_0_84,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_80])).

cnf(c_0_85,negated_conjecture,
    ( k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0)) != k6_relat_1(k1_setfam_1(k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_81,c_0_26]),c_0_27])).

cnf(c_0_86,plain,
    ( k5_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X2))),X1) = k7_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_42,c_0_49])).

cnf(c_0_87,plain,
    ( k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) = k6_relat_1(X1)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_82,c_0_83])).

cnf(c_0_88,plain,
    ( r1_tarski(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_84,c_0_26]),c_0_27])).

cnf(c_0_89,negated_conjecture,
    ( k6_relat_1(k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,esk1_0))) != k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0)) ),
    inference(rw,[status(thm)],[c_0_85,c_0_31])).

cnf(c_0_90,plain,
    ( k6_relat_1(k1_setfam_1(k2_enumset1(X1,X1,X1,X2))) = k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_87]),c_0_54]),c_0_54]),c_0_54]),c_0_68]),c_0_48]),c_0_54]),c_0_54]),c_0_54]),c_0_88])])).

cnf(c_0_91,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_89,c_0_90]),c_0_83])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:04:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.45  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.19/0.45  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.45  #
% 0.19/0.45  # Preprocessing time       : 0.027 s
% 0.19/0.45  # Presaturation interreduction done
% 0.19/0.45  
% 0.19/0.45  # Proof found!
% 0.19/0.45  # SZS status Theorem
% 0.19/0.45  # SZS output start CNFRefutation
% 0.19/0.45  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.19/0.45  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.19/0.45  fof(fc1_relat_1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k3_xboole_0(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_relat_1)).
% 0.19/0.45  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.19/0.45  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.19/0.45  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.19/0.45  fof(t100_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>k7_relat_1(k7_relat_1(X3,X1),X2)=k7_relat_1(X3,k3_xboole_0(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_relat_1)).
% 0.19/0.45  fof(t76_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k5_relat_1(X2,k6_relat_1(X1)),X2)&r1_tarski(k5_relat_1(k6_relat_1(X1),X2),X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_relat_1)).
% 0.19/0.45  fof(t94_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k7_relat_1(X2,X1)=k5_relat_1(k6_relat_1(X1),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 0.19/0.45  fof(t192_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k7_relat_1(X2,X1)=k7_relat_1(X2,k3_xboole_0(k1_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t192_relat_1)).
% 0.19/0.45  fof(fc3_funct_1, axiom, ![X1]:(v1_relat_1(k6_relat_1(X1))&v1_funct_1(k6_relat_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 0.19/0.45  fof(t71_relat_1, axiom, ![X1]:(k1_relat_1(k6_relat_1(X1))=X1&k2_relat_1(k6_relat_1(X1))=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 0.19/0.45  fof(t80_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k5_relat_1(X1,k6_relat_1(k2_relat_1(X1)))=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_relat_1)).
% 0.19/0.45  fof(t55_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>k5_relat_1(k5_relat_1(X1,X2),X3)=k5_relat_1(X1,k5_relat_1(X2,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_relat_1)).
% 0.19/0.45  fof(t43_funct_1, conjecture, ![X1, X2]:k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))=k6_relat_1(k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_funct_1)).
% 0.19/0.45  fof(t77_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k1_relat_1(X2),X1)=>k5_relat_1(k6_relat_1(X1),X2)=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_relat_1)).
% 0.19/0.45  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.19/0.45  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 0.19/0.45  fof(c_0_18, plain, ![X17, X18]:k1_setfam_1(k2_tarski(X17,X18))=k3_xboole_0(X17,X18), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.19/0.45  fof(c_0_19, plain, ![X12, X13]:k1_enumset1(X12,X12,X13)=k2_tarski(X12,X13), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.19/0.45  fof(c_0_20, plain, ![X19, X20]:(~v1_relat_1(X19)|v1_relat_1(k3_xboole_0(X19,X20))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_relat_1])])).
% 0.19/0.45  cnf(c_0_21, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.45  cnf(c_0_22, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.45  fof(c_0_23, plain, ![X14, X15, X16]:k2_enumset1(X14,X14,X15,X16)=k1_enumset1(X14,X15,X16), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.19/0.45  fof(c_0_24, plain, ![X4, X5]:k3_xboole_0(X4,X5)=k3_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.19/0.45  cnf(c_0_25, plain, (v1_relat_1(k3_xboole_0(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.45  cnf(c_0_26, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_21, c_0_22])).
% 0.19/0.45  cnf(c_0_27, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.45  cnf(c_0_28, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.45  fof(c_0_29, plain, ![X10, X11]:(~r1_tarski(X10,X11)|k3_xboole_0(X10,X11)=X10), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.19/0.45  cnf(c_0_30, plain, (v1_relat_1(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25, c_0_26]), c_0_27])).
% 0.19/0.45  cnf(c_0_31, plain, (k1_setfam_1(k2_enumset1(X1,X1,X1,X2))=k1_setfam_1(k2_enumset1(X2,X2,X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_26]), c_0_26]), c_0_27]), c_0_27])).
% 0.19/0.45  cnf(c_0_32, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.45  fof(c_0_33, plain, ![X21, X22, X23]:(~v1_relat_1(X23)|k7_relat_1(k7_relat_1(X23,X21),X22)=k7_relat_1(X23,k3_xboole_0(X21,X22))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t100_relat_1])])).
% 0.19/0.45  cnf(c_0_34, plain, (v1_relat_1(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)))|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.19/0.45  cnf(c_0_35, plain, (k1_setfam_1(k2_enumset1(X1,X1,X1,X2))=X1|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_26]), c_0_27])).
% 0.19/0.45  fof(c_0_36, plain, ![X30, X31]:((r1_tarski(k5_relat_1(X31,k6_relat_1(X30)),X31)|~v1_relat_1(X31))&(r1_tarski(k5_relat_1(k6_relat_1(X30),X31),X31)|~v1_relat_1(X31))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t76_relat_1])])])).
% 0.19/0.45  fof(c_0_37, plain, ![X35, X36]:(~v1_relat_1(X36)|k7_relat_1(X36,X35)=k5_relat_1(k6_relat_1(X35),X36)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).
% 0.19/0.45  cnf(c_0_38, plain, (k7_relat_1(k7_relat_1(X1,X2),X3)=k7_relat_1(X1,k3_xboole_0(X2,X3))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.45  fof(c_0_39, plain, ![X24, X25]:(~v1_relat_1(X25)|k7_relat_1(X25,X24)=k7_relat_1(X25,k3_xboole_0(k1_relat_1(X25),X24))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t192_relat_1])])).
% 0.19/0.45  cnf(c_0_40, plain, (v1_relat_1(X1)|~v1_relat_1(X2)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.19/0.45  cnf(c_0_41, plain, (r1_tarski(k5_relat_1(X1,k6_relat_1(X2)),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.19/0.45  cnf(c_0_42, plain, (k7_relat_1(X1,X2)=k5_relat_1(k6_relat_1(X2),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.19/0.45  cnf(c_0_43, plain, (k7_relat_1(k7_relat_1(X1,X2),X3)=k7_relat_1(X1,k1_setfam_1(k2_enumset1(X2,X2,X2,X3)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_26]), c_0_27])).
% 0.19/0.45  fof(c_0_44, plain, ![X37]:(v1_relat_1(k6_relat_1(X37))&v1_funct_1(k6_relat_1(X37))), inference(variable_rename,[status(thm)],[fc3_funct_1])).
% 0.19/0.45  cnf(c_0_45, plain, (k7_relat_1(X1,X2)=k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.19/0.45  cnf(c_0_46, plain, (v1_relat_1(k5_relat_1(X1,k6_relat_1(X2)))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.19/0.45  cnf(c_0_47, plain, (k5_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X1,X1,X1,X2))),X3)=k7_relat_1(k7_relat_1(X3,X1),X2)|~v1_relat_1(X3)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.19/0.45  cnf(c_0_48, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.19/0.45  cnf(c_0_49, plain, (k7_relat_1(X1,X2)=k7_relat_1(X1,k1_setfam_1(k2_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X2)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45, c_0_26]), c_0_27])).
% 0.19/0.45  fof(c_0_50, plain, ![X29]:(k1_relat_1(k6_relat_1(X29))=X29&k2_relat_1(k6_relat_1(X29))=X29), inference(variable_rename,[status(thm)],[t71_relat_1])).
% 0.19/0.45  cnf(c_0_51, plain, (v1_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X3))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_48]), c_0_48])])).
% 0.19/0.45  fof(c_0_52, plain, ![X34]:(~v1_relat_1(X34)|k5_relat_1(X34,k6_relat_1(k2_relat_1(X34)))=X34), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t80_relat_1])])).
% 0.19/0.45  cnf(c_0_53, plain, (k7_relat_1(k7_relat_1(X1,k1_relat_1(X1)),X2)=k7_relat_1(X1,X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_43, c_0_49])).
% 0.19/0.45  cnf(c_0_54, plain, (k1_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.19/0.45  cnf(c_0_55, plain, (v1_relat_1(k7_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)),X3))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_42]), c_0_48])])).
% 0.19/0.45  cnf(c_0_56, plain, (k5_relat_1(X1,k6_relat_1(k2_relat_1(X1)))=X1|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.19/0.45  fof(c_0_57, plain, ![X26, X27, X28]:(~v1_relat_1(X26)|(~v1_relat_1(X27)|(~v1_relat_1(X28)|k5_relat_1(k5_relat_1(X26,X27),X28)=k5_relat_1(X26,k5_relat_1(X27,X28))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_relat_1])])])).
% 0.19/0.45  cnf(c_0_58, plain, (k2_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.19/0.45  cnf(c_0_59, plain, (k7_relat_1(k7_relat_1(k6_relat_1(X1),X1),X2)=k7_relat_1(k6_relat_1(X1),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_48])])).
% 0.19/0.45  cnf(c_0_60, plain, (v1_relat_1(k7_relat_1(k6_relat_1(X1),X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_48])])).
% 0.19/0.45  cnf(c_0_61, plain, (k5_relat_1(k5_relat_1(X1,X2),X3)=k5_relat_1(X1,k5_relat_1(X2,X3))|~v1_relat_1(X1)|~v1_relat_1(X2)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.19/0.45  cnf(c_0_62, plain, (k5_relat_1(k6_relat_1(X1),k6_relat_1(X1))=k6_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_58]), c_0_48])])).
% 0.19/0.45  cnf(c_0_63, plain, (k7_relat_1(X1,k1_setfam_1(k2_enumset1(X2,X2,X2,X3)))=k7_relat_1(k7_relat_1(X1,X3),X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_43, c_0_31])).
% 0.19/0.45  cnf(c_0_64, plain, (k5_relat_1(k6_relat_1(X1),k7_relat_1(k6_relat_1(X2),X2))=k7_relat_1(k6_relat_1(X2),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_59]), c_0_60])])).
% 0.19/0.45  cnf(c_0_65, plain, (r1_tarski(k5_relat_1(X1,k5_relat_1(X2,k6_relat_1(X3))),k5_relat_1(X1,X2))|~v1_relat_1(k5_relat_1(X1,X2))|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_61]), c_0_48])])).
% 0.19/0.45  cnf(c_0_66, plain, (k5_relat_1(k6_relat_1(X1),k5_relat_1(k6_relat_1(X1),X2))=k5_relat_1(k6_relat_1(X1),X2)|~v1_relat_1(X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_48])])).
% 0.19/0.45  cnf(c_0_67, plain, (k7_relat_1(k7_relat_1(X1,X2),k1_relat_1(X1))=k7_relat_1(X1,X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_49, c_0_63])).
% 0.19/0.45  cnf(c_0_68, plain, (k7_relat_1(k6_relat_1(X1),X2)=k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_42]), c_0_62]), c_0_48])])).
% 0.19/0.45  cnf(c_0_69, plain, (r1_tarski(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)),k6_relat_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_62]), c_0_62]), c_0_48]), c_0_48]), c_0_48])])).
% 0.19/0.45  cnf(c_0_70, plain, (k7_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)),X2)=k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_54]), c_0_68]), c_0_68]), c_0_48])])).
% 0.19/0.45  cnf(c_0_71, plain, (v1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_69]), c_0_48])])).
% 0.19/0.45  fof(c_0_72, negated_conjecture, ~(![X1, X2]:k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))=k6_relat_1(k3_xboole_0(X1,X2))), inference(assume_negation,[status(cth)],[t43_funct_1])).
% 0.19/0.45  fof(c_0_73, plain, ![X32, X33]:(~v1_relat_1(X33)|(~r1_tarski(k1_relat_1(X33),X32)|k5_relat_1(k6_relat_1(X32),X33)=X33)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t77_relat_1])])).
% 0.19/0.45  fof(c_0_74, plain, ![X6, X7]:(((r1_tarski(X6,X7)|X6!=X7)&(r1_tarski(X7,X6)|X6!=X7))&(~r1_tarski(X6,X7)|~r1_tarski(X7,X6)|X6=X7)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.19/0.45  cnf(c_0_75, plain, (k5_relat_1(k6_relat_1(X1),k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)))=k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_70]), c_0_71])])).
% 0.19/0.45  fof(c_0_76, negated_conjecture, k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0))!=k6_relat_1(k3_xboole_0(esk1_0,esk2_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_72])])])).
% 0.19/0.45  cnf(c_0_77, plain, (k5_relat_1(k6_relat_1(X2),X1)=X1|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_73])).
% 0.19/0.45  cnf(c_0_78, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_74])).
% 0.19/0.45  cnf(c_0_79, plain, (r1_tarski(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)),k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_75]), c_0_71]), c_0_48]), c_0_48])])).
% 0.19/0.45  fof(c_0_80, plain, ![X8, X9]:r1_tarski(k3_xboole_0(X8,X9),X8), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 0.19/0.45  cnf(c_0_81, negated_conjecture, (k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0))!=k6_relat_1(k3_xboole_0(esk1_0,esk2_0))), inference(split_conjunct,[status(thm)],[c_0_76])).
% 0.19/0.45  cnf(c_0_82, plain, (k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))=k6_relat_1(X2)|~r1_tarski(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_54]), c_0_48])])).
% 0.19/0.45  cnf(c_0_83, plain, (k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))=k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_79]), c_0_79])])).
% 0.19/0.45  cnf(c_0_84, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_80])).
% 0.19/0.45  cnf(c_0_85, negated_conjecture, (k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0))!=k6_relat_1(k1_setfam_1(k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_81, c_0_26]), c_0_27])).
% 0.19/0.45  cnf(c_0_86, plain, (k5_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X2))),X1)=k7_relat_1(X1,X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_42, c_0_49])).
% 0.19/0.45  cnf(c_0_87, plain, (k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))=k6_relat_1(X1)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_82, c_0_83])).
% 0.19/0.45  cnf(c_0_88, plain, (r1_tarski(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_84, c_0_26]), c_0_27])).
% 0.19/0.45  cnf(c_0_89, negated_conjecture, (k6_relat_1(k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,esk1_0)))!=k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0))), inference(rw,[status(thm)],[c_0_85, c_0_31])).
% 0.19/0.45  cnf(c_0_90, plain, (k6_relat_1(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)))=k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_87]), c_0_54]), c_0_54]), c_0_54]), c_0_68]), c_0_48]), c_0_54]), c_0_54]), c_0_54]), c_0_88])])).
% 0.19/0.45  cnf(c_0_91, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_89, c_0_90]), c_0_83])]), ['proof']).
% 0.19/0.45  # SZS output end CNFRefutation
% 0.19/0.45  # Proof object total steps             : 92
% 0.19/0.45  # Proof object clause steps            : 55
% 0.19/0.45  # Proof object formula steps           : 37
% 0.19/0.45  # Proof object conjectures             : 7
% 0.19/0.45  # Proof object clause conjectures      : 4
% 0.19/0.45  # Proof object formula conjectures     : 3
% 0.19/0.45  # Proof object initial clauses used    : 19
% 0.19/0.45  # Proof object initial formulas used   : 18
% 0.19/0.45  # Proof object generating inferences   : 26
% 0.19/0.45  # Proof object simplifying inferences  : 73
% 0.19/0.45  # Training examples: 0 positive, 0 negative
% 0.19/0.45  # Parsed axioms                        : 18
% 0.19/0.45  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.45  # Initial clauses                      : 23
% 0.19/0.45  # Removed in clause preprocessing      : 3
% 0.19/0.45  # Initial clauses in saturation        : 20
% 0.19/0.45  # Processed clauses                    : 661
% 0.19/0.45  # ...of these trivial                  : 32
% 0.19/0.45  # ...subsumed                          : 399
% 0.19/0.45  # ...remaining for further processing  : 230
% 0.19/0.45  # Other redundant clauses eliminated   : 2
% 0.19/0.45  # Clauses deleted for lack of memory   : 0
% 0.19/0.45  # Backward-subsumed                    : 2
% 0.19/0.45  # Backward-rewritten                   : 30
% 0.19/0.45  # Generated clauses                    : 5024
% 0.19/0.45  # ...of the previous two non-trivial   : 3653
% 0.19/0.45  # Contextual simplify-reflections      : 11
% 0.19/0.45  # Paramodulations                      : 5022
% 0.19/0.45  # Factorizations                       : 0
% 0.19/0.45  # Equation resolutions                 : 2
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
% 0.19/0.45  # Current number of processed clauses  : 177
% 0.19/0.45  #    Positive orientable unit clauses  : 36
% 0.19/0.45  #    Positive unorientable unit clauses: 2
% 0.19/0.45  #    Negative unit clauses             : 2
% 0.19/0.45  #    Non-unit-clauses                  : 137
% 0.19/0.45  # Current number of unprocessed clauses: 2970
% 0.19/0.45  # ...number of literals in the above   : 9550
% 0.19/0.45  # Current number of archived formulas  : 0
% 0.19/0.45  # Current number of archived clauses   : 54
% 0.19/0.45  # Clause-clause subsumption calls (NU) : 3545
% 0.19/0.45  # Rec. Clause-clause subsumption calls : 2832
% 0.19/0.45  # Non-unit clause-clause subsumptions  : 411
% 0.19/0.45  # Unit Clause-clause subsumption calls : 18
% 0.19/0.45  # Rewrite failures with RHS unbound    : 0
% 0.19/0.45  # BW rewrite match attempts            : 113
% 0.19/0.45  # BW rewrite match successes           : 69
% 0.19/0.45  # Condensation attempts                : 0
% 0.19/0.45  # Condensation successes               : 0
% 0.19/0.45  # Termbank termtop insertions          : 95766
% 0.19/0.45  
% 0.19/0.45  # -------------------------------------------------
% 0.19/0.45  # User time                : 0.110 s
% 0.19/0.45  # System time              : 0.004 s
% 0.19/0.45  # Total time               : 0.114 s
% 0.19/0.45  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
