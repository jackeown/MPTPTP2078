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
% DateTime   : Thu Dec  3 10:53:28 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  109 (2421 expanded)
%              Number of clauses        :   70 (1094 expanded)
%              Number of leaves         :   19 ( 663 expanded)
%              Depth                    :   19
%              Number of atoms          :  179 (3387 expanded)
%              Number of equality atoms :   89 (1927 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    7 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t47_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(t90_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k1_relat_1(k7_relat_1(X2,X1)) = k3_xboole_0(k1_relat_1(X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

fof(t94_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,X1) = k5_relat_1(k6_relat_1(X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(fc3_funct_1,axiom,(
    ! [X1] :
      ( v1_relat_1(k6_relat_1(X1))
      & v1_funct_1(k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(t55_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( v1_relat_1(X3)
             => k5_relat_1(k5_relat_1(X1,X2),X3) = k5_relat_1(X1,k5_relat_1(X2,X3)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).

fof(t97_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k1_relat_1(X2),X1)
       => k7_relat_1(X2,X1) = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

fof(t71_relat_1,axiom,(
    ! [X1] :
      ( k1_relat_1(k6_relat_1(X1)) = X1
      & k2_relat_1(k6_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(dt_k5_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X2) )
     => v1_relat_1(k5_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(t100_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => k7_relat_1(k7_relat_1(X3,X1),X2) = k7_relat_1(X3,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t77_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k1_relat_1(X2),X1)
       => k5_relat_1(k6_relat_1(X1),X2) = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).

fof(t76_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k5_relat_1(X2,k6_relat_1(X1)),X2)
        & r1_tarski(k5_relat_1(k6_relat_1(X1),X2),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_relat_1)).

fof(t43_funct_1,conjecture,(
    ! [X1,X2] : k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)) = k6_relat_1(k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

fof(c_0_19,plain,(
    ! [X19,X20] : k1_setfam_1(k2_tarski(X19,X20)) = k3_xboole_0(X19,X20) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_20,plain,(
    ! [X14,X15] : k1_enumset1(X14,X14,X15) = k2_tarski(X14,X15) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_21,plain,(
    ! [X8,X9] : r1_tarski(k3_xboole_0(X8,X9),X8) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

cnf(c_0_22,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_23,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_24,plain,(
    ! [X16,X17,X18] : k2_enumset1(X16,X16,X17,X18) = k1_enumset1(X16,X17,X18) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_25,plain,(
    ! [X12,X13] : k4_xboole_0(X12,k4_xboole_0(X12,X13)) = k3_xboole_0(X12,X13) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_26,plain,(
    ! [X10,X11] : k4_xboole_0(X10,k3_xboole_0(X10,X11)) = k4_xboole_0(X10,X11) ),
    inference(variable_rename,[status(thm)],[t47_xboole_1])).

fof(c_0_27,plain,(
    ! [X35,X36] :
      ( ~ v1_relat_1(X36)
      | k1_relat_1(k7_relat_1(X36,X35)) = k3_xboole_0(k1_relat_1(X36),X35) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t90_relat_1])])).

cnf(c_0_28,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_30,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_32,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_33,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = k3_xboole_0(k1_relat_1(X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_34,plain,(
    ! [X37,X38] :
      ( ~ v1_relat_1(X38)
      | k7_relat_1(X38,X37) = k5_relat_1(k6_relat_1(X37),X38) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).

fof(c_0_35,plain,(
    ! [X41] :
      ( v1_relat_1(k6_relat_1(X41))
      & v1_funct_1(k6_relat_1(X41)) ) ),
    inference(variable_rename,[status(thm)],[fc3_funct_1])).

fof(c_0_36,plain,(
    ! [X26,X27,X28] :
      ( ~ v1_relat_1(X26)
      | ~ v1_relat_1(X27)
      | ~ v1_relat_1(X28)
      | k5_relat_1(k5_relat_1(X26,X27),X28) = k5_relat_1(X26,k5_relat_1(X27,X28)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_relat_1])])])).

fof(c_0_37,plain,(
    ! [X39,X40] :
      ( ~ v1_relat_1(X40)
      | ~ r1_tarski(k1_relat_1(X40),X39)
      | k7_relat_1(X40,X39) = X40 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t97_relat_1])])).

fof(c_0_38,plain,(
    ! [X29] :
      ( k1_relat_1(k6_relat_1(X29)) = X29
      & k2_relat_1(k6_relat_1(X29)) = X29 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

cnf(c_0_39,plain,
    ( r1_tarski(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_29]),c_0_30])).

cnf(c_0_40,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k1_setfam_1(k2_enumset1(X1,X1,X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_29]),c_0_30])).

cnf(c_0_41,plain,
    ( k4_xboole_0(X1,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_29]),c_0_30])).

cnf(c_0_42,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = k1_setfam_1(k2_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X2))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_29]),c_0_30])).

fof(c_0_43,plain,(
    ! [X21,X22] :
      ( ~ v1_relat_1(X21)
      | ~ v1_relat_1(X22)
      | v1_relat_1(k5_relat_1(X21,X22)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_relat_1])])).

cnf(c_0_44,plain,
    ( k7_relat_1(X1,X2) = k5_relat_1(k6_relat_1(X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_45,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_46,plain,
    ( k5_relat_1(k5_relat_1(X1,X2),X3) = k5_relat_1(X1,k5_relat_1(X2,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_47,plain,
    ( k7_relat_1(X1,X2) = X1
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_48,plain,
    ( k1_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_49,plain,
    ( r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X1) ),
    inference(rw,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_50,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_41,c_0_40])).

cnf(c_0_51,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = k4_xboole_0(k1_relat_1(X1),k4_xboole_0(k1_relat_1(X1),X2))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_42,c_0_40])).

cnf(c_0_52,plain,
    ( v1_relat_1(k5_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_53,plain,
    ( k7_relat_1(k6_relat_1(X1),X2) = k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

fof(c_0_54,plain,(
    ! [X23,X24,X25] :
      ( ~ v1_relat_1(X25)
      | k7_relat_1(k7_relat_1(X25,X23),X24) = k7_relat_1(X25,k3_xboole_0(X23,X24)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t100_relat_1])])).

cnf(c_0_55,plain,
    ( k5_relat_1(k5_relat_1(k6_relat_1(X1),X2),X3) = k5_relat_1(k6_relat_1(X1),k5_relat_1(X2,X3))
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_46,c_0_45])).

cnf(c_0_56,plain,
    ( k7_relat_1(k6_relat_1(X1),X2) = k6_relat_1(X1)
    | ~ r1_tarski(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_45])])).

cnf(c_0_57,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_58,plain,
    ( k1_relat_1(k7_relat_1(k6_relat_1(X1),X2)) = k4_xboole_0(X1,k4_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_45]),c_0_48]),c_0_48])).

cnf(c_0_59,plain,
    ( v1_relat_1(k7_relat_1(k6_relat_1(X1),X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_45]),c_0_45])])).

cnf(c_0_60,plain,
    ( k7_relat_1(k7_relat_1(X1,X2),X3) = k7_relat_1(X1,k3_xboole_0(X2,X3))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

fof(c_0_61,plain,(
    ! [X4,X5] : k3_xboole_0(X4,X5) = k3_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_62,plain,
    ( k5_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)),X3) = k5_relat_1(k6_relat_1(X1),k5_relat_1(k6_relat_1(X2),X3))
    | ~ v1_relat_1(X3) ),
    inference(spm,[status(thm)],[c_0_55,c_0_45])).

cnf(c_0_63,plain,
    ( k7_relat_1(k6_relat_1(k4_xboole_0(X1,X2)),X1) = k6_relat_1(k4_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_64,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X3) = k7_relat_1(k6_relat_1(X1),X2)
    | ~ r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_58]),c_0_59])])).

cnf(c_0_65,plain,
    ( k7_relat_1(k7_relat_1(X1,X2),X3) = k7_relat_1(X1,k1_setfam_1(k2_enumset1(X2,X2,X2,X3)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_60,c_0_29]),c_0_30])).

cnf(c_0_66,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

fof(c_0_67,plain,(
    ! [X6,X7] :
      ( ( r1_tarski(X6,X7)
        | X6 != X7 )
      & ( r1_tarski(X7,X6)
        | X6 != X7 )
      & ( ~ r1_tarski(X6,X7)
        | ~ r1_tarski(X7,X6)
        | X6 = X7 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_68,plain,
    ( k5_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)),k6_relat_1(X3)) = k5_relat_1(k6_relat_1(X1),k5_relat_1(k6_relat_1(X2),k6_relat_1(X3))) ),
    inference(spm,[status(thm)],[c_0_62,c_0_45])).

cnf(c_0_69,plain,
    ( k5_relat_1(k6_relat_1(X1),k6_relat_1(k4_xboole_0(X1,X2))) = k6_relat_1(k4_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[c_0_63,c_0_53])).

cnf(c_0_70,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X1) = k7_relat_1(k6_relat_1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_64,c_0_57])).

cnf(c_0_71,plain,
    ( k7_relat_1(k7_relat_1(X1,X2),X3) = k7_relat_1(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_65,c_0_40])).

cnf(c_0_72,plain,
    ( k1_setfam_1(k2_enumset1(X1,X1,X1,X2)) = k1_setfam_1(k2_enumset1(X2,X2,X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66,c_0_29]),c_0_29]),c_0_30]),c_0_30])).

fof(c_0_73,plain,(
    ! [X32,X33] :
      ( ~ v1_relat_1(X33)
      | ~ r1_tarski(k1_relat_1(X33),X32)
      | k5_relat_1(k6_relat_1(X32),X33) = X33 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t77_relat_1])])).

cnf(c_0_74,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_75,plain,
    ( v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_44]),c_0_45])])).

cnf(c_0_76,plain,
    ( k5_relat_1(k6_relat_1(X1),k5_relat_1(k6_relat_1(k4_xboole_0(X1,X2)),k6_relat_1(X3))) = k5_relat_1(k6_relat_1(k4_xboole_0(X1,X2)),k6_relat_1(X3)) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_77,plain,
    ( k7_relat_1(k6_relat_1(X1),k4_xboole_0(X2,k4_xboole_0(X2,X1))) = k7_relat_1(k6_relat_1(X1),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_45])])).

cnf(c_0_78,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X2,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_72,c_0_40]),c_0_40])).

fof(c_0_79,plain,(
    ! [X30,X31] :
      ( ( r1_tarski(k5_relat_1(X31,k6_relat_1(X30)),X31)
        | ~ v1_relat_1(X31) )
      & ( r1_tarski(k5_relat_1(k6_relat_1(X30),X31),X31)
        | ~ v1_relat_1(X31) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t76_relat_1])])])).

cnf(c_0_80,plain,
    ( k5_relat_1(k6_relat_1(X2),X1) = X1
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_81,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_74])).

cnf(c_0_82,plain,
    ( v1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_53]),c_0_45])])).

cnf(c_0_83,plain,
    ( k7_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)),X3) = k7_relat_1(k6_relat_1(X2),k4_xboole_0(X1,k4_xboole_0(X1,X3))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_53]),c_0_45])])).

cnf(c_0_84,plain,
    ( k5_relat_1(k6_relat_1(X1),k7_relat_1(k6_relat_1(X2),k4_xboole_0(X1,X3))) = k7_relat_1(k6_relat_1(X2),k4_xboole_0(X1,X3)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_44]),c_0_45])])).

cnf(c_0_85,plain,
    ( k7_relat_1(k6_relat_1(X1),k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k7_relat_1(k6_relat_1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_77,c_0_78])).

cnf(c_0_86,plain,
    ( r1_tarski(k5_relat_1(X1,k6_relat_1(X2)),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_79])).

cnf(c_0_87,plain,
    ( k5_relat_1(k6_relat_1(k1_relat_1(X1)),X1) = X1
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_80,c_0_81])).

cnf(c_0_88,plain,
    ( k7_relat_1(k6_relat_1(X1),k4_xboole_0(X2,k4_xboole_0(X2,X3))) = k5_relat_1(k6_relat_1(X3),k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_82]),c_0_83])).

cnf(c_0_89,plain,
    ( k5_relat_1(k6_relat_1(X1),k7_relat_1(k6_relat_1(X1),X2)) = k7_relat_1(k6_relat_1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_84,c_0_85])).

cnf(c_0_90,plain,
    ( r1_tarski(k5_relat_1(k6_relat_1(X1),k5_relat_1(k6_relat_1(X2),k6_relat_1(X3))),k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_82]),c_0_68])).

cnf(c_0_91,plain,
    ( k5_relat_1(k6_relat_1(k1_relat_1(k5_relat_1(X1,X2))),k5_relat_1(X1,X2)) = k5_relat_1(X1,X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_87,c_0_52])).

cnf(c_0_92,plain,
    ( k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) = k4_xboole_0(X2,k4_xboole_0(X2,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_53]),c_0_48]),c_0_48]),c_0_45])])).

cnf(c_0_93,plain,
    ( k5_relat_1(k6_relat_1(k4_xboole_0(X1,k4_xboole_0(X1,X2))),k6_relat_1(X3)) = k5_relat_1(k6_relat_1(X2),k5_relat_1(k6_relat_1(X1),k6_relat_1(X3))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_88]),c_0_45])])).

cnf(c_0_94,plain,
    ( k5_relat_1(k6_relat_1(X1),k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))) = k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_44]),c_0_45])])).

fof(c_0_95,negated_conjecture,(
    ~ ! [X1,X2] : k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)) = k6_relat_1(k3_xboole_0(X1,X2)) ),
    inference(assume_negation,[status(cth)],[t43_funct_1])).

cnf(c_0_96,plain,
    ( r1_tarski(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)),k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_91]),c_0_92]),c_0_93]),c_0_94]),c_0_45]),c_0_45])])).

fof(c_0_97,negated_conjecture,(
    k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0)) != k6_relat_1(k3_xboole_0(esk1_0,esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_95])])])).

cnf(c_0_98,plain,
    ( r1_tarski(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)),k7_relat_1(k6_relat_1(X1),X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_44]),c_0_45])])).

cnf(c_0_99,negated_conjecture,
    ( k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0)) != k6_relat_1(k3_xboole_0(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_97])).

cnf(c_0_100,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_101,plain,
    ( r1_tarski(k7_relat_1(k6_relat_1(X1),X2),k7_relat_1(k6_relat_1(X2),X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_44]),c_0_45])])).

cnf(c_0_102,negated_conjecture,
    ( k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0)) != k6_relat_1(k1_setfam_1(k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_99,c_0_29]),c_0_30])).

cnf(c_0_103,plain,
    ( k7_relat_1(k6_relat_1(X1),X2) = k7_relat_1(k6_relat_1(X2),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_101]),c_0_101])])).

cnf(c_0_104,negated_conjecture,
    ( k6_relat_1(k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk2_0))) != k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0)) ),
    inference(rw,[status(thm)],[c_0_102,c_0_40])).

cnf(c_0_105,plain,
    ( k7_relat_1(k6_relat_1(X1),X2) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_103]),c_0_45])])).

cnf(c_0_106,negated_conjecture,
    ( k6_relat_1(k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk1_0))) != k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0)) ),
    inference(rw,[status(thm)],[c_0_104,c_0_78])).

cnf(c_0_107,plain,
    ( k6_relat_1(k4_xboole_0(X1,X2)) = k7_relat_1(k6_relat_1(X1),k4_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[c_0_69,c_0_105])).

cnf(c_0_108,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_106,c_0_105]),c_0_107]),c_0_85])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n005.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 13:16:02 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.51  # AutoSched0-Mode selected heuristic H_____042_B03_F1_AE_Q4_SP_S2S
% 0.19/0.51  # and selection function SelectNewComplexAHP.
% 0.19/0.51  #
% 0.19/0.51  # Preprocessing time       : 0.027 s
% 0.19/0.51  
% 0.19/0.51  # Proof found!
% 0.19/0.51  # SZS status Theorem
% 0.19/0.51  # SZS output start CNFRefutation
% 0.19/0.51  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.19/0.51  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.19/0.51  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 0.19/0.51  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.19/0.51  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.19/0.51  fof(t47_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 0.19/0.52  fof(t90_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k1_relat_1(k7_relat_1(X2,X1))=k3_xboole_0(k1_relat_1(X2),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_relat_1)).
% 0.19/0.52  fof(t94_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k7_relat_1(X2,X1)=k5_relat_1(k6_relat_1(X1),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 0.19/0.52  fof(fc3_funct_1, axiom, ![X1]:(v1_relat_1(k6_relat_1(X1))&v1_funct_1(k6_relat_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 0.19/0.52  fof(t55_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>k5_relat_1(k5_relat_1(X1,X2),X3)=k5_relat_1(X1,k5_relat_1(X2,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_relat_1)).
% 0.19/0.52  fof(t97_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k1_relat_1(X2),X1)=>k7_relat_1(X2,X1)=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 0.19/0.52  fof(t71_relat_1, axiom, ![X1]:(k1_relat_1(k6_relat_1(X1))=X1&k2_relat_1(k6_relat_1(X1))=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 0.19/0.52  fof(dt_k5_relat_1, axiom, ![X1, X2]:((v1_relat_1(X1)&v1_relat_1(X2))=>v1_relat_1(k5_relat_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 0.19/0.52  fof(t100_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>k7_relat_1(k7_relat_1(X3,X1),X2)=k7_relat_1(X3,k3_xboole_0(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_relat_1)).
% 0.19/0.52  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.19/0.52  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.19/0.52  fof(t77_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k1_relat_1(X2),X1)=>k5_relat_1(k6_relat_1(X1),X2)=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_relat_1)).
% 0.19/0.52  fof(t76_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k5_relat_1(X2,k6_relat_1(X1)),X2)&r1_tarski(k5_relat_1(k6_relat_1(X1),X2),X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_relat_1)).
% 0.19/0.52  fof(t43_funct_1, conjecture, ![X1, X2]:k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))=k6_relat_1(k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_funct_1)).
% 0.19/0.52  fof(c_0_19, plain, ![X19, X20]:k1_setfam_1(k2_tarski(X19,X20))=k3_xboole_0(X19,X20), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.19/0.52  fof(c_0_20, plain, ![X14, X15]:k1_enumset1(X14,X14,X15)=k2_tarski(X14,X15), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.19/0.52  fof(c_0_21, plain, ![X8, X9]:r1_tarski(k3_xboole_0(X8,X9),X8), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 0.19/0.52  cnf(c_0_22, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.52  cnf(c_0_23, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.52  fof(c_0_24, plain, ![X16, X17, X18]:k2_enumset1(X16,X16,X17,X18)=k1_enumset1(X16,X17,X18), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.19/0.52  fof(c_0_25, plain, ![X12, X13]:k4_xboole_0(X12,k4_xboole_0(X12,X13))=k3_xboole_0(X12,X13), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.19/0.52  fof(c_0_26, plain, ![X10, X11]:k4_xboole_0(X10,k3_xboole_0(X10,X11))=k4_xboole_0(X10,X11), inference(variable_rename,[status(thm)],[t47_xboole_1])).
% 0.19/0.52  fof(c_0_27, plain, ![X35, X36]:(~v1_relat_1(X36)|k1_relat_1(k7_relat_1(X36,X35))=k3_xboole_0(k1_relat_1(X36),X35)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t90_relat_1])])).
% 0.19/0.52  cnf(c_0_28, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.52  cnf(c_0_29, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_22, c_0_23])).
% 0.19/0.52  cnf(c_0_30, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.52  cnf(c_0_31, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.52  cnf(c_0_32, plain, (k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.52  cnf(c_0_33, plain, (k1_relat_1(k7_relat_1(X1,X2))=k3_xboole_0(k1_relat_1(X1),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.52  fof(c_0_34, plain, ![X37, X38]:(~v1_relat_1(X38)|k7_relat_1(X38,X37)=k5_relat_1(k6_relat_1(X37),X38)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).
% 0.19/0.52  fof(c_0_35, plain, ![X41]:(v1_relat_1(k6_relat_1(X41))&v1_funct_1(k6_relat_1(X41))), inference(variable_rename,[status(thm)],[fc3_funct_1])).
% 0.19/0.52  fof(c_0_36, plain, ![X26, X27, X28]:(~v1_relat_1(X26)|(~v1_relat_1(X27)|(~v1_relat_1(X28)|k5_relat_1(k5_relat_1(X26,X27),X28)=k5_relat_1(X26,k5_relat_1(X27,X28))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_relat_1])])])).
% 0.19/0.52  fof(c_0_37, plain, ![X39, X40]:(~v1_relat_1(X40)|(~r1_tarski(k1_relat_1(X40),X39)|k7_relat_1(X40,X39)=X40)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t97_relat_1])])).
% 0.19/0.52  fof(c_0_38, plain, ![X29]:(k1_relat_1(k6_relat_1(X29))=X29&k2_relat_1(k6_relat_1(X29))=X29), inference(variable_rename,[status(thm)],[t71_relat_1])).
% 0.19/0.52  cnf(c_0_39, plain, (r1_tarski(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_29]), c_0_30])).
% 0.19/0.52  cnf(c_0_40, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k1_setfam_1(k2_enumset1(X1,X1,X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_29]), c_0_30])).
% 0.19/0.52  cnf(c_0_41, plain, (k4_xboole_0(X1,k1_setfam_1(k2_enumset1(X1,X1,X1,X2)))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_29]), c_0_30])).
% 0.19/0.52  cnf(c_0_42, plain, (k1_relat_1(k7_relat_1(X1,X2))=k1_setfam_1(k2_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X2))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33, c_0_29]), c_0_30])).
% 0.19/0.52  fof(c_0_43, plain, ![X21, X22]:(~v1_relat_1(X21)|~v1_relat_1(X22)|v1_relat_1(k5_relat_1(X21,X22))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_relat_1])])).
% 0.19/0.52  cnf(c_0_44, plain, (k7_relat_1(X1,X2)=k5_relat_1(k6_relat_1(X2),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.19/0.52  cnf(c_0_45, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.19/0.52  cnf(c_0_46, plain, (k5_relat_1(k5_relat_1(X1,X2),X3)=k5_relat_1(X1,k5_relat_1(X2,X3))|~v1_relat_1(X1)|~v1_relat_1(X2)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.19/0.52  cnf(c_0_47, plain, (k7_relat_1(X1,X2)=X1|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.19/0.52  cnf(c_0_48, plain, (k1_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.19/0.52  cnf(c_0_49, plain, (r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X1)), inference(rw,[status(thm)],[c_0_39, c_0_40])).
% 0.19/0.52  cnf(c_0_50, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2)))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_41, c_0_40])).
% 0.19/0.52  cnf(c_0_51, plain, (k1_relat_1(k7_relat_1(X1,X2))=k4_xboole_0(k1_relat_1(X1),k4_xboole_0(k1_relat_1(X1),X2))|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_42, c_0_40])).
% 0.19/0.52  cnf(c_0_52, plain, (v1_relat_1(k5_relat_1(X1,X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.19/0.52  cnf(c_0_53, plain, (k7_relat_1(k6_relat_1(X1),X2)=k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.19/0.52  fof(c_0_54, plain, ![X23, X24, X25]:(~v1_relat_1(X25)|k7_relat_1(k7_relat_1(X25,X23),X24)=k7_relat_1(X25,k3_xboole_0(X23,X24))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t100_relat_1])])).
% 0.19/0.52  cnf(c_0_55, plain, (k5_relat_1(k5_relat_1(k6_relat_1(X1),X2),X3)=k5_relat_1(k6_relat_1(X1),k5_relat_1(X2,X3))|~v1_relat_1(X3)|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_46, c_0_45])).
% 0.19/0.52  cnf(c_0_56, plain, (k7_relat_1(k6_relat_1(X1),X2)=k6_relat_1(X1)|~r1_tarski(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_45])])).
% 0.19/0.52  cnf(c_0_57, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.19/0.52  cnf(c_0_58, plain, (k1_relat_1(k7_relat_1(k6_relat_1(X1),X2))=k4_xboole_0(X1,k4_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_45]), c_0_48]), c_0_48])).
% 0.19/0.52  cnf(c_0_59, plain, (v1_relat_1(k7_relat_1(k6_relat_1(X1),X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_45]), c_0_45])])).
% 0.19/0.52  cnf(c_0_60, plain, (k7_relat_1(k7_relat_1(X1,X2),X3)=k7_relat_1(X1,k3_xboole_0(X2,X3))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.19/0.52  fof(c_0_61, plain, ![X4, X5]:k3_xboole_0(X4,X5)=k3_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.19/0.52  cnf(c_0_62, plain, (k5_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)),X3)=k5_relat_1(k6_relat_1(X1),k5_relat_1(k6_relat_1(X2),X3))|~v1_relat_1(X3)), inference(spm,[status(thm)],[c_0_55, c_0_45])).
% 0.19/0.52  cnf(c_0_63, plain, (k7_relat_1(k6_relat_1(k4_xboole_0(X1,X2)),X1)=k6_relat_1(k4_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.19/0.52  cnf(c_0_64, plain, (k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X3)=k7_relat_1(k6_relat_1(X1),X2)|~r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_58]), c_0_59])])).
% 0.19/0.52  cnf(c_0_65, plain, (k7_relat_1(k7_relat_1(X1,X2),X3)=k7_relat_1(X1,k1_setfam_1(k2_enumset1(X2,X2,X2,X3)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_60, c_0_29]), c_0_30])).
% 0.19/0.52  cnf(c_0_66, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.19/0.52  fof(c_0_67, plain, ![X6, X7]:(((r1_tarski(X6,X7)|X6!=X7)&(r1_tarski(X7,X6)|X6!=X7))&(~r1_tarski(X6,X7)|~r1_tarski(X7,X6)|X6=X7)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.19/0.52  cnf(c_0_68, plain, (k5_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)),k6_relat_1(X3))=k5_relat_1(k6_relat_1(X1),k5_relat_1(k6_relat_1(X2),k6_relat_1(X3)))), inference(spm,[status(thm)],[c_0_62, c_0_45])).
% 0.19/0.52  cnf(c_0_69, plain, (k5_relat_1(k6_relat_1(X1),k6_relat_1(k4_xboole_0(X1,X2)))=k6_relat_1(k4_xboole_0(X1,X2))), inference(rw,[status(thm)],[c_0_63, c_0_53])).
% 0.19/0.52  cnf(c_0_70, plain, (k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X1)=k7_relat_1(k6_relat_1(X1),X2)), inference(spm,[status(thm)],[c_0_64, c_0_57])).
% 0.19/0.52  cnf(c_0_71, plain, (k7_relat_1(k7_relat_1(X1,X2),X3)=k7_relat_1(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_65, c_0_40])).
% 0.19/0.52  cnf(c_0_72, plain, (k1_setfam_1(k2_enumset1(X1,X1,X1,X2))=k1_setfam_1(k2_enumset1(X2,X2,X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66, c_0_29]), c_0_29]), c_0_30]), c_0_30])).
% 0.19/0.52  fof(c_0_73, plain, ![X32, X33]:(~v1_relat_1(X33)|(~r1_tarski(k1_relat_1(X33),X32)|k5_relat_1(k6_relat_1(X32),X33)=X33)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t77_relat_1])])).
% 0.19/0.52  cnf(c_0_74, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.19/0.52  cnf(c_0_75, plain, (v1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_44]), c_0_45])])).
% 0.19/0.52  cnf(c_0_76, plain, (k5_relat_1(k6_relat_1(X1),k5_relat_1(k6_relat_1(k4_xboole_0(X1,X2)),k6_relat_1(X3)))=k5_relat_1(k6_relat_1(k4_xboole_0(X1,X2)),k6_relat_1(X3))), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 0.19/0.52  cnf(c_0_77, plain, (k7_relat_1(k6_relat_1(X1),k4_xboole_0(X2,k4_xboole_0(X2,X1)))=k7_relat_1(k6_relat_1(X1),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_71]), c_0_45])])).
% 0.19/0.52  cnf(c_0_78, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k4_xboole_0(X2,k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_72, c_0_40]), c_0_40])).
% 0.19/0.52  fof(c_0_79, plain, ![X30, X31]:((r1_tarski(k5_relat_1(X31,k6_relat_1(X30)),X31)|~v1_relat_1(X31))&(r1_tarski(k5_relat_1(k6_relat_1(X30),X31),X31)|~v1_relat_1(X31))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t76_relat_1])])])).
% 0.19/0.52  cnf(c_0_80, plain, (k5_relat_1(k6_relat_1(X2),X1)=X1|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_73])).
% 0.19/0.52  cnf(c_0_81, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_74])).
% 0.19/0.52  cnf(c_0_82, plain, (v1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_53]), c_0_45])])).
% 0.19/0.52  cnf(c_0_83, plain, (k7_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)),X3)=k7_relat_1(k6_relat_1(X2),k4_xboole_0(X1,k4_xboole_0(X1,X3)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_53]), c_0_45])])).
% 0.19/0.52  cnf(c_0_84, plain, (k5_relat_1(k6_relat_1(X1),k7_relat_1(k6_relat_1(X2),k4_xboole_0(X1,X3)))=k7_relat_1(k6_relat_1(X2),k4_xboole_0(X1,X3))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_44]), c_0_45])])).
% 0.19/0.52  cnf(c_0_85, plain, (k7_relat_1(k6_relat_1(X1),k4_xboole_0(X1,k4_xboole_0(X1,X2)))=k7_relat_1(k6_relat_1(X1),X2)), inference(spm,[status(thm)],[c_0_77, c_0_78])).
% 0.19/0.52  cnf(c_0_86, plain, (r1_tarski(k5_relat_1(X1,k6_relat_1(X2)),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_79])).
% 0.19/0.52  cnf(c_0_87, plain, (k5_relat_1(k6_relat_1(k1_relat_1(X1)),X1)=X1|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_80, c_0_81])).
% 0.19/0.52  cnf(c_0_88, plain, (k7_relat_1(k6_relat_1(X1),k4_xboole_0(X2,k4_xboole_0(X2,X3)))=k5_relat_1(k6_relat_1(X3),k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_82]), c_0_83])).
% 0.19/0.52  cnf(c_0_89, plain, (k5_relat_1(k6_relat_1(X1),k7_relat_1(k6_relat_1(X1),X2))=k7_relat_1(k6_relat_1(X1),X2)), inference(spm,[status(thm)],[c_0_84, c_0_85])).
% 0.19/0.52  cnf(c_0_90, plain, (r1_tarski(k5_relat_1(k6_relat_1(X1),k5_relat_1(k6_relat_1(X2),k6_relat_1(X3))),k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_82]), c_0_68])).
% 0.19/0.52  cnf(c_0_91, plain, (k5_relat_1(k6_relat_1(k1_relat_1(k5_relat_1(X1,X2))),k5_relat_1(X1,X2))=k5_relat_1(X1,X2)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_87, c_0_52])).
% 0.19/0.52  cnf(c_0_92, plain, (k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))=k4_xboole_0(X2,k4_xboole_0(X2,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_53]), c_0_48]), c_0_48]), c_0_45])])).
% 0.19/0.52  cnf(c_0_93, plain, (k5_relat_1(k6_relat_1(k4_xboole_0(X1,k4_xboole_0(X1,X2))),k6_relat_1(X3))=k5_relat_1(k6_relat_1(X2),k5_relat_1(k6_relat_1(X1),k6_relat_1(X3)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_88]), c_0_45])])).
% 0.19/0.52  cnf(c_0_94, plain, (k5_relat_1(k6_relat_1(X1),k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)))=k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_44]), c_0_45])])).
% 0.19/0.52  fof(c_0_95, negated_conjecture, ~(![X1, X2]:k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))=k6_relat_1(k3_xboole_0(X1,X2))), inference(assume_negation,[status(cth)],[t43_funct_1])).
% 0.19/0.52  cnf(c_0_96, plain, (r1_tarski(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)),k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_91]), c_0_92]), c_0_93]), c_0_94]), c_0_45]), c_0_45])])).
% 0.19/0.52  fof(c_0_97, negated_conjecture, k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0))!=k6_relat_1(k3_xboole_0(esk1_0,esk2_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_95])])])).
% 0.19/0.52  cnf(c_0_98, plain, (r1_tarski(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)),k7_relat_1(k6_relat_1(X1),X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_44]), c_0_45])])).
% 0.19/0.52  cnf(c_0_99, negated_conjecture, (k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0))!=k6_relat_1(k3_xboole_0(esk1_0,esk2_0))), inference(split_conjunct,[status(thm)],[c_0_97])).
% 0.19/0.52  cnf(c_0_100, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.19/0.52  cnf(c_0_101, plain, (r1_tarski(k7_relat_1(k6_relat_1(X1),X2),k7_relat_1(k6_relat_1(X2),X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_44]), c_0_45])])).
% 0.19/0.52  cnf(c_0_102, negated_conjecture, (k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0))!=k6_relat_1(k1_setfam_1(k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_99, c_0_29]), c_0_30])).
% 0.19/0.52  cnf(c_0_103, plain, (k7_relat_1(k6_relat_1(X1),X2)=k7_relat_1(k6_relat_1(X2),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_101]), c_0_101])])).
% 0.19/0.52  cnf(c_0_104, negated_conjecture, (k6_relat_1(k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk2_0)))!=k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0))), inference(rw,[status(thm)],[c_0_102, c_0_40])).
% 0.19/0.52  cnf(c_0_105, plain, (k7_relat_1(k6_relat_1(X1),X2)=k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_103]), c_0_45])])).
% 0.19/0.52  cnf(c_0_106, negated_conjecture, (k6_relat_1(k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk1_0)))!=k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0))), inference(rw,[status(thm)],[c_0_104, c_0_78])).
% 0.19/0.52  cnf(c_0_107, plain, (k6_relat_1(k4_xboole_0(X1,X2))=k7_relat_1(k6_relat_1(X1),k4_xboole_0(X1,X2))), inference(rw,[status(thm)],[c_0_69, c_0_105])).
% 0.19/0.52  cnf(c_0_108, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_106, c_0_105]), c_0_107]), c_0_85])]), ['proof']).
% 0.19/0.52  # SZS output end CNFRefutation
% 0.19/0.52  # Proof object total steps             : 109
% 0.19/0.52  # Proof object clause steps            : 70
% 0.19/0.52  # Proof object formula steps           : 39
% 0.19/0.52  # Proof object conjectures             : 8
% 0.19/0.52  # Proof object clause conjectures      : 5
% 0.19/0.52  # Proof object formula conjectures     : 3
% 0.19/0.52  # Proof object initial clauses used    : 20
% 0.19/0.52  # Proof object initial formulas used   : 19
% 0.19/0.52  # Proof object generating inferences   : 31
% 0.19/0.52  # Proof object simplifying inferences  : 75
% 0.19/0.52  # Training examples: 0 positive, 0 negative
% 0.19/0.52  # Parsed axioms                        : 20
% 0.19/0.52  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.52  # Initial clauses                      : 25
% 0.19/0.52  # Removed in clause preprocessing      : 3
% 0.19/0.52  # Initial clauses in saturation        : 22
% 0.19/0.52  # Processed clauses                    : 1353
% 0.19/0.52  # ...of these trivial                  : 179
% 0.19/0.52  # ...subsumed                          : 843
% 0.19/0.52  # ...remaining for further processing  : 330
% 0.19/0.52  # Other redundant clauses eliminated   : 2
% 0.19/0.52  # Clauses deleted for lack of memory   : 0
% 0.19/0.52  # Backward-subsumed                    : 16
% 0.19/0.52  # Backward-rewritten                   : 71
% 0.19/0.52  # Generated clauses                    : 15273
% 0.19/0.52  # ...of the previous two non-trivial   : 11712
% 0.19/0.52  # Contextual simplify-reflections      : 0
% 0.19/0.52  # Paramodulations                      : 15271
% 0.19/0.52  # Factorizations                       : 0
% 0.19/0.52  # Equation resolutions                 : 2
% 0.19/0.52  # Propositional unsat checks           : 0
% 0.19/0.52  #    Propositional check models        : 0
% 0.19/0.52  #    Propositional check unsatisfiable : 0
% 0.19/0.52  #    Propositional clauses             : 0
% 0.19/0.52  #    Propositional clauses after purity: 0
% 0.19/0.52  #    Propositional unsat core size     : 0
% 0.19/0.52  #    Propositional preprocessing time  : 0.000
% 0.19/0.52  #    Propositional encoding time       : 0.000
% 0.19/0.52  #    Propositional solver time         : 0.000
% 0.19/0.52  #    Success case prop preproc time    : 0.000
% 0.19/0.52  #    Success case prop encoding time   : 0.000
% 0.19/0.52  #    Success case prop solver time     : 0.000
% 0.19/0.52  # Current number of processed clauses  : 241
% 0.19/0.52  #    Positive orientable unit clauses  : 95
% 0.19/0.52  #    Positive unorientable unit clauses: 6
% 0.19/0.52  #    Negative unit clauses             : 0
% 0.19/0.52  #    Non-unit-clauses                  : 140
% 0.19/0.52  # Current number of unprocessed clauses: 10236
% 0.19/0.52  # ...number of literals in the above   : 21991
% 0.19/0.52  # Current number of archived formulas  : 0
% 0.19/0.52  # Current number of archived clauses   : 90
% 0.19/0.52  # Clause-clause subsumption calls (NU) : 4633
% 0.19/0.52  # Rec. Clause-clause subsumption calls : 3893
% 0.19/0.52  # Non-unit clause-clause subsumptions  : 822
% 0.19/0.52  # Unit Clause-clause subsumption calls : 154
% 0.19/0.52  # Rewrite failures with RHS unbound    : 0
% 0.19/0.52  # BW rewrite match attempts            : 445
% 0.19/0.52  # BW rewrite match successes           : 149
% 0.19/0.52  # Condensation attempts                : 0
% 0.19/0.52  # Condensation successes               : 0
% 0.19/0.52  # Termbank termtop insertions          : 240807
% 0.19/0.52  
% 0.19/0.52  # -------------------------------------------------
% 0.19/0.52  # User time                : 0.171 s
% 0.19/0.52  # System time              : 0.010 s
% 0.19/0.52  # Total time               : 0.181 s
% 0.19/0.52  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
