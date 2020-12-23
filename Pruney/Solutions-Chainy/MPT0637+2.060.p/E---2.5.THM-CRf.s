%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:53:32 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  124 (5998 expanded)
%              Number of clauses        :   75 (2447 expanded)
%              Number of leaves         :   24 (1775 expanded)
%              Depth                    :   14
%              Number of atoms          :  205 (9784 expanded)
%              Number of equality atoms :  104 (3654 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    3 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t80_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k5_relat_1(X1,k6_relat_1(k2_relat_1(X1))) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

fof(t71_relat_1,axiom,(
    ! [X1] :
      ( k1_relat_1(k6_relat_1(X1)) = X1
      & k2_relat_1(k6_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(dt_k6_relat_1,axiom,(
    ! [X1] : v1_relat_1(k6_relat_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(t123_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k8_relat_1(X1,X2) = k5_relat_1(X2,k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).

fof(t94_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,X1) = k5_relat_1(k6_relat_1(X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(t45_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => r1_tarski(k2_relat_1(k5_relat_1(X1,X2)),k2_relat_1(X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).

fof(dt_k5_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X2) )
     => v1_relat_1(k5_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(t139_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => k8_relat_1(X1,k5_relat_1(X2,X3)) = k5_relat_1(X2,k8_relat_1(X1,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_relat_1)).

fof(t97_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k1_relat_1(X2),X1)
       => k7_relat_1(X2,X1) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

fof(t77_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k1_relat_1(X2),X1)
       => k5_relat_1(k6_relat_1(X1),X2) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).

fof(t89_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k1_relat_1(k7_relat_1(X2,X1)),k1_relat_1(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t89_relat_1)).

fof(t112_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => k7_relat_1(k5_relat_1(X2,X3),X1) = k5_relat_1(k7_relat_1(X2,X1),X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_relat_1)).

fof(t54_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k4_relat_1(k5_relat_1(X1,X2)) = k5_relat_1(k4_relat_1(X2),k4_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_relat_1)).

fof(t72_relat_1,axiom,(
    ! [X1] : k4_relat_1(k6_relat_1(X1)) = k6_relat_1(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_relat_1)).

fof(t148_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k2_relat_1(k7_relat_1(X2,X1)) = k9_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(t43_funct_1,conjecture,(
    ! [X1,X2] : k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)) = k6_relat_1(k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(t75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(t90_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k1_relat_1(k7_relat_1(X2,X1)) = k3_xboole_0(k1_relat_1(X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

fof(c_0_24,plain,(
    ! [X58] :
      ( ~ v1_relat_1(X58)
      | k5_relat_1(X58,k6_relat_1(k2_relat_1(X58))) = X58 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t80_relat_1])])).

fof(c_0_25,plain,(
    ! [X54] :
      ( k1_relat_1(k6_relat_1(X54)) = X54
      & k2_relat_1(k6_relat_1(X54)) = X54 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

fof(c_0_26,plain,(
    ! [X39] : v1_relat_1(k6_relat_1(X39)) ),
    inference(variable_rename,[status(thm)],[dt_k6_relat_1])).

fof(c_0_27,plain,(
    ! [X43,X44] :
      ( ~ v1_relat_1(X44)
      | k8_relat_1(X43,X44) = k5_relat_1(X44,k6_relat_1(X43)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t123_relat_1])])).

fof(c_0_28,plain,(
    ! [X63,X64] :
      ( ~ v1_relat_1(X64)
      | k7_relat_1(X64,X63) = k5_relat_1(k6_relat_1(X63),X64) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).

fof(c_0_29,plain,(
    ! [X50,X51] :
      ( ~ v1_relat_1(X50)
      | ~ v1_relat_1(X51)
      | r1_tarski(k2_relat_1(k5_relat_1(X50,X51)),k2_relat_1(X51)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t45_relat_1])])])).

cnf(c_0_30,plain,
    ( k5_relat_1(X1,k6_relat_1(k2_relat_1(X1))) = X1
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,plain,
    ( k2_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_32,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_33,plain,(
    ! [X37,X38] :
      ( ~ v1_relat_1(X37)
      | ~ v1_relat_1(X38)
      | v1_relat_1(k5_relat_1(X37,X38)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_relat_1])])).

fof(c_0_34,plain,(
    ! [X45,X46,X47] :
      ( ~ v1_relat_1(X46)
      | ~ v1_relat_1(X47)
      | k8_relat_1(X45,k5_relat_1(X46,X47)) = k5_relat_1(X46,k8_relat_1(X45,X47)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t139_relat_1])])])).

cnf(c_0_35,plain,
    ( k8_relat_1(X2,X1) = k5_relat_1(X1,k6_relat_1(X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_36,plain,
    ( k7_relat_1(X1,X2) = k5_relat_1(k6_relat_1(X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_37,plain,(
    ! [X65,X66] :
      ( ~ v1_relat_1(X66)
      | ~ r1_tarski(k1_relat_1(X66),X65)
      | k7_relat_1(X66,X65) = X66 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t97_relat_1])])).

cnf(c_0_38,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X1,X2)),k2_relat_1(X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_39,plain,
    ( k5_relat_1(k6_relat_1(X1),k6_relat_1(X1)) = k6_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32])])).

fof(c_0_40,plain,(
    ! [X56,X57] :
      ( ~ v1_relat_1(X57)
      | ~ r1_tarski(k1_relat_1(X57),X56)
      | k5_relat_1(k6_relat_1(X56),X57) = X57 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t77_relat_1])])).

fof(c_0_41,plain,(
    ! [X59,X60] :
      ( ~ v1_relat_1(X60)
      | r1_tarski(k1_relat_1(k7_relat_1(X60,X59)),k1_relat_1(X60)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t89_relat_1])])).

cnf(c_0_42,plain,
    ( v1_relat_1(k5_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

fof(c_0_43,plain,(
    ! [X40,X41,X42] :
      ( ~ v1_relat_1(X41)
      | ~ v1_relat_1(X42)
      | k7_relat_1(k5_relat_1(X41,X42),X40) = k5_relat_1(k7_relat_1(X41,X40),X42) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t112_relat_1])])])).

cnf(c_0_44,plain,
    ( k8_relat_1(X3,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X3,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_45,plain,
    ( k8_relat_1(X1,k6_relat_1(X2)) = k7_relat_1(k6_relat_1(X1),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_32]),c_0_32])])).

cnf(c_0_46,plain,
    ( k7_relat_1(X1,X2) = X1
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_47,plain,
    ( r1_tarski(X1,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_31]),c_0_31]),c_0_32])])).

cnf(c_0_48,plain,
    ( k5_relat_1(k6_relat_1(X2),X1) = X1
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_49,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_50,plain,
    ( v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_36]),c_0_32])])).

cnf(c_0_51,plain,
    ( k7_relat_1(k5_relat_1(X1,X2),X3) = k5_relat_1(k7_relat_1(X1,X3),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_52,plain,
    ( v1_relat_1(k8_relat_1(X1,X2))
    | ~ v1_relat_1(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_35]),c_0_32])])).

fof(c_0_53,plain,(
    ! [X52,X53] :
      ( ~ v1_relat_1(X52)
      | ~ v1_relat_1(X53)
      | k4_relat_1(k5_relat_1(X52,X53)) = k5_relat_1(k4_relat_1(X53),k4_relat_1(X52)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t54_relat_1])])])).

fof(c_0_54,plain,(
    ! [X55] : k4_relat_1(k6_relat_1(X55)) = k6_relat_1(X55) ),
    inference(variable_rename,[status(thm)],[t72_relat_1])).

fof(c_0_55,plain,(
    ! [X48,X49] :
      ( ~ v1_relat_1(X49)
      | k2_relat_1(k7_relat_1(X49,X48)) = k9_relat_1(X49,X48) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).

cnf(c_0_56,plain,
    ( k5_relat_1(X1,k7_relat_1(k6_relat_1(X2),X3)) = k8_relat_1(X2,k8_relat_1(X3,X1))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_35]),c_0_32])]),c_0_45])).

cnf(c_0_57,plain,
    ( k7_relat_1(X1,k1_relat_1(X1)) = X1
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_58,plain,
    ( k1_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_59,plain,
    ( k5_relat_1(k6_relat_1(k1_relat_1(X1)),k7_relat_1(X1,X2)) = k7_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_50])).

cnf(c_0_60,plain,
    ( k5_relat_1(k7_relat_1(k6_relat_1(X1),X2),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_39]),c_0_32])])).

cnf(c_0_61,plain,
    ( v1_relat_1(k7_relat_1(k6_relat_1(X1),X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_45]),c_0_32])])).

cnf(c_0_62,plain,
    ( k4_relat_1(k5_relat_1(X1,X2)) = k5_relat_1(k4_relat_1(X2),k4_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_63,plain,
    ( k4_relat_1(k6_relat_1(X1)) = k6_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_64,plain,
    ( k5_relat_1(k6_relat_1(X1),k8_relat_1(X2,X3)) = k8_relat_1(X2,k7_relat_1(X3,X1))
    | ~ v1_relat_1(X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_36]),c_0_32])])).

cnf(c_0_65,plain,
    ( k2_relat_1(k7_relat_1(X1,X2)) = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_66,plain,
    ( k8_relat_1(X1,k8_relat_1(X1,X2)) = k5_relat_1(X2,k6_relat_1(X1))
    | ~ v1_relat_1(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_58]),c_0_32])])).

cnf(c_0_67,plain,
    ( k8_relat_1(X1,k7_relat_1(k6_relat_1(X2),X1)) = k7_relat_1(k6_relat_1(X1),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_56]),c_0_58]),c_0_45]),c_0_32]),c_0_58]),c_0_32])])).

cnf(c_0_68,plain,
    ( k8_relat_1(X1,k7_relat_1(k6_relat_1(X1),X2)) = k7_relat_1(k6_relat_1(X1),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_60]),c_0_61])])).

cnf(c_0_69,plain,
    ( k4_relat_1(k5_relat_1(k6_relat_1(X1),X2)) = k5_relat_1(k4_relat_1(X2),k6_relat_1(X1))
    | ~ v1_relat_1(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_32])])).

cnf(c_0_70,plain,
    ( k5_relat_1(k6_relat_1(X1),k7_relat_1(k6_relat_1(X2),X3)) = k8_relat_1(X2,k7_relat_1(k6_relat_1(X3),X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_45]),c_0_32])])).

cnf(c_0_71,plain,
    ( k2_relat_1(k5_relat_1(k7_relat_1(X1,X2),X3)) = k9_relat_1(k5_relat_1(X1,X3),X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_51]),c_0_42])).

cnf(c_0_72,plain,
    ( k4_relat_1(k5_relat_1(X1,k6_relat_1(X2))) = k5_relat_1(k6_relat_1(X2),k4_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_32])])).

cnf(c_0_73,plain,
    ( k5_relat_1(k7_relat_1(k6_relat_1(X1),X2),k6_relat_1(X2)) = k7_relat_1(k6_relat_1(X2),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_68]),c_0_61])])).

cnf(c_0_74,plain,
    ( k4_relat_1(k7_relat_1(k6_relat_1(X1),X2)) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_35]),c_0_45]),c_0_63]),c_0_32]),c_0_32])])).

cnf(c_0_75,plain,
    ( k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) = k7_relat_1(k6_relat_1(X2),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_57]),c_0_58]),c_0_68]),c_0_32])])).

fof(c_0_76,negated_conjecture,(
    ~ ! [X1,X2] : k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)) = k6_relat_1(k3_xboole_0(X1,X2)) ),
    inference(assume_negation,[status(cth)],[t43_funct_1])).

fof(c_0_77,plain,(
    ! [X35,X36] : k1_setfam_1(k2_tarski(X35,X36)) = k3_xboole_0(X35,X36) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_78,plain,(
    ! [X8,X9] : k1_enumset1(X8,X8,X9) = k2_tarski(X8,X9) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

cnf(c_0_79,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X1),X2)),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_58]),c_0_32])])).

cnf(c_0_80,plain,
    ( k2_relat_1(k7_relat_1(k6_relat_1(X1),X2)) = k9_relat_1(k6_relat_1(X1),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_60]),c_0_39]),c_0_32])])).

cnf(c_0_81,plain,
    ( k5_relat_1(k7_relat_1(X1,X2),k6_relat_1(X3)) = k7_relat_1(k8_relat_1(X3,X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_35]),c_0_32])])).

cnf(c_0_82,plain,
    ( k7_relat_1(k6_relat_1(X1),X2) = k7_relat_1(k6_relat_1(X2),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_74]),c_0_75]),c_0_74]),c_0_75]),c_0_70]),c_0_67]),c_0_61])])).

cnf(c_0_83,plain,
    ( k5_relat_1(k7_relat_1(k6_relat_1(X1),X2),k6_relat_1(X3)) = k7_relat_1(k7_relat_1(k6_relat_1(X3),X1),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_75]),c_0_32]),c_0_32])])).

cnf(c_0_84,plain,
    ( k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) = k6_relat_1(X2)
    | ~ r1_tarski(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_58]),c_0_32])])).

fof(c_0_85,negated_conjecture,(
    k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0)) != k6_relat_1(k3_xboole_0(esk1_0,esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_76])])])).

cnf(c_0_86,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_77])).

cnf(c_0_87,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_78])).

fof(c_0_88,plain,(
    ! [X10,X11,X12] : k2_enumset1(X10,X10,X11,X12) = k1_enumset1(X10,X11,X12) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_89,plain,(
    ! [X13,X14,X15,X16] : k3_enumset1(X13,X13,X14,X15,X16) = k2_enumset1(X13,X14,X15,X16) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_90,plain,(
    ! [X17,X18,X19,X20,X21] : k4_enumset1(X17,X17,X18,X19,X20,X21) = k3_enumset1(X17,X18,X19,X20,X21) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_91,plain,(
    ! [X22,X23,X24,X25,X26,X27] : k5_enumset1(X22,X22,X23,X24,X25,X26,X27) = k4_enumset1(X22,X23,X24,X25,X26,X27) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_92,plain,(
    ! [X28,X29,X30,X31,X32,X33,X34] : k6_enumset1(X28,X28,X29,X30,X31,X32,X33,X34) = k5_enumset1(X28,X29,X30,X31,X32,X33,X34) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_93,plain,(
    ! [X61,X62] :
      ( ~ v1_relat_1(X62)
      | k1_relat_1(k7_relat_1(X62,X61)) = k3_xboole_0(k1_relat_1(X62),X61) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t90_relat_1])])).

cnf(c_0_94,plain,
    ( k5_relat_1(k7_relat_1(X1,X2),k6_relat_1(k9_relat_1(X1,X2))) = k7_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_65]),c_0_50])).

cnf(c_0_95,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X1) = k7_relat_1(k6_relat_1(X1),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_79]),c_0_61])])).

cnf(c_0_96,plain,
    ( k9_relat_1(k7_relat_1(k6_relat_1(X1),X2),X1) = k9_relat_1(k6_relat_1(X1),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_73]),c_0_80]),c_0_75]),c_0_32]),c_0_32])])).

cnf(c_0_97,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X3) = k7_relat_1(k7_relat_1(k6_relat_1(X1),X3),X2) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_82]),c_0_45]),c_0_32])]),c_0_83])).

cnf(c_0_98,plain,
    ( k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) = k6_relat_1(X1)
    | ~ r1_tarski(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_84]),c_0_63]),c_0_63]),c_0_32])])).

cnf(c_0_99,plain,
    ( k8_relat_1(X1,k7_relat_1(k6_relat_1(X2),X3)) = k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_56]),c_0_45]),c_0_61]),c_0_32])])).

cnf(c_0_100,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(X1,X2)),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_36]),c_0_32])])).

cnf(c_0_101,negated_conjecture,
    ( k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0)) != k6_relat_1(k3_xboole_0(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_85])).

cnf(c_0_102,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_86,c_0_87])).

cnf(c_0_103,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_88])).

cnf(c_0_104,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_89])).

cnf(c_0_105,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_90])).

cnf(c_0_106,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_91])).

cnf(c_0_107,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_92])).

cnf(c_0_108,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = k3_xboole_0(k1_relat_1(X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_93])).

cnf(c_0_109,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),k9_relat_1(k6_relat_1(X1),X2)) = k7_relat_1(k6_relat_1(X1),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_95]),c_0_61])]),c_0_96]),c_0_83]),c_0_82]),c_0_97])).

cnf(c_0_110,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X3) = k7_relat_1(k6_relat_1(X1),X3)
    | ~ r1_tarski(X3,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_98]),c_0_45]),c_0_45]),c_0_32]),c_0_32])]),c_0_70]),c_0_99])).

cnf(c_0_111,plain,
    ( r1_tarski(k9_relat_1(k6_relat_1(X1),X2),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_82]),c_0_80]),c_0_31]),c_0_32])])).

cnf(c_0_112,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X1),X2)),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_60]),c_0_31]),c_0_32]),c_0_61])])).

cnf(c_0_113,negated_conjecture,
    ( k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0)) != k6_relat_1(k1_setfam_1(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_101,c_0_102]),c_0_103]),c_0_104]),c_0_105]),c_0_106]),c_0_107])).

cnf(c_0_114,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = k1_setfam_1(k6_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X2))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_108,c_0_102]),c_0_103]),c_0_104]),c_0_105]),c_0_106]),c_0_107])).

cnf(c_0_115,plain,
    ( k7_relat_1(k6_relat_1(X1),X2) = k6_relat_1(X2)
    | ~ r1_tarski(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_98]),c_0_45]),c_0_32])])).

cnf(c_0_116,plain,
    ( k7_relat_1(k6_relat_1(X1),k9_relat_1(k6_relat_1(X1),X2)) = k7_relat_1(k6_relat_1(X1),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_110]),c_0_111])])).

cnf(c_0_117,plain,
    ( r1_tarski(k9_relat_1(k6_relat_1(X1),X2),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112,c_0_65]),c_0_32])])).

cnf(c_0_118,negated_conjecture,
    ( k6_relat_1(k1_setfam_1(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0))) != k7_relat_1(k6_relat_1(esk1_0),esk2_0) ),
    inference(rw,[status(thm)],[c_0_113,c_0_75])).

cnf(c_0_119,plain,
    ( k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) = k1_relat_1(k7_relat_1(k6_relat_1(X1),X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114,c_0_58]),c_0_32])])).

cnf(c_0_120,plain,
    ( k6_relat_1(k9_relat_1(k6_relat_1(X1),X2)) = k7_relat_1(k6_relat_1(X1),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115,c_0_116]),c_0_117])])).

cnf(c_0_121,negated_conjecture,
    ( k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(esk1_0),esk2_0))) != k7_relat_1(k6_relat_1(esk1_0),esk2_0) ),
    inference(rw,[status(thm)],[c_0_118,c_0_119])).

cnf(c_0_122,plain,
    ( k1_relat_1(k7_relat_1(k6_relat_1(X1),X2)) = k9_relat_1(k6_relat_1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_58,c_0_120])).

cnf(c_0_123,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_121,c_0_122]),c_0_120])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:57:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.42  # AutoSched0-Mode selected heuristic G_E___107_C12_02_nc_F1_PI_AE_Q4_CS_SP_PS_S06DN
% 0.20/0.42  # and selection function SelectNewComplexAHPExceptUniqMaxHorn.
% 0.20/0.42  #
% 0.20/0.42  # Preprocessing time       : 0.028 s
% 0.20/0.42  # Presaturation interreduction done
% 0.20/0.42  
% 0.20/0.42  # Proof found!
% 0.20/0.42  # SZS status Theorem
% 0.20/0.42  # SZS output start CNFRefutation
% 0.20/0.42  fof(t80_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k5_relat_1(X1,k6_relat_1(k2_relat_1(X1)))=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_relat_1)).
% 0.20/0.42  fof(t71_relat_1, axiom, ![X1]:(k1_relat_1(k6_relat_1(X1))=X1&k2_relat_1(k6_relat_1(X1))=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 0.20/0.42  fof(dt_k6_relat_1, axiom, ![X1]:v1_relat_1(k6_relat_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 0.20/0.42  fof(t123_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k8_relat_1(X1,X2)=k5_relat_1(X2,k6_relat_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_relat_1)).
% 0.20/0.42  fof(t94_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k7_relat_1(X2,X1)=k5_relat_1(k6_relat_1(X1),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 0.20/0.42  fof(t45_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>r1_tarski(k2_relat_1(k5_relat_1(X1,X2)),k2_relat_1(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_relat_1)).
% 0.20/0.42  fof(dt_k5_relat_1, axiom, ![X1, X2]:((v1_relat_1(X1)&v1_relat_1(X2))=>v1_relat_1(k5_relat_1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 0.20/0.42  fof(t139_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>k8_relat_1(X1,k5_relat_1(X2,X3))=k5_relat_1(X2,k8_relat_1(X1,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t139_relat_1)).
% 0.20/0.42  fof(t97_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k1_relat_1(X2),X1)=>k7_relat_1(X2,X1)=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_relat_1)).
% 0.20/0.42  fof(t77_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k1_relat_1(X2),X1)=>k5_relat_1(k6_relat_1(X1),X2)=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_relat_1)).
% 0.20/0.42  fof(t89_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k1_relat_1(k7_relat_1(X2,X1)),k1_relat_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t89_relat_1)).
% 0.20/0.42  fof(t112_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>k7_relat_1(k5_relat_1(X2,X3),X1)=k5_relat_1(k7_relat_1(X2,X1),X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t112_relat_1)).
% 0.20/0.42  fof(t54_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>k4_relat_1(k5_relat_1(X1,X2))=k5_relat_1(k4_relat_1(X2),k4_relat_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t54_relat_1)).
% 0.20/0.42  fof(t72_relat_1, axiom, ![X1]:k4_relat_1(k6_relat_1(X1))=k6_relat_1(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_relat_1)).
% 0.20/0.42  fof(t148_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k2_relat_1(k7_relat_1(X2,X1))=k9_relat_1(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 0.20/0.42  fof(t43_funct_1, conjecture, ![X1, X2]:k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))=k6_relat_1(k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_funct_1)).
% 0.20/0.42  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.20/0.42  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.20/0.42  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.20/0.42  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.20/0.42  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 0.20/0.42  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 0.20/0.42  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 0.20/0.42  fof(t90_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k1_relat_1(k7_relat_1(X2,X1))=k3_xboole_0(k1_relat_1(X2),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_relat_1)).
% 0.20/0.42  fof(c_0_24, plain, ![X58]:(~v1_relat_1(X58)|k5_relat_1(X58,k6_relat_1(k2_relat_1(X58)))=X58), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t80_relat_1])])).
% 0.20/0.42  fof(c_0_25, plain, ![X54]:(k1_relat_1(k6_relat_1(X54))=X54&k2_relat_1(k6_relat_1(X54))=X54), inference(variable_rename,[status(thm)],[t71_relat_1])).
% 0.20/0.42  fof(c_0_26, plain, ![X39]:v1_relat_1(k6_relat_1(X39)), inference(variable_rename,[status(thm)],[dt_k6_relat_1])).
% 0.20/0.42  fof(c_0_27, plain, ![X43, X44]:(~v1_relat_1(X44)|k8_relat_1(X43,X44)=k5_relat_1(X44,k6_relat_1(X43))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t123_relat_1])])).
% 0.20/0.42  fof(c_0_28, plain, ![X63, X64]:(~v1_relat_1(X64)|k7_relat_1(X64,X63)=k5_relat_1(k6_relat_1(X63),X64)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).
% 0.20/0.42  fof(c_0_29, plain, ![X50, X51]:(~v1_relat_1(X50)|(~v1_relat_1(X51)|r1_tarski(k2_relat_1(k5_relat_1(X50,X51)),k2_relat_1(X51)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t45_relat_1])])])).
% 0.20/0.42  cnf(c_0_30, plain, (k5_relat_1(X1,k6_relat_1(k2_relat_1(X1)))=X1|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.42  cnf(c_0_31, plain, (k2_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.42  cnf(c_0_32, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.42  fof(c_0_33, plain, ![X37, X38]:(~v1_relat_1(X37)|~v1_relat_1(X38)|v1_relat_1(k5_relat_1(X37,X38))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_relat_1])])).
% 0.20/0.42  fof(c_0_34, plain, ![X45, X46, X47]:(~v1_relat_1(X46)|(~v1_relat_1(X47)|k8_relat_1(X45,k5_relat_1(X46,X47))=k5_relat_1(X46,k8_relat_1(X45,X47)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t139_relat_1])])])).
% 0.20/0.42  cnf(c_0_35, plain, (k8_relat_1(X2,X1)=k5_relat_1(X1,k6_relat_1(X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.42  cnf(c_0_36, plain, (k7_relat_1(X1,X2)=k5_relat_1(k6_relat_1(X2),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.42  fof(c_0_37, plain, ![X65, X66]:(~v1_relat_1(X66)|(~r1_tarski(k1_relat_1(X66),X65)|k7_relat_1(X66,X65)=X66)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t97_relat_1])])).
% 0.20/0.42  cnf(c_0_38, plain, (r1_tarski(k2_relat_1(k5_relat_1(X1,X2)),k2_relat_1(X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.20/0.42  cnf(c_0_39, plain, (k5_relat_1(k6_relat_1(X1),k6_relat_1(X1))=k6_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32])])).
% 0.20/0.42  fof(c_0_40, plain, ![X56, X57]:(~v1_relat_1(X57)|(~r1_tarski(k1_relat_1(X57),X56)|k5_relat_1(k6_relat_1(X56),X57)=X57)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t77_relat_1])])).
% 0.20/0.42  fof(c_0_41, plain, ![X59, X60]:(~v1_relat_1(X60)|r1_tarski(k1_relat_1(k7_relat_1(X60,X59)),k1_relat_1(X60))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t89_relat_1])])).
% 0.20/0.42  cnf(c_0_42, plain, (v1_relat_1(k5_relat_1(X1,X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.20/0.42  fof(c_0_43, plain, ![X40, X41, X42]:(~v1_relat_1(X41)|(~v1_relat_1(X42)|k7_relat_1(k5_relat_1(X41,X42),X40)=k5_relat_1(k7_relat_1(X41,X40),X42))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t112_relat_1])])])).
% 0.20/0.42  cnf(c_0_44, plain, (k8_relat_1(X3,k5_relat_1(X1,X2))=k5_relat_1(X1,k8_relat_1(X3,X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.20/0.42  cnf(c_0_45, plain, (k8_relat_1(X1,k6_relat_1(X2))=k7_relat_1(k6_relat_1(X1),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_32]), c_0_32])])).
% 0.20/0.42  cnf(c_0_46, plain, (k7_relat_1(X1,X2)=X1|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.20/0.42  cnf(c_0_47, plain, (r1_tarski(X1,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_31]), c_0_31]), c_0_32])])).
% 0.20/0.42  cnf(c_0_48, plain, (k5_relat_1(k6_relat_1(X2),X1)=X1|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.20/0.42  cnf(c_0_49, plain, (r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),k1_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.20/0.42  cnf(c_0_50, plain, (v1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_36]), c_0_32])])).
% 0.20/0.42  cnf(c_0_51, plain, (k7_relat_1(k5_relat_1(X1,X2),X3)=k5_relat_1(k7_relat_1(X1,X3),X2)|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.20/0.42  cnf(c_0_52, plain, (v1_relat_1(k8_relat_1(X1,X2))|~v1_relat_1(X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_35]), c_0_32])])).
% 0.20/0.42  fof(c_0_53, plain, ![X52, X53]:(~v1_relat_1(X52)|(~v1_relat_1(X53)|k4_relat_1(k5_relat_1(X52,X53))=k5_relat_1(k4_relat_1(X53),k4_relat_1(X52)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t54_relat_1])])])).
% 0.20/0.42  fof(c_0_54, plain, ![X55]:k4_relat_1(k6_relat_1(X55))=k6_relat_1(X55), inference(variable_rename,[status(thm)],[t72_relat_1])).
% 0.20/0.42  fof(c_0_55, plain, ![X48, X49]:(~v1_relat_1(X49)|k2_relat_1(k7_relat_1(X49,X48))=k9_relat_1(X49,X48)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).
% 0.20/0.42  cnf(c_0_56, plain, (k5_relat_1(X1,k7_relat_1(k6_relat_1(X2),X3))=k8_relat_1(X2,k8_relat_1(X3,X1))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_35]), c_0_32])]), c_0_45])).
% 0.20/0.42  cnf(c_0_57, plain, (k7_relat_1(X1,k1_relat_1(X1))=X1|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.20/0.42  cnf(c_0_58, plain, (k1_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.42  cnf(c_0_59, plain, (k5_relat_1(k6_relat_1(k1_relat_1(X1)),k7_relat_1(X1,X2))=k7_relat_1(X1,X2)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_50])).
% 0.20/0.42  cnf(c_0_60, plain, (k5_relat_1(k7_relat_1(k6_relat_1(X1),X2),k6_relat_1(X1))=k7_relat_1(k6_relat_1(X1),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_39]), c_0_32])])).
% 0.20/0.42  cnf(c_0_61, plain, (v1_relat_1(k7_relat_1(k6_relat_1(X1),X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_45]), c_0_32])])).
% 0.20/0.42  cnf(c_0_62, plain, (k4_relat_1(k5_relat_1(X1,X2))=k5_relat_1(k4_relat_1(X2),k4_relat_1(X1))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.20/0.42  cnf(c_0_63, plain, (k4_relat_1(k6_relat_1(X1))=k6_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.20/0.42  cnf(c_0_64, plain, (k5_relat_1(k6_relat_1(X1),k8_relat_1(X2,X3))=k8_relat_1(X2,k7_relat_1(X3,X1))|~v1_relat_1(X3)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_36]), c_0_32])])).
% 0.20/0.42  cnf(c_0_65, plain, (k2_relat_1(k7_relat_1(X1,X2))=k9_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.20/0.42  cnf(c_0_66, plain, (k8_relat_1(X1,k8_relat_1(X1,X2))=k5_relat_1(X2,k6_relat_1(X1))|~v1_relat_1(X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_58]), c_0_32])])).
% 0.20/0.42  cnf(c_0_67, plain, (k8_relat_1(X1,k7_relat_1(k6_relat_1(X2),X1))=k7_relat_1(k6_relat_1(X1),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_56]), c_0_58]), c_0_45]), c_0_32]), c_0_58]), c_0_32])])).
% 0.20/0.42  cnf(c_0_68, plain, (k8_relat_1(X1,k7_relat_1(k6_relat_1(X1),X2))=k7_relat_1(k6_relat_1(X1),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_60]), c_0_61])])).
% 0.20/0.42  cnf(c_0_69, plain, (k4_relat_1(k5_relat_1(k6_relat_1(X1),X2))=k5_relat_1(k4_relat_1(X2),k6_relat_1(X1))|~v1_relat_1(X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_32])])).
% 0.20/0.42  cnf(c_0_70, plain, (k5_relat_1(k6_relat_1(X1),k7_relat_1(k6_relat_1(X2),X3))=k8_relat_1(X2,k7_relat_1(k6_relat_1(X3),X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_45]), c_0_32])])).
% 0.20/0.42  cnf(c_0_71, plain, (k2_relat_1(k5_relat_1(k7_relat_1(X1,X2),X3))=k9_relat_1(k5_relat_1(X1,X3),X2)|~v1_relat_1(X3)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_51]), c_0_42])).
% 0.20/0.42  cnf(c_0_72, plain, (k4_relat_1(k5_relat_1(X1,k6_relat_1(X2)))=k5_relat_1(k6_relat_1(X2),k4_relat_1(X1))|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_32])])).
% 0.20/0.42  cnf(c_0_73, plain, (k5_relat_1(k7_relat_1(k6_relat_1(X1),X2),k6_relat_1(X2))=k7_relat_1(k6_relat_1(X2),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_68]), c_0_61])])).
% 0.20/0.42  cnf(c_0_74, plain, (k4_relat_1(k7_relat_1(k6_relat_1(X1),X2))=k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_35]), c_0_45]), c_0_63]), c_0_32]), c_0_32])])).
% 0.20/0.42  cnf(c_0_75, plain, (k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))=k7_relat_1(k6_relat_1(X2),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_57]), c_0_58]), c_0_68]), c_0_32])])).
% 0.20/0.42  fof(c_0_76, negated_conjecture, ~(![X1, X2]:k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))=k6_relat_1(k3_xboole_0(X1,X2))), inference(assume_negation,[status(cth)],[t43_funct_1])).
% 0.20/0.42  fof(c_0_77, plain, ![X35, X36]:k1_setfam_1(k2_tarski(X35,X36))=k3_xboole_0(X35,X36), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.20/0.42  fof(c_0_78, plain, ![X8, X9]:k1_enumset1(X8,X8,X9)=k2_tarski(X8,X9), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.20/0.42  cnf(c_0_79, plain, (r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X1),X2)),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_58]), c_0_32])])).
% 0.20/0.42  cnf(c_0_80, plain, (k2_relat_1(k7_relat_1(k6_relat_1(X1),X2))=k9_relat_1(k6_relat_1(X1),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_60]), c_0_39]), c_0_32])])).
% 0.20/0.42  cnf(c_0_81, plain, (k5_relat_1(k7_relat_1(X1,X2),k6_relat_1(X3))=k7_relat_1(k8_relat_1(X3,X1),X2)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_35]), c_0_32])])).
% 0.20/0.42  cnf(c_0_82, plain, (k7_relat_1(k6_relat_1(X1),X2)=k7_relat_1(k6_relat_1(X2),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_73]), c_0_74]), c_0_75]), c_0_74]), c_0_75]), c_0_70]), c_0_67]), c_0_61])])).
% 0.20/0.42  cnf(c_0_83, plain, (k5_relat_1(k7_relat_1(k6_relat_1(X1),X2),k6_relat_1(X3))=k7_relat_1(k7_relat_1(k6_relat_1(X3),X1),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_75]), c_0_32]), c_0_32])])).
% 0.20/0.42  cnf(c_0_84, plain, (k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))=k6_relat_1(X2)|~r1_tarski(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_58]), c_0_32])])).
% 0.20/0.42  fof(c_0_85, negated_conjecture, k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0))!=k6_relat_1(k3_xboole_0(esk1_0,esk2_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_76])])])).
% 0.20/0.42  cnf(c_0_86, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_77])).
% 0.20/0.42  cnf(c_0_87, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_78])).
% 0.20/0.42  fof(c_0_88, plain, ![X10, X11, X12]:k2_enumset1(X10,X10,X11,X12)=k1_enumset1(X10,X11,X12), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.20/0.42  fof(c_0_89, plain, ![X13, X14, X15, X16]:k3_enumset1(X13,X13,X14,X15,X16)=k2_enumset1(X13,X14,X15,X16), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.20/0.42  fof(c_0_90, plain, ![X17, X18, X19, X20, X21]:k4_enumset1(X17,X17,X18,X19,X20,X21)=k3_enumset1(X17,X18,X19,X20,X21), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.20/0.42  fof(c_0_91, plain, ![X22, X23, X24, X25, X26, X27]:k5_enumset1(X22,X22,X23,X24,X25,X26,X27)=k4_enumset1(X22,X23,X24,X25,X26,X27), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.20/0.42  fof(c_0_92, plain, ![X28, X29, X30, X31, X32, X33, X34]:k6_enumset1(X28,X28,X29,X30,X31,X32,X33,X34)=k5_enumset1(X28,X29,X30,X31,X32,X33,X34), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.20/0.42  fof(c_0_93, plain, ![X61, X62]:(~v1_relat_1(X62)|k1_relat_1(k7_relat_1(X62,X61))=k3_xboole_0(k1_relat_1(X62),X61)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t90_relat_1])])).
% 0.20/0.42  cnf(c_0_94, plain, (k5_relat_1(k7_relat_1(X1,X2),k6_relat_1(k9_relat_1(X1,X2)))=k7_relat_1(X1,X2)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_65]), c_0_50])).
% 0.20/0.42  cnf(c_0_95, plain, (k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X1)=k7_relat_1(k6_relat_1(X1),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_79]), c_0_61])])).
% 0.20/0.42  cnf(c_0_96, plain, (k9_relat_1(k7_relat_1(k6_relat_1(X1),X2),X1)=k9_relat_1(k6_relat_1(X1),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_73]), c_0_80]), c_0_75]), c_0_32]), c_0_32])])).
% 0.20/0.42  cnf(c_0_97, plain, (k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X3)=k7_relat_1(k7_relat_1(k6_relat_1(X1),X3),X2)), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_82]), c_0_45]), c_0_32])]), c_0_83])).
% 0.20/0.42  cnf(c_0_98, plain, (k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))=k6_relat_1(X1)|~r1_tarski(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_84]), c_0_63]), c_0_63]), c_0_32])])).
% 0.20/0.42  cnf(c_0_99, plain, (k8_relat_1(X1,k7_relat_1(k6_relat_1(X2),X3))=k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X3)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_56]), c_0_45]), c_0_61]), c_0_32])])).
% 0.20/0.42  cnf(c_0_100, plain, (r1_tarski(k2_relat_1(k7_relat_1(X1,X2)),k2_relat_1(X1))|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_36]), c_0_32])])).
% 0.20/0.42  cnf(c_0_101, negated_conjecture, (k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0))!=k6_relat_1(k3_xboole_0(esk1_0,esk2_0))), inference(split_conjunct,[status(thm)],[c_0_85])).
% 0.20/0.42  cnf(c_0_102, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_86, c_0_87])).
% 0.20/0.42  cnf(c_0_103, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_88])).
% 0.20/0.42  cnf(c_0_104, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_89])).
% 0.20/0.42  cnf(c_0_105, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_90])).
% 0.20/0.42  cnf(c_0_106, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_91])).
% 0.20/0.42  cnf(c_0_107, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_92])).
% 0.20/0.42  cnf(c_0_108, plain, (k1_relat_1(k7_relat_1(X1,X2))=k3_xboole_0(k1_relat_1(X1),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_93])).
% 0.20/0.42  cnf(c_0_109, plain, (k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),k9_relat_1(k6_relat_1(X1),X2))=k7_relat_1(k6_relat_1(X1),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_95]), c_0_61])]), c_0_96]), c_0_83]), c_0_82]), c_0_97])).
% 0.20/0.42  cnf(c_0_110, plain, (k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X3)=k7_relat_1(k6_relat_1(X1),X3)|~r1_tarski(X3,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_98]), c_0_45]), c_0_45]), c_0_32]), c_0_32])]), c_0_70]), c_0_99])).
% 0.20/0.42  cnf(c_0_111, plain, (r1_tarski(k9_relat_1(k6_relat_1(X1),X2),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_82]), c_0_80]), c_0_31]), c_0_32])])).
% 0.20/0.42  cnf(c_0_112, plain, (r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X1),X2)),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_60]), c_0_31]), c_0_32]), c_0_61])])).
% 0.20/0.42  cnf(c_0_113, negated_conjecture, (k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0))!=k6_relat_1(k1_setfam_1(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_101, c_0_102]), c_0_103]), c_0_104]), c_0_105]), c_0_106]), c_0_107])).
% 0.20/0.42  cnf(c_0_114, plain, (k1_relat_1(k7_relat_1(X1,X2))=k1_setfam_1(k6_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X2))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_108, c_0_102]), c_0_103]), c_0_104]), c_0_105]), c_0_106]), c_0_107])).
% 0.20/0.42  cnf(c_0_115, plain, (k7_relat_1(k6_relat_1(X1),X2)=k6_relat_1(X2)|~r1_tarski(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_98]), c_0_45]), c_0_32])])).
% 0.20/0.42  cnf(c_0_116, plain, (k7_relat_1(k6_relat_1(X1),k9_relat_1(k6_relat_1(X1),X2))=k7_relat_1(k6_relat_1(X1),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109, c_0_110]), c_0_111])])).
% 0.20/0.42  cnf(c_0_117, plain, (r1_tarski(k9_relat_1(k6_relat_1(X1),X2),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112, c_0_65]), c_0_32])])).
% 0.20/0.42  cnf(c_0_118, negated_conjecture, (k6_relat_1(k1_setfam_1(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0)))!=k7_relat_1(k6_relat_1(esk1_0),esk2_0)), inference(rw,[status(thm)],[c_0_113, c_0_75])).
% 0.20/0.42  cnf(c_0_119, plain, (k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))=k1_relat_1(k7_relat_1(k6_relat_1(X1),X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114, c_0_58]), c_0_32])])).
% 0.20/0.42  cnf(c_0_120, plain, (k6_relat_1(k9_relat_1(k6_relat_1(X1),X2))=k7_relat_1(k6_relat_1(X1),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115, c_0_116]), c_0_117])])).
% 0.20/0.42  cnf(c_0_121, negated_conjecture, (k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(esk1_0),esk2_0)))!=k7_relat_1(k6_relat_1(esk1_0),esk2_0)), inference(rw,[status(thm)],[c_0_118, c_0_119])).
% 0.20/0.42  cnf(c_0_122, plain, (k1_relat_1(k7_relat_1(k6_relat_1(X1),X2))=k9_relat_1(k6_relat_1(X1),X2)), inference(spm,[status(thm)],[c_0_58, c_0_120])).
% 0.20/0.42  cnf(c_0_123, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_121, c_0_122]), c_0_120])]), ['proof']).
% 0.20/0.42  # SZS output end CNFRefutation
% 0.20/0.42  # Proof object total steps             : 124
% 0.20/0.42  # Proof object clause steps            : 75
% 0.20/0.42  # Proof object formula steps           : 49
% 0.20/0.42  # Proof object conjectures             : 8
% 0.20/0.42  # Proof object clause conjectures      : 5
% 0.20/0.42  # Proof object formula conjectures     : 3
% 0.20/0.42  # Proof object initial clauses used    : 25
% 0.20/0.42  # Proof object initial formulas used   : 24
% 0.20/0.42  # Proof object generating inferences   : 44
% 0.20/0.42  # Proof object simplifying inferences  : 145
% 0.20/0.42  # Training examples: 0 positive, 0 negative
% 0.20/0.42  # Parsed axioms                        : 24
% 0.20/0.42  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.42  # Initial clauses                      : 25
% 0.20/0.42  # Removed in clause preprocessing      : 7
% 0.20/0.42  # Initial clauses in saturation        : 18
% 0.20/0.42  # Processed clauses                    : 564
% 0.20/0.42  # ...of these trivial                  : 44
% 0.20/0.42  # ...subsumed                          : 313
% 0.20/0.42  # ...remaining for further processing  : 207
% 0.20/0.42  # Other redundant clauses eliminated   : 0
% 0.20/0.42  # Clauses deleted for lack of memory   : 0
% 0.20/0.42  # Backward-subsumed                    : 0
% 0.20/0.42  # Backward-rewritten                   : 31
% 0.20/0.42  # Generated clauses                    : 3843
% 0.20/0.42  # ...of the previous two non-trivial   : 2639
% 0.20/0.42  # Contextual simplify-reflections      : 26
% 0.20/0.42  # Paramodulations                      : 3843
% 0.20/0.42  # Factorizations                       : 0
% 0.20/0.42  # Equation resolutions                 : 0
% 0.20/0.42  # Propositional unsat checks           : 0
% 0.20/0.42  #    Propositional check models        : 0
% 0.20/0.42  #    Propositional check unsatisfiable : 0
% 0.20/0.42  #    Propositional clauses             : 0
% 0.20/0.42  #    Propositional clauses after purity: 0
% 0.20/0.42  #    Propositional unsat core size     : 0
% 0.20/0.42  #    Propositional preprocessing time  : 0.000
% 0.20/0.42  #    Propositional encoding time       : 0.000
% 0.20/0.42  #    Propositional solver time         : 0.000
% 0.20/0.42  #    Success case prop preproc time    : 0.000
% 0.20/0.42  #    Success case prop encoding time   : 0.000
% 0.20/0.42  #    Success case prop solver time     : 0.000
% 0.20/0.42  # Current number of processed clauses  : 158
% 0.20/0.42  #    Positive orientable unit clauses  : 42
% 0.20/0.42  #    Positive unorientable unit clauses: 3
% 0.20/0.42  #    Negative unit clauses             : 2
% 0.20/0.42  #    Non-unit-clauses                  : 111
% 0.20/0.42  # Current number of unprocessed clauses: 2090
% 0.20/0.42  # ...number of literals in the above   : 5273
% 0.20/0.42  # Current number of archived formulas  : 0
% 0.20/0.42  # Current number of archived clauses   : 56
% 0.20/0.42  # Clause-clause subsumption calls (NU) : 2040
% 0.20/0.42  # Rec. Clause-clause subsumption calls : 1852
% 0.20/0.42  # Non-unit clause-clause subsumptions  : 299
% 0.20/0.42  # Unit Clause-clause subsumption calls : 45
% 0.20/0.42  # Rewrite failures with RHS unbound    : 0
% 0.20/0.42  # BW rewrite match attempts            : 108
% 0.20/0.42  # BW rewrite match successes           : 50
% 0.20/0.42  # Condensation attempts                : 0
% 0.20/0.42  # Condensation successes               : 0
% 0.20/0.42  # Termbank termtop insertions          : 49617
% 0.20/0.42  
% 0.20/0.42  # -------------------------------------------------
% 0.20/0.42  # User time                : 0.076 s
% 0.20/0.42  # System time              : 0.009 s
% 0.20/0.42  # Total time               : 0.084 s
% 0.20/0.42  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
