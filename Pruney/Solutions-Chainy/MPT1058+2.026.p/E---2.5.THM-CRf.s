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
% DateTime   : Thu Dec  3 11:07:29 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  155 (1229 expanded)
%              Number of clauses        :   94 ( 506 expanded)
%              Number of leaves         :   30 ( 360 expanded)
%              Depth                    :   14
%              Number of atoms          :  227 (1488 expanded)
%              Number of equality atoms :  114 (1169 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :    7 (   1 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t43_funct_1,axiom,(
    ! [X1,X2] : k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)) = k6_relat_1(k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(t75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(t79_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t16_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

fof(t71_relat_1,axiom,(
    ! [X1] :
      ( k1_relat_1(k6_relat_1(X1)) = X1
      & k2_relat_1(k6_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(t182_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k1_relat_1(k5_relat_1(X1,X2)) = k10_relat_1(X1,k1_relat_1(X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

fof(fc3_funct_1,axiom,(
    ! [X1] :
      ( v1_relat_1(k6_relat_1(X1))
      & v1_funct_1(k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(t175_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => k10_relat_1(X3,k2_xboole_0(X1,X2)) = k2_xboole_0(k10_relat_1(X3,X1),k10_relat_1(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_relat_1)).

fof(t169_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,k2_relat_1(X1)) = k1_relat_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(t139_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => k10_relat_1(k7_relat_1(X3,X1),X2) = k3_xboole_0(X1,k10_relat_1(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).

fof(t175_funct_2,conjecture,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2,X3] :
          ( r1_tarski(k10_relat_1(X1,X3),X2)
         => k10_relat_1(X1,X3) = k10_relat_1(k7_relat_1(X1,X2),X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_funct_2)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(c_0_30,plain,(
    ! [X79,X80] : k1_setfam_1(k2_tarski(X79,X80)) = k3_xboole_0(X79,X80) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_31,plain,(
    ! [X52,X53] : k1_enumset1(X52,X52,X53) = k2_tarski(X52,X53) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_32,plain,(
    ! [X25,X26] : k4_xboole_0(X25,X26) = k5_xboole_0(X25,k3_xboole_0(X25,X26)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_33,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_34,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_35,plain,(
    ! [X92,X93] : k5_relat_1(k6_relat_1(X93),k6_relat_1(X92)) = k6_relat_1(k3_xboole_0(X92,X93)) ),
    inference(variable_rename,[status(thm)],[t43_funct_1])).

fof(c_0_36,plain,(
    ! [X54,X55,X56] : k2_enumset1(X54,X54,X55,X56) = k1_enumset1(X54,X55,X56) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_37,plain,(
    ! [X57,X58,X59,X60] : k3_enumset1(X57,X57,X58,X59,X60) = k2_enumset1(X57,X58,X59,X60) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_38,plain,(
    ! [X61,X62,X63,X64,X65] : k4_enumset1(X61,X61,X62,X63,X64,X65) = k3_enumset1(X61,X62,X63,X64,X65) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_39,plain,(
    ! [X66,X67,X68,X69,X70,X71] : k5_enumset1(X66,X66,X67,X68,X69,X70,X71) = k4_enumset1(X66,X67,X68,X69,X70,X71) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_40,plain,(
    ! [X72,X73,X74,X75,X76,X77,X78] : k6_enumset1(X72,X72,X73,X74,X75,X76,X77,X78) = k5_enumset1(X72,X73,X74,X75,X76,X77,X78) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_41,plain,(
    ! [X17,X18,X20,X21,X22] :
      ( ( r1_xboole_0(X17,X18)
        | r2_hidden(esk2_2(X17,X18),k3_xboole_0(X17,X18)) )
      & ( ~ r2_hidden(X22,k3_xboole_0(X20,X21))
        | ~ r1_xboole_0(X20,X21) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

fof(c_0_42,plain,(
    ! [X45,X46] : r1_xboole_0(k4_xboole_0(X45,X46),X46) ),
    inference(variable_rename,[status(thm)],[t79_xboole_1])).

cnf(c_0_43,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_44,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_33,c_0_34])).

fof(c_0_45,plain,(
    ! [X34,X35] :
      ( ~ r1_tarski(X34,X35)
      | k3_xboole_0(X34,X35) = X34 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

fof(c_0_46,plain,(
    ! [X38,X39] : r1_tarski(k4_xboole_0(X38,X39),X38) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

fof(c_0_47,plain,(
    ! [X29,X30,X31] : k3_xboole_0(k3_xboole_0(X29,X30),X31) = k3_xboole_0(X29,k3_xboole_0(X30,X31)) ),
    inference(variable_rename,[status(thm)],[t16_xboole_1])).

fof(c_0_48,plain,(
    ! [X87] :
      ( k1_relat_1(k6_relat_1(X87)) = X87
      & k2_relat_1(k6_relat_1(X87)) = X87 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

cnf(c_0_49,plain,
    ( k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) = k6_relat_1(k3_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_50,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_51,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_52,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_53,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_54,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

fof(c_0_55,plain,(
    ! [X85,X86] :
      ( ~ v1_relat_1(X85)
      | ~ v1_relat_1(X86)
      | k1_relat_1(k5_relat_1(X85,X86)) = k10_relat_1(X85,k1_relat_1(X86)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t182_relat_1])])])).

fof(c_0_56,plain,(
    ! [X88] :
      ( v1_relat_1(k6_relat_1(X88))
      & v1_funct_1(k6_relat_1(X88)) ) ),
    inference(variable_rename,[status(thm)],[fc3_funct_1])).

fof(c_0_57,plain,(
    ! [X32,X33] : r1_tarski(k3_xboole_0(X32,X33),X32) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

cnf(c_0_58,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_59,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_60,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2))) ),
    inference(rw,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_61,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_62,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_63,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk2_2(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_64,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_65,plain,
    ( k2_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_66,plain,
    ( k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) = k6_relat_1(k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_44]),c_0_50]),c_0_51]),c_0_52]),c_0_53]),c_0_54])).

cnf(c_0_67,plain,
    ( k1_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_68,plain,
    ( k1_relat_1(k5_relat_1(X1,X2)) = k10_relat_1(X1,k1_relat_1(X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_69,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_70,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_71,plain,
    ( ~ r1_xboole_0(X2,X3)
    | ~ r2_hidden(X1,k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58,c_0_44]),c_0_50]),c_0_51]),c_0_52]),c_0_53]),c_0_54])).

cnf(c_0_72,plain,
    ( r1_xboole_0(k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59,c_0_60]),c_0_50]),c_0_51]),c_0_52]),c_0_53]),c_0_54])).

cnf(c_0_73,plain,
    ( k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_44]),c_0_50]),c_0_51]),c_0_52]),c_0_53]),c_0_54])).

cnf(c_0_74,plain,
    ( r1_tarski(k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_62,c_0_60]),c_0_50]),c_0_51]),c_0_52]),c_0_53]),c_0_54])).

fof(c_0_75,plain,(
    ! [X16] : k3_xboole_0(X16,X16) = X16 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

cnf(c_0_76,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk2_2(X1,X2),k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_63,c_0_44]),c_0_50]),c_0_51]),c_0_52]),c_0_53]),c_0_54])).

fof(c_0_77,plain,(
    ! [X10,X11,X12,X13,X14] :
      ( ( ~ r1_tarski(X10,X11)
        | ~ r2_hidden(X12,X10)
        | r2_hidden(X12,X11) )
      & ( r2_hidden(esk1_2(X13,X14),X13)
        | r1_tarski(X13,X14) )
      & ( ~ r2_hidden(esk1_2(X13,X14),X14)
        | r1_tarski(X13,X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_78,plain,(
    ! [X47,X48] : r1_tarski(X47,k2_xboole_0(X47,X48)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

fof(c_0_79,plain,(
    ! [X40,X41] : k2_xboole_0(X40,k4_xboole_0(X41,X40)) = k2_xboole_0(X40,X41) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

cnf(c_0_80,plain,
    ( k1_setfam_1(k6_enumset1(k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),X3)) = k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_64,c_0_44]),c_0_44]),c_0_44]),c_0_44]),c_0_50]),c_0_50]),c_0_50]),c_0_50]),c_0_50]),c_0_51]),c_0_51]),c_0_51]),c_0_51]),c_0_51]),c_0_51]),c_0_52]),c_0_52]),c_0_52]),c_0_52]),c_0_52]),c_0_52]),c_0_52]),c_0_53]),c_0_53]),c_0_53]),c_0_53]),c_0_53]),c_0_53]),c_0_53]),c_0_53]),c_0_54]),c_0_54]),c_0_54]),c_0_54]),c_0_54]),c_0_54]),c_0_54]),c_0_54]),c_0_54])).

cnf(c_0_81,plain,
    ( k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) = k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1)) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_82,plain,
    ( k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) = k1_relat_1(k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))) ),
    inference(spm,[status(thm)],[c_0_67,c_0_66])).

cnf(c_0_83,plain,
    ( k1_relat_1(k5_relat_1(k6_relat_1(X1),X2)) = k10_relat_1(k6_relat_1(X1),k1_relat_1(X2))
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_84,plain,
    ( r1_tarski(k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_70,c_0_44]),c_0_50]),c_0_51]),c_0_52]),c_0_53]),c_0_54])).

cnf(c_0_85,plain,
    ( ~ r2_hidden(X1,k1_setfam_1(k6_enumset1(k5_xboole_0(X2,k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3))),k5_xboole_0(X2,k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3))),k5_xboole_0(X2,k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3))),k5_xboole_0(X2,k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3))),k5_xboole_0(X2,k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3))),k5_xboole_0(X2,k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3))),k5_xboole_0(X2,k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3))),X3))) ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_86,plain,
    ( k1_setfam_1(k6_enumset1(k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))),k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))),k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))),k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))),k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))),k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))),k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))),X1)) = k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) ),
    inference(spm,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_87,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_88,plain,
    ( r2_hidden(esk2_2(X1,X2),k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))
    | ~ r2_hidden(X3,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) ),
    inference(spm,[status(thm)],[c_0_71,c_0_76])).

cnf(c_0_89,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_77])).

cnf(c_0_90,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_78])).

fof(c_0_91,plain,(
    ! [X82,X83,X84] :
      ( ~ v1_relat_1(X84)
      | k10_relat_1(X84,k2_xboole_0(X82,X83)) = k2_xboole_0(k10_relat_1(X84,X82),k10_relat_1(X84,X83)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t175_relat_1])])).

cnf(c_0_92,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_79])).

fof(c_0_93,plain,(
    ! [X81] :
      ( ~ v1_relat_1(X81)
      | k10_relat_1(X81,k2_relat_1(X81)) = k1_relat_1(X81) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t169_relat_1])])).

cnf(c_0_94,plain,
    ( k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)))) = k2_relat_1(k5_relat_1(k6_relat_1(X3),k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_80,c_0_81]),c_0_66])).

cnf(c_0_95,plain,
    ( k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) ),
    inference(rw,[status(thm)],[c_0_66,c_0_82])).

cnf(c_0_96,plain,
    ( k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) = k10_relat_1(k6_relat_1(X1),X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_69]),c_0_67])).

cnf(c_0_97,plain,
    ( k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) = X2
    | ~ r1_tarski(X2,X1) ),
    inference(rw,[status(thm)],[c_0_73,c_0_82])).

cnf(c_0_98,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))),X2) ),
    inference(rw,[status(thm)],[c_0_84,c_0_82])).

fof(c_0_99,plain,(
    ! [X23,X24] :
      ( ( r1_tarski(X23,X24)
        | X23 != X24 )
      & ( r1_tarski(X24,X23)
        | X23 != X24 )
      & ( ~ r1_tarski(X23,X24)
        | ~ r1_tarski(X24,X23)
        | X23 = X24 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_100,plain,(
    ! [X37] : r1_tarski(k1_xboole_0,X37) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_101,plain,
    ( ~ r2_hidden(X1,k2_relat_1(k5_relat_1(k6_relat_1(X2),k6_relat_1(k5_xboole_0(X3,k1_setfam_1(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X2))))))) ),
    inference(rw,[status(thm)],[c_0_85,c_0_81])).

cnf(c_0_102,plain,
    ( k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))))) = k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) ),
    inference(rw,[status(thm)],[c_0_86,c_0_81])).

cnf(c_0_103,plain,
    ( k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_87,c_0_44]),c_0_50]),c_0_51]),c_0_52]),c_0_53]),c_0_54])).

cnf(c_0_104,plain,
    ( r2_hidden(esk2_2(X1,X2),k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))
    | r1_tarski(k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),X3) ),
    inference(spm,[status(thm)],[c_0_88,c_0_89])).

cnf(c_0_105,plain,
    ( k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k2_xboole_0(X1,X2))) = X1 ),
    inference(spm,[status(thm)],[c_0_73,c_0_90])).

fof(c_0_106,plain,(
    ! [X27,X28] :
      ( ~ r1_tarski(X27,X28)
      | k2_xboole_0(X27,X28) = X28 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

fof(c_0_107,plain,(
    ! [X89,X90,X91] :
      ( ~ v1_relat_1(X91)
      | k10_relat_1(k7_relat_1(X91,X89),X90) = k3_xboole_0(X89,k10_relat_1(X91,X90)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t139_funct_1])])).

fof(c_0_108,negated_conjecture,(
    ~ ! [X1] :
        ( ( v1_relat_1(X1)
          & v1_funct_1(X1) )
       => ! [X2,X3] :
            ( r1_tarski(k10_relat_1(X1,X3),X2)
           => k10_relat_1(X1,X3) = k10_relat_1(k7_relat_1(X1,X2),X3) ) ) ),
    inference(assume_negation,[status(cth)],[t175_funct_2])).

cnf(c_0_109,plain,
    ( k10_relat_1(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(k10_relat_1(X1,X2),k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_91])).

cnf(c_0_110,plain,
    ( k2_xboole_0(X1,k5_xboole_0(X2,k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1)))) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_92,c_0_60]),c_0_50]),c_0_51]),c_0_52]),c_0_53]),c_0_54])).

cnf(c_0_111,plain,
    ( k10_relat_1(X1,k2_relat_1(X1)) = k1_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_93])).

cnf(c_0_112,plain,
    ( k2_relat_1(k5_relat_1(k6_relat_1(X1),k5_relat_1(k6_relat_1(X2),k6_relat_1(X3)))) = k1_relat_1(k5_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)),k6_relat_1(X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_94,c_0_82]),c_0_66])).

cnf(c_0_113,plain,
    ( k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) = k6_relat_1(k10_relat_1(k6_relat_1(X1),X2)) ),
    inference(rw,[status(thm)],[c_0_95,c_0_96])).

cnf(c_0_114,plain,
    ( k10_relat_1(k6_relat_1(X1),X2) = X2
    | ~ r1_tarski(X2,X1) ),
    inference(rw,[status(thm)],[c_0_97,c_0_96])).

cnf(c_0_115,plain,
    ( r1_tarski(k10_relat_1(k6_relat_1(X1),X2),X2) ),
    inference(rw,[status(thm)],[c_0_98,c_0_96])).

cnf(c_0_116,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_99])).

cnf(c_0_117,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_100])).

cnf(c_0_118,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_102]),c_0_103])).

cnf(c_0_119,plain,
    ( r2_hidden(esk2_2(X1,k2_xboole_0(X1,X2)),X1)
    | r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_104,c_0_105])).

cnf(c_0_120,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_106])).

fof(c_0_121,plain,(
    ! [X8,X9] : k2_xboole_0(X8,X9) = k2_xboole_0(X9,X8) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_122,plain,
    ( k10_relat_1(k7_relat_1(X1,X2),X3) = k3_xboole_0(X2,k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_107])).

fof(c_0_123,negated_conjecture,
    ( v1_relat_1(esk3_0)
    & v1_funct_1(esk3_0)
    & r1_tarski(k10_relat_1(esk3_0,esk5_0),esk4_0)
    & k10_relat_1(esk3_0,esk5_0) != k10_relat_1(k7_relat_1(esk3_0,esk4_0),esk5_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_108])])])).

cnf(c_0_124,plain,
    ( k2_xboole_0(k10_relat_1(k6_relat_1(X1),X2),k10_relat_1(k6_relat_1(X1),X3)) = k10_relat_1(k6_relat_1(X1),k2_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_109,c_0_69])).

cnf(c_0_125,plain,
    ( k2_xboole_0(X1,k5_xboole_0(X2,k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))))) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_110,c_0_82])).

cnf(c_0_126,plain,
    ( k10_relat_1(k6_relat_1(X1),X1) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111,c_0_69]),c_0_65]),c_0_67])).

cnf(c_0_127,plain,
    ( k10_relat_1(k6_relat_1(k10_relat_1(k6_relat_1(X1),X2)),X3) = k10_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X2),X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_112,c_0_113]),c_0_113]),c_0_65]),c_0_113]),c_0_113]),c_0_67])).

cnf(c_0_128,plain,
    ( k10_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X2),X1)) = k10_relat_1(k6_relat_1(X2),X1) ),
    inference(spm,[status(thm)],[c_0_114,c_0_115])).

cnf(c_0_129,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_116,c_0_117])).

cnf(c_0_130,plain,
    ( r1_tarski(k5_xboole_0(X1,X1),X2) ),
    inference(spm,[status(thm)],[c_0_118,c_0_119])).

cnf(c_0_131,plain,
    ( k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_120,c_0_117])).

cnf(c_0_132,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_121])).

cnf(c_0_133,plain,
    ( k10_relat_1(k7_relat_1(X1,X2),X3) = k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,k10_relat_1(X1,X3)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_122,c_0_44]),c_0_50]),c_0_51]),c_0_52]),c_0_53]),c_0_54])).

cnf(c_0_134,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_123])).

cnf(c_0_135,plain,
    ( r1_tarski(k10_relat_1(k6_relat_1(X1),X2),k10_relat_1(k6_relat_1(X1),k2_xboole_0(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_90,c_0_124])).

cnf(c_0_136,plain,
    ( k2_xboole_0(X1,k5_xboole_0(X2,k10_relat_1(k6_relat_1(X1),X2))) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_125,c_0_96])).

cnf(c_0_137,plain,
    ( k10_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X2)) = k10_relat_1(k6_relat_1(X1),X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_126,c_0_127]),c_0_128])).

cnf(c_0_138,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_129,c_0_130])).

cnf(c_0_139,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(spm,[status(thm)],[c_0_131,c_0_132])).

cnf(c_0_140,negated_conjecture,
    ( k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k10_relat_1(esk3_0,X2))) = k10_relat_1(k7_relat_1(esk3_0,X1),X2) ),
    inference(spm,[status(thm)],[c_0_133,c_0_134])).

cnf(c_0_141,plain,
    ( r1_tarski(X1,k10_relat_1(k6_relat_1(X1),k2_xboole_0(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_135,c_0_126])).

cnf(c_0_142,plain,
    ( k2_xboole_0(X1,k10_relat_1(k6_relat_1(X1),X2)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_136,c_0_137]),c_0_138]),c_0_139])).

cnf(c_0_143,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_90,c_0_132])).

cnf(c_0_144,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk3_0,esk5_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_123])).

cnf(c_0_145,negated_conjecture,
    ( k1_relat_1(k5_relat_1(k6_relat_1(k10_relat_1(esk3_0,X1)),k6_relat_1(X2))) = k10_relat_1(k7_relat_1(esk3_0,X2),X1) ),
    inference(rw,[status(thm)],[c_0_140,c_0_82])).

cnf(c_0_146,plain,
    ( k10_relat_1(k6_relat_1(X1),k2_xboole_0(X1,X2)) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120,c_0_141]),c_0_142])).

cnf(c_0_147,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X2,X1)) = k2_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_120,c_0_143])).

cnf(c_0_148,negated_conjecture,
    ( k2_xboole_0(k10_relat_1(esk3_0,esk5_0),esk4_0) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_120,c_0_144])).

cnf(c_0_149,negated_conjecture,
    ( k10_relat_1(esk3_0,esk5_0) != k10_relat_1(k7_relat_1(esk3_0,esk4_0),esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_123])).

cnf(c_0_150,negated_conjecture,
    ( k10_relat_1(k7_relat_1(esk3_0,X1),X2) = k10_relat_1(k6_relat_1(k10_relat_1(esk3_0,X2)),X1) ),
    inference(rw,[status(thm)],[c_0_145,c_0_96])).

cnf(c_0_151,plain,
    ( k10_relat_1(k6_relat_1(X1),k2_xboole_0(X2,X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_146,c_0_147])).

cnf(c_0_152,negated_conjecture,
    ( k2_xboole_0(esk4_0,k10_relat_1(esk3_0,esk5_0)) = esk4_0 ),
    inference(rw,[status(thm)],[c_0_148,c_0_132])).

cnf(c_0_153,negated_conjecture,
    ( k10_relat_1(k6_relat_1(k10_relat_1(esk3_0,esk5_0)),esk4_0) != k10_relat_1(esk3_0,esk5_0) ),
    inference(rw,[status(thm)],[c_0_149,c_0_150])).

cnf(c_0_154,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_151,c_0_152]),c_0_153]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 15:26:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.53  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_S2mI
% 0.20/0.53  # and selection function SelectCQArNTNpEqFirst.
% 0.20/0.53  #
% 0.20/0.53  # Preprocessing time       : 0.029 s
% 0.20/0.53  # Presaturation interreduction done
% 0.20/0.53  
% 0.20/0.53  # Proof found!
% 0.20/0.53  # SZS status Theorem
% 0.20/0.53  # SZS output start CNFRefutation
% 0.20/0.53  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.20/0.53  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.20/0.53  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.20/0.53  fof(t43_funct_1, axiom, ![X1, X2]:k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))=k6_relat_1(k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_funct_1)).
% 0.20/0.53  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.20/0.53  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.20/0.53  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 0.20/0.53  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 0.20/0.53  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 0.20/0.53  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 0.20/0.53  fof(t79_xboole_1, axiom, ![X1, X2]:r1_xboole_0(k4_xboole_0(X1,X2),X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 0.20/0.53  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.20/0.53  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.20/0.53  fof(t16_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(k3_xboole_0(X1,X2),X3)=k3_xboole_0(X1,k3_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_xboole_1)).
% 0.20/0.53  fof(t71_relat_1, axiom, ![X1]:(k1_relat_1(k6_relat_1(X1))=X1&k2_relat_1(k6_relat_1(X1))=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 0.20/0.53  fof(t182_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>k1_relat_1(k5_relat_1(X1,X2))=k10_relat_1(X1,k1_relat_1(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t182_relat_1)).
% 0.20/0.53  fof(fc3_funct_1, axiom, ![X1]:(v1_relat_1(k6_relat_1(X1))&v1_funct_1(k6_relat_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 0.20/0.53  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 0.20/0.53  fof(idempotence_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 0.20/0.53  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.20/0.53  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.20/0.53  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 0.20/0.53  fof(t175_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>k10_relat_1(X3,k2_xboole_0(X1,X2))=k2_xboole_0(k10_relat_1(X3,X1),k10_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t175_relat_1)).
% 0.20/0.53  fof(t169_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k10_relat_1(X1,k2_relat_1(X1))=k1_relat_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 0.20/0.53  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.20/0.53  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.20/0.53  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.20/0.53  fof(t139_funct_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>k10_relat_1(k7_relat_1(X3,X1),X2)=k3_xboole_0(X1,k10_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t139_funct_1)).
% 0.20/0.53  fof(t175_funct_2, conjecture, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2, X3]:(r1_tarski(k10_relat_1(X1,X3),X2)=>k10_relat_1(X1,X3)=k10_relat_1(k7_relat_1(X1,X2),X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t175_funct_2)).
% 0.20/0.53  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.20/0.53  fof(c_0_30, plain, ![X79, X80]:k1_setfam_1(k2_tarski(X79,X80))=k3_xboole_0(X79,X80), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.20/0.53  fof(c_0_31, plain, ![X52, X53]:k1_enumset1(X52,X52,X53)=k2_tarski(X52,X53), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.20/0.53  fof(c_0_32, plain, ![X25, X26]:k4_xboole_0(X25,X26)=k5_xboole_0(X25,k3_xboole_0(X25,X26)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.20/0.53  cnf(c_0_33, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.53  cnf(c_0_34, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.20/0.53  fof(c_0_35, plain, ![X92, X93]:k5_relat_1(k6_relat_1(X93),k6_relat_1(X92))=k6_relat_1(k3_xboole_0(X92,X93)), inference(variable_rename,[status(thm)],[t43_funct_1])).
% 0.20/0.53  fof(c_0_36, plain, ![X54, X55, X56]:k2_enumset1(X54,X54,X55,X56)=k1_enumset1(X54,X55,X56), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.20/0.53  fof(c_0_37, plain, ![X57, X58, X59, X60]:k3_enumset1(X57,X57,X58,X59,X60)=k2_enumset1(X57,X58,X59,X60), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.20/0.53  fof(c_0_38, plain, ![X61, X62, X63, X64, X65]:k4_enumset1(X61,X61,X62,X63,X64,X65)=k3_enumset1(X61,X62,X63,X64,X65), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.20/0.53  fof(c_0_39, plain, ![X66, X67, X68, X69, X70, X71]:k5_enumset1(X66,X66,X67,X68,X69,X70,X71)=k4_enumset1(X66,X67,X68,X69,X70,X71), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.20/0.53  fof(c_0_40, plain, ![X72, X73, X74, X75, X76, X77, X78]:k6_enumset1(X72,X72,X73,X74,X75,X76,X77,X78)=k5_enumset1(X72,X73,X74,X75,X76,X77,X78), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.20/0.53  fof(c_0_41, plain, ![X17, X18, X20, X21, X22]:((r1_xboole_0(X17,X18)|r2_hidden(esk2_2(X17,X18),k3_xboole_0(X17,X18)))&(~r2_hidden(X22,k3_xboole_0(X20,X21))|~r1_xboole_0(X20,X21))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 0.20/0.53  fof(c_0_42, plain, ![X45, X46]:r1_xboole_0(k4_xboole_0(X45,X46),X46), inference(variable_rename,[status(thm)],[t79_xboole_1])).
% 0.20/0.53  cnf(c_0_43, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.53  cnf(c_0_44, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_33, c_0_34])).
% 0.20/0.53  fof(c_0_45, plain, ![X34, X35]:(~r1_tarski(X34,X35)|k3_xboole_0(X34,X35)=X34), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.20/0.53  fof(c_0_46, plain, ![X38, X39]:r1_tarski(k4_xboole_0(X38,X39),X38), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.20/0.53  fof(c_0_47, plain, ![X29, X30, X31]:k3_xboole_0(k3_xboole_0(X29,X30),X31)=k3_xboole_0(X29,k3_xboole_0(X30,X31)), inference(variable_rename,[status(thm)],[t16_xboole_1])).
% 0.20/0.53  fof(c_0_48, plain, ![X87]:(k1_relat_1(k6_relat_1(X87))=X87&k2_relat_1(k6_relat_1(X87))=X87), inference(variable_rename,[status(thm)],[t71_relat_1])).
% 0.20/0.53  cnf(c_0_49, plain, (k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))=k6_relat_1(k3_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.20/0.53  cnf(c_0_50, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.20/0.53  cnf(c_0_51, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.20/0.53  cnf(c_0_52, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.20/0.53  cnf(c_0_53, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.20/0.53  cnf(c_0_54, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.20/0.53  fof(c_0_55, plain, ![X85, X86]:(~v1_relat_1(X85)|(~v1_relat_1(X86)|k1_relat_1(k5_relat_1(X85,X86))=k10_relat_1(X85,k1_relat_1(X86)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t182_relat_1])])])).
% 0.20/0.53  fof(c_0_56, plain, ![X88]:(v1_relat_1(k6_relat_1(X88))&v1_funct_1(k6_relat_1(X88))), inference(variable_rename,[status(thm)],[fc3_funct_1])).
% 0.20/0.53  fof(c_0_57, plain, ![X32, X33]:r1_tarski(k3_xboole_0(X32,X33),X32), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 0.20/0.53  cnf(c_0_58, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.20/0.53  cnf(c_0_59, plain, (r1_xboole_0(k4_xboole_0(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.20/0.53  cnf(c_0_60, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2)))), inference(rw,[status(thm)],[c_0_43, c_0_44])).
% 0.20/0.53  cnf(c_0_61, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.20/0.53  cnf(c_0_62, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.20/0.53  cnf(c_0_63, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk2_2(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.20/0.53  cnf(c_0_64, plain, (k3_xboole_0(k3_xboole_0(X1,X2),X3)=k3_xboole_0(X1,k3_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.20/0.53  cnf(c_0_65, plain, (k2_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.20/0.53  cnf(c_0_66, plain, (k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))=k6_relat_1(k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49, c_0_44]), c_0_50]), c_0_51]), c_0_52]), c_0_53]), c_0_54])).
% 0.20/0.53  cnf(c_0_67, plain, (k1_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.20/0.53  cnf(c_0_68, plain, (k1_relat_1(k5_relat_1(X1,X2))=k10_relat_1(X1,k1_relat_1(X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.20/0.53  cnf(c_0_69, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.20/0.53  cnf(c_0_70, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.20/0.53  cnf(c_0_71, plain, (~r1_xboole_0(X2,X3)|~r2_hidden(X1,k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58, c_0_44]), c_0_50]), c_0_51]), c_0_52]), c_0_53]), c_0_54])).
% 0.20/0.53  cnf(c_0_72, plain, (r1_xboole_0(k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59, c_0_60]), c_0_50]), c_0_51]), c_0_52]), c_0_53]), c_0_54])).
% 0.20/0.53  cnf(c_0_73, plain, (k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))=X1|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61, c_0_44]), c_0_50]), c_0_51]), c_0_52]), c_0_53]), c_0_54])).
% 0.20/0.53  cnf(c_0_74, plain, (r1_tarski(k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_62, c_0_60]), c_0_50]), c_0_51]), c_0_52]), c_0_53]), c_0_54])).
% 0.20/0.53  fof(c_0_75, plain, ![X16]:k3_xboole_0(X16,X16)=X16, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).
% 0.20/0.53  cnf(c_0_76, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk2_2(X1,X2),k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_63, c_0_44]), c_0_50]), c_0_51]), c_0_52]), c_0_53]), c_0_54])).
% 0.20/0.53  fof(c_0_77, plain, ![X10, X11, X12, X13, X14]:((~r1_tarski(X10,X11)|(~r2_hidden(X12,X10)|r2_hidden(X12,X11)))&((r2_hidden(esk1_2(X13,X14),X13)|r1_tarski(X13,X14))&(~r2_hidden(esk1_2(X13,X14),X14)|r1_tarski(X13,X14)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.20/0.53  fof(c_0_78, plain, ![X47, X48]:r1_tarski(X47,k2_xboole_0(X47,X48)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.20/0.53  fof(c_0_79, plain, ![X40, X41]:k2_xboole_0(X40,k4_xboole_0(X41,X40))=k2_xboole_0(X40,X41), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 0.20/0.53  cnf(c_0_80, plain, (k1_setfam_1(k6_enumset1(k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),X3))=k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_64, c_0_44]), c_0_44]), c_0_44]), c_0_44]), c_0_50]), c_0_50]), c_0_50]), c_0_50]), c_0_50]), c_0_51]), c_0_51]), c_0_51]), c_0_51]), c_0_51]), c_0_51]), c_0_52]), c_0_52]), c_0_52]), c_0_52]), c_0_52]), c_0_52]), c_0_52]), c_0_53]), c_0_53]), c_0_53]), c_0_53]), c_0_53]), c_0_53]), c_0_53]), c_0_53]), c_0_54]), c_0_54]), c_0_54]), c_0_54]), c_0_54]), c_0_54]), c_0_54]), c_0_54]), c_0_54])).
% 0.20/0.53  cnf(c_0_81, plain, (k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))=k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 0.20/0.53  cnf(c_0_82, plain, (k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))=k1_relat_1(k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)))), inference(spm,[status(thm)],[c_0_67, c_0_66])).
% 0.20/0.53  cnf(c_0_83, plain, (k1_relat_1(k5_relat_1(k6_relat_1(X1),X2))=k10_relat_1(k6_relat_1(X1),k1_relat_1(X2))|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 0.20/0.53  cnf(c_0_84, plain, (r1_tarski(k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_70, c_0_44]), c_0_50]), c_0_51]), c_0_52]), c_0_53]), c_0_54])).
% 0.20/0.53  cnf(c_0_85, plain, (~r2_hidden(X1,k1_setfam_1(k6_enumset1(k5_xboole_0(X2,k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3))),k5_xboole_0(X2,k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3))),k5_xboole_0(X2,k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3))),k5_xboole_0(X2,k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3))),k5_xboole_0(X2,k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3))),k5_xboole_0(X2,k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3))),k5_xboole_0(X2,k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3))),X3)))), inference(spm,[status(thm)],[c_0_71, c_0_72])).
% 0.20/0.53  cnf(c_0_86, plain, (k1_setfam_1(k6_enumset1(k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))),k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))),k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))),k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))),k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))),k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))),k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))),X1))=k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))), inference(spm,[status(thm)],[c_0_73, c_0_74])).
% 0.20/0.53  cnf(c_0_87, plain, (k3_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_75])).
% 0.20/0.53  cnf(c_0_88, plain, (r2_hidden(esk2_2(X1,X2),k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))|~r2_hidden(X3,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))), inference(spm,[status(thm)],[c_0_71, c_0_76])).
% 0.20/0.53  cnf(c_0_89, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_77])).
% 0.20/0.53  cnf(c_0_90, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_78])).
% 0.20/0.53  fof(c_0_91, plain, ![X82, X83, X84]:(~v1_relat_1(X84)|k10_relat_1(X84,k2_xboole_0(X82,X83))=k2_xboole_0(k10_relat_1(X84,X82),k10_relat_1(X84,X83))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t175_relat_1])])).
% 0.20/0.53  cnf(c_0_92, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_79])).
% 0.20/0.53  fof(c_0_93, plain, ![X81]:(~v1_relat_1(X81)|k10_relat_1(X81,k2_relat_1(X81))=k1_relat_1(X81)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t169_relat_1])])).
% 0.20/0.53  cnf(c_0_94, plain, (k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3))))=k2_relat_1(k5_relat_1(k6_relat_1(X3),k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_80, c_0_81]), c_0_66])).
% 0.20/0.53  cnf(c_0_95, plain, (k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))))=k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))), inference(rw,[status(thm)],[c_0_66, c_0_82])).
% 0.20/0.53  cnf(c_0_96, plain, (k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))=k10_relat_1(k6_relat_1(X1),X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_69]), c_0_67])).
% 0.20/0.53  cnf(c_0_97, plain, (k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))=X2|~r1_tarski(X2,X1)), inference(rw,[status(thm)],[c_0_73, c_0_82])).
% 0.20/0.53  cnf(c_0_98, plain, (r1_tarski(k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))),X2)), inference(rw,[status(thm)],[c_0_84, c_0_82])).
% 0.20/0.53  fof(c_0_99, plain, ![X23, X24]:(((r1_tarski(X23,X24)|X23!=X24)&(r1_tarski(X24,X23)|X23!=X24))&(~r1_tarski(X23,X24)|~r1_tarski(X24,X23)|X23=X24)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.20/0.53  fof(c_0_100, plain, ![X37]:r1_tarski(k1_xboole_0,X37), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.20/0.53  cnf(c_0_101, plain, (~r2_hidden(X1,k2_relat_1(k5_relat_1(k6_relat_1(X2),k6_relat_1(k5_xboole_0(X3,k1_setfam_1(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X2)))))))), inference(rw,[status(thm)],[c_0_85, c_0_81])).
% 0.20/0.53  cnf(c_0_102, plain, (k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))))))=k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))), inference(rw,[status(thm)],[c_0_86, c_0_81])).
% 0.20/0.53  cnf(c_0_103, plain, (k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_87, c_0_44]), c_0_50]), c_0_51]), c_0_52]), c_0_53]), c_0_54])).
% 0.20/0.53  cnf(c_0_104, plain, (r2_hidden(esk2_2(X1,X2),k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))|r1_tarski(k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),X3)), inference(spm,[status(thm)],[c_0_88, c_0_89])).
% 0.20/0.53  cnf(c_0_105, plain, (k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k2_xboole_0(X1,X2)))=X1), inference(spm,[status(thm)],[c_0_73, c_0_90])).
% 0.20/0.53  fof(c_0_106, plain, ![X27, X28]:(~r1_tarski(X27,X28)|k2_xboole_0(X27,X28)=X28), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.20/0.53  fof(c_0_107, plain, ![X89, X90, X91]:(~v1_relat_1(X91)|k10_relat_1(k7_relat_1(X91,X89),X90)=k3_xboole_0(X89,k10_relat_1(X91,X90))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t139_funct_1])])).
% 0.20/0.53  fof(c_0_108, negated_conjecture, ~(![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2, X3]:(r1_tarski(k10_relat_1(X1,X3),X2)=>k10_relat_1(X1,X3)=k10_relat_1(k7_relat_1(X1,X2),X3)))), inference(assume_negation,[status(cth)],[t175_funct_2])).
% 0.20/0.53  cnf(c_0_109, plain, (k10_relat_1(X1,k2_xboole_0(X2,X3))=k2_xboole_0(k10_relat_1(X1,X2),k10_relat_1(X1,X3))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_91])).
% 0.20/0.53  cnf(c_0_110, plain, (k2_xboole_0(X1,k5_xboole_0(X2,k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_92, c_0_60]), c_0_50]), c_0_51]), c_0_52]), c_0_53]), c_0_54])).
% 0.20/0.53  cnf(c_0_111, plain, (k10_relat_1(X1,k2_relat_1(X1))=k1_relat_1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_93])).
% 0.20/0.53  cnf(c_0_112, plain, (k2_relat_1(k5_relat_1(k6_relat_1(X1),k5_relat_1(k6_relat_1(X2),k6_relat_1(X3))))=k1_relat_1(k5_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)),k6_relat_1(X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_94, c_0_82]), c_0_66])).
% 0.20/0.53  cnf(c_0_113, plain, (k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))=k6_relat_1(k10_relat_1(k6_relat_1(X1),X2))), inference(rw,[status(thm)],[c_0_95, c_0_96])).
% 0.20/0.53  cnf(c_0_114, plain, (k10_relat_1(k6_relat_1(X1),X2)=X2|~r1_tarski(X2,X1)), inference(rw,[status(thm)],[c_0_97, c_0_96])).
% 0.20/0.53  cnf(c_0_115, plain, (r1_tarski(k10_relat_1(k6_relat_1(X1),X2),X2)), inference(rw,[status(thm)],[c_0_98, c_0_96])).
% 0.20/0.53  cnf(c_0_116, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_99])).
% 0.20/0.53  cnf(c_0_117, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_100])).
% 0.20/0.53  cnf(c_0_118, plain, (~r2_hidden(X1,k5_xboole_0(X2,X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101, c_0_102]), c_0_103])).
% 0.20/0.53  cnf(c_0_119, plain, (r2_hidden(esk2_2(X1,k2_xboole_0(X1,X2)),X1)|r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_104, c_0_105])).
% 0.20/0.53  cnf(c_0_120, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_106])).
% 0.20/0.53  fof(c_0_121, plain, ![X8, X9]:k2_xboole_0(X8,X9)=k2_xboole_0(X9,X8), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.20/0.53  cnf(c_0_122, plain, (k10_relat_1(k7_relat_1(X1,X2),X3)=k3_xboole_0(X2,k10_relat_1(X1,X3))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_107])).
% 0.20/0.53  fof(c_0_123, negated_conjecture, ((v1_relat_1(esk3_0)&v1_funct_1(esk3_0))&(r1_tarski(k10_relat_1(esk3_0,esk5_0),esk4_0)&k10_relat_1(esk3_0,esk5_0)!=k10_relat_1(k7_relat_1(esk3_0,esk4_0),esk5_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_108])])])).
% 0.20/0.53  cnf(c_0_124, plain, (k2_xboole_0(k10_relat_1(k6_relat_1(X1),X2),k10_relat_1(k6_relat_1(X1),X3))=k10_relat_1(k6_relat_1(X1),k2_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_109, c_0_69])).
% 0.20/0.53  cnf(c_0_125, plain, (k2_xboole_0(X1,k5_xboole_0(X2,k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_110, c_0_82])).
% 0.20/0.53  cnf(c_0_126, plain, (k10_relat_1(k6_relat_1(X1),X1)=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111, c_0_69]), c_0_65]), c_0_67])).
% 0.20/0.53  cnf(c_0_127, plain, (k10_relat_1(k6_relat_1(k10_relat_1(k6_relat_1(X1),X2)),X3)=k10_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X2),X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_112, c_0_113]), c_0_113]), c_0_65]), c_0_113]), c_0_113]), c_0_67])).
% 0.20/0.53  cnf(c_0_128, plain, (k10_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X2),X1))=k10_relat_1(k6_relat_1(X2),X1)), inference(spm,[status(thm)],[c_0_114, c_0_115])).
% 0.20/0.53  cnf(c_0_129, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_116, c_0_117])).
% 0.20/0.53  cnf(c_0_130, plain, (r1_tarski(k5_xboole_0(X1,X1),X2)), inference(spm,[status(thm)],[c_0_118, c_0_119])).
% 0.20/0.53  cnf(c_0_131, plain, (k2_xboole_0(k1_xboole_0,X1)=X1), inference(spm,[status(thm)],[c_0_120, c_0_117])).
% 0.20/0.53  cnf(c_0_132, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_121])).
% 0.20/0.53  cnf(c_0_133, plain, (k10_relat_1(k7_relat_1(X1,X2),X3)=k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,k10_relat_1(X1,X3)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_122, c_0_44]), c_0_50]), c_0_51]), c_0_52]), c_0_53]), c_0_54])).
% 0.20/0.53  cnf(c_0_134, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_123])).
% 0.20/0.53  cnf(c_0_135, plain, (r1_tarski(k10_relat_1(k6_relat_1(X1),X2),k10_relat_1(k6_relat_1(X1),k2_xboole_0(X2,X3)))), inference(spm,[status(thm)],[c_0_90, c_0_124])).
% 0.20/0.53  cnf(c_0_136, plain, (k2_xboole_0(X1,k5_xboole_0(X2,k10_relat_1(k6_relat_1(X1),X2)))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_125, c_0_96])).
% 0.20/0.53  cnf(c_0_137, plain, (k10_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X2))=k10_relat_1(k6_relat_1(X1),X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_126, c_0_127]), c_0_128])).
% 0.20/0.53  cnf(c_0_138, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_129, c_0_130])).
% 0.20/0.53  cnf(c_0_139, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(spm,[status(thm)],[c_0_131, c_0_132])).
% 0.20/0.53  cnf(c_0_140, negated_conjecture, (k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k10_relat_1(esk3_0,X2)))=k10_relat_1(k7_relat_1(esk3_0,X1),X2)), inference(spm,[status(thm)],[c_0_133, c_0_134])).
% 0.20/0.53  cnf(c_0_141, plain, (r1_tarski(X1,k10_relat_1(k6_relat_1(X1),k2_xboole_0(X1,X2)))), inference(spm,[status(thm)],[c_0_135, c_0_126])).
% 0.20/0.53  cnf(c_0_142, plain, (k2_xboole_0(X1,k10_relat_1(k6_relat_1(X1),X2))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_136, c_0_137]), c_0_138]), c_0_139])).
% 0.20/0.53  cnf(c_0_143, plain, (r1_tarski(X1,k2_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_90, c_0_132])).
% 0.20/0.53  cnf(c_0_144, negated_conjecture, (r1_tarski(k10_relat_1(esk3_0,esk5_0),esk4_0)), inference(split_conjunct,[status(thm)],[c_0_123])).
% 0.20/0.53  cnf(c_0_145, negated_conjecture, (k1_relat_1(k5_relat_1(k6_relat_1(k10_relat_1(esk3_0,X1)),k6_relat_1(X2)))=k10_relat_1(k7_relat_1(esk3_0,X2),X1)), inference(rw,[status(thm)],[c_0_140, c_0_82])).
% 0.20/0.53  cnf(c_0_146, plain, (k10_relat_1(k6_relat_1(X1),k2_xboole_0(X1,X2))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120, c_0_141]), c_0_142])).
% 0.20/0.53  cnf(c_0_147, plain, (k2_xboole_0(X1,k2_xboole_0(X2,X1))=k2_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_120, c_0_143])).
% 0.20/0.53  cnf(c_0_148, negated_conjecture, (k2_xboole_0(k10_relat_1(esk3_0,esk5_0),esk4_0)=esk4_0), inference(spm,[status(thm)],[c_0_120, c_0_144])).
% 0.20/0.53  cnf(c_0_149, negated_conjecture, (k10_relat_1(esk3_0,esk5_0)!=k10_relat_1(k7_relat_1(esk3_0,esk4_0),esk5_0)), inference(split_conjunct,[status(thm)],[c_0_123])).
% 0.20/0.53  cnf(c_0_150, negated_conjecture, (k10_relat_1(k7_relat_1(esk3_0,X1),X2)=k10_relat_1(k6_relat_1(k10_relat_1(esk3_0,X2)),X1)), inference(rw,[status(thm)],[c_0_145, c_0_96])).
% 0.20/0.53  cnf(c_0_151, plain, (k10_relat_1(k6_relat_1(X1),k2_xboole_0(X2,X1))=X1), inference(spm,[status(thm)],[c_0_146, c_0_147])).
% 0.20/0.53  cnf(c_0_152, negated_conjecture, (k2_xboole_0(esk4_0,k10_relat_1(esk3_0,esk5_0))=esk4_0), inference(rw,[status(thm)],[c_0_148, c_0_132])).
% 0.20/0.53  cnf(c_0_153, negated_conjecture, (k10_relat_1(k6_relat_1(k10_relat_1(esk3_0,esk5_0)),esk4_0)!=k10_relat_1(esk3_0,esk5_0)), inference(rw,[status(thm)],[c_0_149, c_0_150])).
% 0.20/0.53  cnf(c_0_154, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_151, c_0_152]), c_0_153]), ['proof']).
% 0.20/0.53  # SZS output end CNFRefutation
% 0.20/0.53  # Proof object total steps             : 155
% 0.20/0.53  # Proof object clause steps            : 94
% 0.20/0.53  # Proof object formula steps           : 61
% 0.20/0.53  # Proof object conjectures             : 13
% 0.20/0.53  # Proof object clause conjectures      : 10
% 0.20/0.53  # Proof object formula conjectures     : 3
% 0.20/0.53  # Proof object initial clauses used    : 34
% 0.20/0.53  # Proof object initial formulas used   : 30
% 0.20/0.53  # Proof object generating inferences   : 30
% 0.20/0.53  # Proof object simplifying inferences  : 134
% 0.20/0.53  # Training examples: 0 positive, 0 negative
% 0.20/0.53  # Parsed axioms                        : 33
% 0.20/0.53  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.53  # Initial clauses                      : 43
% 0.20/0.53  # Removed in clause preprocessing      : 8
% 0.20/0.53  # Initial clauses in saturation        : 35
% 0.20/0.53  # Processed clauses                    : 1992
% 0.20/0.53  # ...of these trivial                  : 109
% 0.20/0.53  # ...subsumed                          : 1285
% 0.20/0.53  # ...remaining for further processing  : 598
% 0.20/0.53  # Other redundant clauses eliminated   : 2
% 0.20/0.53  # Clauses deleted for lack of memory   : 0
% 0.20/0.53  # Backward-subsumed                    : 4
% 0.20/0.53  # Backward-rewritten                   : 252
% 0.20/0.53  # Generated clauses                    : 8728
% 0.20/0.53  # ...of the previous two non-trivial   : 6736
% 0.20/0.53  # Contextual simplify-reflections      : 0
% 0.20/0.53  # Paramodulations                      : 8726
% 0.20/0.53  # Factorizations                       : 0
% 0.20/0.53  # Equation resolutions                 : 2
% 0.20/0.53  # Propositional unsat checks           : 0
% 0.20/0.53  #    Propositional check models        : 0
% 0.20/0.53  #    Propositional check unsatisfiable : 0
% 0.20/0.53  #    Propositional clauses             : 0
% 0.20/0.53  #    Propositional clauses after purity: 0
% 0.20/0.53  #    Propositional unsat core size     : 0
% 0.20/0.53  #    Propositional preprocessing time  : 0.000
% 0.20/0.53  #    Propositional encoding time       : 0.000
% 0.20/0.53  #    Propositional solver time         : 0.000
% 0.20/0.53  #    Success case prop preproc time    : 0.000
% 0.20/0.53  #    Success case prop encoding time   : 0.000
% 0.20/0.53  #    Success case prop solver time     : 0.000
% 0.20/0.53  # Current number of processed clauses  : 306
% 0.20/0.53  #    Positive orientable unit clauses  : 124
% 0.20/0.53  #    Positive unorientable unit clauses: 1
% 0.20/0.53  #    Negative unit clauses             : 2
% 0.20/0.53  #    Non-unit-clauses                  : 179
% 0.20/0.53  # Current number of unprocessed clauses: 4451
% 0.20/0.53  # ...number of literals in the above   : 6810
% 0.20/0.53  # Current number of archived formulas  : 0
% 0.20/0.53  # Current number of archived clauses   : 298
% 0.20/0.53  # Clause-clause subsumption calls (NU) : 7316
% 0.20/0.53  # Rec. Clause-clause subsumption calls : 7182
% 0.20/0.53  # Non-unit clause-clause subsumptions  : 877
% 0.20/0.53  # Unit Clause-clause subsumption calls : 763
% 0.20/0.53  # Rewrite failures with RHS unbound    : 0
% 0.20/0.53  # BW rewrite match attempts            : 916
% 0.20/0.53  # BW rewrite match successes           : 167
% 0.20/0.53  # Condensation attempts                : 0
% 0.20/0.53  # Condensation successes               : 0
% 0.20/0.53  # Termbank termtop insertions          : 161016
% 0.20/0.53  
% 0.20/0.53  # -------------------------------------------------
% 0.20/0.53  # User time                : 0.175 s
% 0.20/0.53  # System time              : 0.015 s
% 0.20/0.53  # Total time               : 0.190 s
% 0.20/0.53  # Maximum resident set size: 1604 pages
%------------------------------------------------------------------------------
