%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:54:48 EST 2020

% Result     : Theorem 0.39s
% Output     : CNFRefutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 435 expanded)
%              Number of clauses        :   64 ( 182 expanded)
%              Number of leaves         :   26 ( 117 expanded)
%              Depth                    :   10
%              Number of atoms          :  210 ( 785 expanded)
%              Number of equality atoms :  102 ( 331 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :   12 (   1 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t146_funct_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X1,k1_relat_1(X2))
       => r1_tarski(X1,k10_relat_1(X2,k9_relat_1(X2,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

fof(t169_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,k2_relat_1(X1)) = k1_relat_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

fof(dt_k7_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k7_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t182_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k1_relat_1(k5_relat_1(X1,X2)) = k10_relat_1(X1,k1_relat_1(X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

fof(t94_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,X1) = k5_relat_1(k6_relat_1(X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(t139_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => k10_relat_1(k7_relat_1(X3,X1),X2) = k3_xboole_0(X1,k10_relat_1(X3,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).

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

fof(t175_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => k10_relat_1(X3,k2_xboole_0(X1,X2)) = k2_xboole_0(k10_relat_1(X3,X1),k10_relat_1(X3,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_relat_1)).

fof(dt_k6_relat_1,axiom,(
    ! [X1] : v1_relat_1(k6_relat_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(t14_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X3,X2)
        & ! [X4] :
            ( ( r1_tarski(X1,X4)
              & r1_tarski(X3,X4) )
           => r1_tarski(X2,X4) ) )
     => X2 = k2_xboole_0(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_xboole_1)).

fof(t167_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k10_relat_1(X2,X1),k1_relat_1(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

fof(t71_relat_1,axiom,(
    ! [X1] :
      ( k1_relat_1(k6_relat_1(X1)) = X1
      & k2_relat_1(k6_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t146_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,k1_relat_1(X1)) = k2_relat_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

fof(t162_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2,X3] :
          ( r1_tarski(X2,X3)
         => k9_relat_1(k7_relat_1(X1,X3),X2) = k9_relat_1(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_relat_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(c_0_26,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X1,k1_relat_1(X2))
         => r1_tarski(X1,k10_relat_1(X2,k9_relat_1(X2,X1))) ) ) ),
    inference(assume_negation,[status(cth)],[t146_funct_1])).

fof(c_0_27,plain,(
    ! [X65] :
      ( ~ v1_relat_1(X65)
      | k10_relat_1(X65,k2_relat_1(X65)) = k1_relat_1(X65) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t169_relat_1])])).

fof(c_0_28,negated_conjecture,
    ( v1_relat_1(esk3_0)
    & r1_tarski(esk2_0,k1_relat_1(esk3_0))
    & ~ r1_tarski(esk2_0,k10_relat_1(esk3_0,k9_relat_1(esk3_0,esk2_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_26])])])).

fof(c_0_29,plain,(
    ! [X57,X58] :
      ( ~ v1_relat_1(X57)
      | v1_relat_1(k7_relat_1(X57,X58)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).

fof(c_0_30,plain,(
    ! [X54,X55] : k1_setfam_1(k2_tarski(X54,X55)) = k3_xboole_0(X54,X55) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_31,plain,(
    ! [X27,X28] : k1_enumset1(X27,X27,X28) = k2_tarski(X27,X28) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

cnf(c_0_32,plain,
    ( k10_relat_1(X1,k2_relat_1(X1)) = k1_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_33,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_34,plain,(
    ! [X8,X9] :
      ( ( r1_tarski(X8,X9)
        | X8 != X9 )
      & ( r1_tarski(X9,X8)
        | X8 != X9 )
      & ( ~ r1_tarski(X8,X9)
        | ~ r1_tarski(X9,X8)
        | X8 = X9 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_35,plain,(
    ! [X69,X70] :
      ( ~ v1_relat_1(X69)
      | ~ v1_relat_1(X70)
      | k1_relat_1(k5_relat_1(X69,X70)) = k10_relat_1(X69,k1_relat_1(X70)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t182_relat_1])])])).

fof(c_0_36,plain,(
    ! [X74,X75] :
      ( ~ v1_relat_1(X75)
      | k7_relat_1(X75,X74) = k5_relat_1(k6_relat_1(X74),X75) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).

cnf(c_0_37,plain,
    ( v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_38,plain,(
    ! [X76,X77,X78] :
      ( ~ v1_relat_1(X78)
      | k10_relat_1(k7_relat_1(X78,X76),X77) = k3_xboole_0(X76,k10_relat_1(X78,X77)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t139_funct_1])])).

cnf(c_0_39,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_40,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_41,plain,(
    ! [X29,X30,X31] : k2_enumset1(X29,X29,X30,X31) = k1_enumset1(X29,X30,X31) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_42,plain,(
    ! [X32,X33,X34,X35] : k3_enumset1(X32,X32,X33,X34,X35) = k2_enumset1(X32,X33,X34,X35) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_43,plain,(
    ! [X36,X37,X38,X39,X40] : k4_enumset1(X36,X36,X37,X38,X39,X40) = k3_enumset1(X36,X37,X38,X39,X40) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_44,plain,(
    ! [X41,X42,X43,X44,X45,X46] : k5_enumset1(X41,X41,X42,X43,X44,X45,X46) = k4_enumset1(X41,X42,X43,X44,X45,X46) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_45,plain,(
    ! [X47,X48,X49,X50,X51,X52,X53] : k6_enumset1(X47,X47,X48,X49,X50,X51,X52,X53) = k5_enumset1(X47,X48,X49,X50,X51,X52,X53) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_46,plain,(
    ! [X66,X67,X68] :
      ( ~ v1_relat_1(X68)
      | k10_relat_1(X68,k2_xboole_0(X66,X67)) = k2_xboole_0(k10_relat_1(X68,X66),k10_relat_1(X68,X67)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t175_relat_1])])).

fof(c_0_47,plain,(
    ! [X56] : v1_relat_1(k6_relat_1(X56)) ),
    inference(variable_rename,[status(thm)],[dt_k6_relat_1])).

fof(c_0_48,plain,(
    ! [X17,X18] :
      ( ~ r1_tarski(X17,X18)
      | k2_xboole_0(X17,X18) = X18 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_49,negated_conjecture,
    ( r1_tarski(esk2_0,k1_relat_1(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_50,negated_conjecture,
    ( k1_relat_1(esk3_0) = k10_relat_1(esk3_0,k2_relat_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

fof(c_0_51,plain,(
    ! [X19,X20,X21] :
      ( ( r1_tarski(X19,esk1_3(X19,X20,X21))
        | ~ r1_tarski(X19,X20)
        | ~ r1_tarski(X21,X20)
        | X20 = k2_xboole_0(X19,X21) )
      & ( r1_tarski(X21,esk1_3(X19,X20,X21))
        | ~ r1_tarski(X19,X20)
        | ~ r1_tarski(X21,X20)
        | X20 = k2_xboole_0(X19,X21) )
      & ( ~ r1_tarski(X20,esk1_3(X19,X20,X21))
        | ~ r1_tarski(X19,X20)
        | ~ r1_tarski(X21,X20)
        | X20 = k2_xboole_0(X19,X21) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t14_xboole_1])])])])).

cnf(c_0_52,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

fof(c_0_53,plain,(
    ! [X63,X64] :
      ( ~ v1_relat_1(X64)
      | r1_tarski(k10_relat_1(X64,X63),k1_relat_1(X64)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t167_relat_1])])).

fof(c_0_54,plain,(
    ! [X71] :
      ( k1_relat_1(k6_relat_1(X71)) = X71
      & k2_relat_1(k6_relat_1(X71)) = X71 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

cnf(c_0_55,plain,
    ( k1_relat_1(k5_relat_1(X1,X2)) = k10_relat_1(X1,k1_relat_1(X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_56,plain,
    ( k7_relat_1(X1,X2) = k5_relat_1(k6_relat_1(X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_57,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = k10_relat_1(k7_relat_1(X1,X2),k2_relat_1(k7_relat_1(X1,X2)))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_32,c_0_37])).

cnf(c_0_58,plain,
    ( k10_relat_1(k7_relat_1(X1,X2),X3) = k3_xboole_0(X2,k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_59,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_60,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_61,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_62,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_63,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_64,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

fof(c_0_65,plain,(
    ! [X12,X13] : k4_xboole_0(X12,X13) = k5_xboole_0(X12,k3_xboole_0(X12,X13)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_66,plain,(
    ! [X59] :
      ( ~ v1_relat_1(X59)
      | k9_relat_1(X59,k1_relat_1(X59)) = k2_relat_1(X59) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_relat_1])])).

cnf(c_0_67,plain,
    ( k10_relat_1(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(k10_relat_1(X1,X2),k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_68,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_69,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_70,negated_conjecture,
    ( r1_tarski(esk2_0,k10_relat_1(esk3_0,k2_relat_1(esk3_0))) ),
    inference(rw,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_71,plain,
    ( X1 = k2_xboole_0(X2,X3)
    | ~ r1_tarski(X1,esk1_3(X2,X1,X3))
    | ~ r1_tarski(X2,X1)
    | ~ r1_tarski(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_72,plain,
    ( r1_tarski(X1,esk1_3(X1,X2,X3))
    | X2 = k2_xboole_0(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_73,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_52])).

cnf(c_0_74,plain,
    ( r1_tarski(k10_relat_1(X1,X2),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_75,plain,
    ( k1_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_76,negated_conjecture,
    ( k1_relat_1(k5_relat_1(X1,esk3_0)) = k10_relat_1(X1,k10_relat_1(esk3_0,k2_relat_1(esk3_0)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_33]),c_0_50])).

cnf(c_0_77,negated_conjecture,
    ( k5_relat_1(k6_relat_1(X1),esk3_0) = k7_relat_1(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_56,c_0_33])).

cnf(c_0_78,negated_conjecture,
    ( k1_relat_1(k7_relat_1(esk3_0,X1)) = k10_relat_1(k7_relat_1(esk3_0,X1),k2_relat_1(k7_relat_1(esk3_0,X1))) ),
    inference(spm,[status(thm)],[c_0_57,c_0_33])).

cnf(c_0_79,plain,
    ( k10_relat_1(k7_relat_1(X1,X2),X3) = k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,k10_relat_1(X1,X3)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58,c_0_59]),c_0_60]),c_0_61]),c_0_62]),c_0_63]),c_0_64])).

fof(c_0_80,plain,(
    ! [X60,X61,X62] :
      ( ~ v1_relat_1(X60)
      | ~ r1_tarski(X61,X62)
      | k9_relat_1(k7_relat_1(X60,X62),X61) = k9_relat_1(X60,X61) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t162_relat_1])])])).

fof(c_0_81,plain,(
    ! [X23,X24] :
      ( ~ r1_tarski(X23,X24)
      | k3_xboole_0(X23,X24) = X23 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

fof(c_0_82,plain,(
    ! [X10,X11] :
      ( ( k4_xboole_0(X10,X11) != k1_xboole_0
        | r1_tarski(X10,X11) )
      & ( ~ r1_tarski(X10,X11)
        | k4_xboole_0(X10,X11) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

cnf(c_0_83,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_84,plain,
    ( k9_relat_1(X1,k1_relat_1(X1)) = k2_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_85,plain,
    ( k10_relat_1(k6_relat_1(X1),k2_xboole_0(X2,X3)) = k2_xboole_0(k10_relat_1(k6_relat_1(X1),X2),k10_relat_1(k6_relat_1(X1),X3)) ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_86,negated_conjecture,
    ( k2_xboole_0(esk2_0,k10_relat_1(esk3_0,k2_relat_1(esk3_0))) = k10_relat_1(esk3_0,k2_relat_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_87,plain,
    ( k2_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_88,plain,
    ( k2_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_73])])).

cnf(c_0_89,plain,
    ( r1_tarski(k10_relat_1(k6_relat_1(X1),X2),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_68]),c_0_75])).

cnf(c_0_90,negated_conjecture,
    ( k10_relat_1(k7_relat_1(esk3_0,X1),k2_relat_1(k7_relat_1(esk3_0,X1))) = k10_relat_1(k6_relat_1(X1),k10_relat_1(esk3_0,k2_relat_1(esk3_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_68]),c_0_77]),c_0_78])).

cnf(c_0_91,negated_conjecture,
    ( k10_relat_1(k7_relat_1(esk3_0,X1),X2) = k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k10_relat_1(esk3_0,X2))) ),
    inference(spm,[status(thm)],[c_0_79,c_0_33])).

cnf(c_0_92,plain,
    ( k9_relat_1(k7_relat_1(X1,X3),X2) = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_80])).

cnf(c_0_93,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_81])).

fof(c_0_94,plain,(
    ! [X25,X26] : r1_tarski(X25,k2_xboole_0(X25,X26)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

cnf(c_0_95,plain,
    ( r1_tarski(X1,X2)
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_82])).

cnf(c_0_96,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2))) ),
    inference(rw,[status(thm)],[c_0_83,c_0_59])).

cnf(c_0_97,plain,
    ( k9_relat_1(k7_relat_1(X1,X2),k1_relat_1(k7_relat_1(X1,X2))) = k2_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_84,c_0_37])).

cnf(c_0_98,negated_conjecture,
    ( k2_xboole_0(k10_relat_1(k6_relat_1(X1),esk2_0),k10_relat_1(k6_relat_1(X1),k10_relat_1(esk3_0,k2_relat_1(esk3_0)))) = k10_relat_1(k6_relat_1(X1),k10_relat_1(esk3_0,k2_relat_1(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_85,c_0_86])).

cnf(c_0_99,plain,
    ( k10_relat_1(k6_relat_1(X1),X1) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_68]),c_0_75]),c_0_87])).

cnf(c_0_100,plain,
    ( k2_xboole_0(X1,k10_relat_1(k6_relat_1(X1),X2)) = X1 ),
    inference(spm,[status(thm)],[c_0_88,c_0_89])).

cnf(c_0_101,negated_conjecture,
    ( k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k10_relat_1(esk3_0,k2_relat_1(k7_relat_1(esk3_0,X1))))) = k10_relat_1(k6_relat_1(X1),k10_relat_1(esk3_0,k2_relat_1(esk3_0))) ),
    inference(rw,[status(thm)],[c_0_90,c_0_91])).

cnf(c_0_102,negated_conjecture,
    ( k9_relat_1(k7_relat_1(esk3_0,X1),X2) = k9_relat_1(esk3_0,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_92,c_0_33])).

cnf(c_0_103,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_82])).

cnf(c_0_104,plain,
    ( k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_93,c_0_59]),c_0_60]),c_0_61]),c_0_62]),c_0_63]),c_0_64])).

cnf(c_0_105,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_94])).

cnf(c_0_106,negated_conjecture,
    ( ~ r1_tarski(esk2_0,k10_relat_1(esk3_0,k9_relat_1(esk3_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_107,plain,
    ( r1_tarski(X1,X2)
    | k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_95,c_0_96]),c_0_60]),c_0_61]),c_0_62]),c_0_63]),c_0_64])).

cnf(c_0_108,negated_conjecture,
    ( k9_relat_1(k7_relat_1(esk3_0,X1),k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k10_relat_1(esk3_0,k2_relat_1(k7_relat_1(esk3_0,X1)))))) = k2_relat_1(k7_relat_1(esk3_0,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_33]),c_0_78]),c_0_91])).

cnf(c_0_109,negated_conjecture,
    ( k1_setfam_1(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,k10_relat_1(esk3_0,k2_relat_1(k7_relat_1(esk3_0,esk2_0))))) = esk2_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_99]),c_0_100]),c_0_101])).

cnf(c_0_110,negated_conjecture,
    ( k9_relat_1(k7_relat_1(esk3_0,X1),X1) = k9_relat_1(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_102,c_0_73])).

cnf(c_0_111,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_103,c_0_96]),c_0_60]),c_0_61]),c_0_62]),c_0_63]),c_0_64])).

cnf(c_0_112,plain,
    ( k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k2_xboole_0(X1,X2))) = X1 ),
    inference(spm,[status(thm)],[c_0_104,c_0_105])).

cnf(c_0_113,negated_conjecture,
    ( k5_xboole_0(esk2_0,k1_setfam_1(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,k10_relat_1(esk3_0,k9_relat_1(esk3_0,esk2_0))))) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_106,c_0_107])).

cnf(c_0_114,negated_conjecture,
    ( k9_relat_1(esk3_0,esk2_0) = k2_relat_1(k7_relat_1(esk3_0,esk2_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_109]),c_0_110])).

cnf(c_0_115,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111,c_0_105]),c_0_112])).

cnf(c_0_116,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_113,c_0_114]),c_0_109]),c_0_115])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:28:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  # Version: 2.5pre002
% 0.19/0.35  # No SInE strategy applied
% 0.19/0.35  # Trying AutoSched0 for 299 seconds
% 0.39/0.58  # AutoSched0-Mode selected heuristic G_E___107_B42_F1_PI_SE_Q4_CS_SP_PS_S0YI
% 0.39/0.58  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.39/0.58  #
% 0.39/0.58  # Preprocessing time       : 0.027 s
% 0.39/0.58  # Presaturation interreduction done
% 0.39/0.58  
% 0.39/0.58  # Proof found!
% 0.39/0.58  # SZS status Theorem
% 0.39/0.58  # SZS output start CNFRefutation
% 0.39/0.58  fof(t146_funct_1, conjecture, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(X1,k1_relat_1(X2))=>r1_tarski(X1,k10_relat_1(X2,k9_relat_1(X2,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_funct_1)).
% 0.39/0.58  fof(t169_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k10_relat_1(X1,k2_relat_1(X1))=k1_relat_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 0.39/0.58  fof(dt_k7_relat_1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k7_relat_1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 0.39/0.58  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.39/0.58  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.39/0.58  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.39/0.58  fof(t182_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>k1_relat_1(k5_relat_1(X1,X2))=k10_relat_1(X1,k1_relat_1(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t182_relat_1)).
% 0.39/0.58  fof(t94_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k7_relat_1(X2,X1)=k5_relat_1(k6_relat_1(X1),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 0.39/0.58  fof(t139_funct_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>k10_relat_1(k7_relat_1(X3,X1),X2)=k3_xboole_0(X1,k10_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t139_funct_1)).
% 0.39/0.58  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.39/0.58  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.39/0.58  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 0.39/0.58  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 0.39/0.58  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 0.39/0.58  fof(t175_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>k10_relat_1(X3,k2_xboole_0(X1,X2))=k2_xboole_0(k10_relat_1(X3,X1),k10_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t175_relat_1)).
% 0.39/0.58  fof(dt_k6_relat_1, axiom, ![X1]:v1_relat_1(k6_relat_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 0.39/0.58  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.39/0.58  fof(t14_xboole_1, axiom, ![X1, X2, X3]:(((r1_tarski(X1,X2)&r1_tarski(X3,X2))&![X4]:((r1_tarski(X1,X4)&r1_tarski(X3,X4))=>r1_tarski(X2,X4)))=>X2=k2_xboole_0(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_xboole_1)).
% 0.39/0.58  fof(t167_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k10_relat_1(X2,X1),k1_relat_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t167_relat_1)).
% 0.39/0.58  fof(t71_relat_1, axiom, ![X1]:(k1_relat_1(k6_relat_1(X1))=X1&k2_relat_1(k6_relat_1(X1))=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 0.39/0.58  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.39/0.58  fof(t146_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k9_relat_1(X1,k1_relat_1(X1))=k2_relat_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 0.39/0.58  fof(t162_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2, X3]:(r1_tarski(X2,X3)=>k9_relat_1(k7_relat_1(X1,X3),X2)=k9_relat_1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t162_relat_1)).
% 0.39/0.58  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.39/0.58  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.39/0.58  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.39/0.58  fof(c_0_26, negated_conjecture, ~(![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(X1,k1_relat_1(X2))=>r1_tarski(X1,k10_relat_1(X2,k9_relat_1(X2,X1)))))), inference(assume_negation,[status(cth)],[t146_funct_1])).
% 0.39/0.58  fof(c_0_27, plain, ![X65]:(~v1_relat_1(X65)|k10_relat_1(X65,k2_relat_1(X65))=k1_relat_1(X65)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t169_relat_1])])).
% 0.39/0.58  fof(c_0_28, negated_conjecture, (v1_relat_1(esk3_0)&(r1_tarski(esk2_0,k1_relat_1(esk3_0))&~r1_tarski(esk2_0,k10_relat_1(esk3_0,k9_relat_1(esk3_0,esk2_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_26])])])).
% 0.39/0.58  fof(c_0_29, plain, ![X57, X58]:(~v1_relat_1(X57)|v1_relat_1(k7_relat_1(X57,X58))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).
% 0.39/0.58  fof(c_0_30, plain, ![X54, X55]:k1_setfam_1(k2_tarski(X54,X55))=k3_xboole_0(X54,X55), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.39/0.58  fof(c_0_31, plain, ![X27, X28]:k1_enumset1(X27,X27,X28)=k2_tarski(X27,X28), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.39/0.58  cnf(c_0_32, plain, (k10_relat_1(X1,k2_relat_1(X1))=k1_relat_1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.39/0.58  cnf(c_0_33, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.39/0.58  fof(c_0_34, plain, ![X8, X9]:(((r1_tarski(X8,X9)|X8!=X9)&(r1_tarski(X9,X8)|X8!=X9))&(~r1_tarski(X8,X9)|~r1_tarski(X9,X8)|X8=X9)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.39/0.58  fof(c_0_35, plain, ![X69, X70]:(~v1_relat_1(X69)|(~v1_relat_1(X70)|k1_relat_1(k5_relat_1(X69,X70))=k10_relat_1(X69,k1_relat_1(X70)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t182_relat_1])])])).
% 0.39/0.58  fof(c_0_36, plain, ![X74, X75]:(~v1_relat_1(X75)|k7_relat_1(X75,X74)=k5_relat_1(k6_relat_1(X74),X75)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).
% 0.39/0.58  cnf(c_0_37, plain, (v1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.39/0.58  fof(c_0_38, plain, ![X76, X77, X78]:(~v1_relat_1(X78)|k10_relat_1(k7_relat_1(X78,X76),X77)=k3_xboole_0(X76,k10_relat_1(X78,X77))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t139_funct_1])])).
% 0.39/0.58  cnf(c_0_39, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.39/0.58  cnf(c_0_40, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.39/0.58  fof(c_0_41, plain, ![X29, X30, X31]:k2_enumset1(X29,X29,X30,X31)=k1_enumset1(X29,X30,X31), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.39/0.58  fof(c_0_42, plain, ![X32, X33, X34, X35]:k3_enumset1(X32,X32,X33,X34,X35)=k2_enumset1(X32,X33,X34,X35), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.39/0.58  fof(c_0_43, plain, ![X36, X37, X38, X39, X40]:k4_enumset1(X36,X36,X37,X38,X39,X40)=k3_enumset1(X36,X37,X38,X39,X40), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.39/0.58  fof(c_0_44, plain, ![X41, X42, X43, X44, X45, X46]:k5_enumset1(X41,X41,X42,X43,X44,X45,X46)=k4_enumset1(X41,X42,X43,X44,X45,X46), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.39/0.58  fof(c_0_45, plain, ![X47, X48, X49, X50, X51, X52, X53]:k6_enumset1(X47,X47,X48,X49,X50,X51,X52,X53)=k5_enumset1(X47,X48,X49,X50,X51,X52,X53), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.39/0.58  fof(c_0_46, plain, ![X66, X67, X68]:(~v1_relat_1(X68)|k10_relat_1(X68,k2_xboole_0(X66,X67))=k2_xboole_0(k10_relat_1(X68,X66),k10_relat_1(X68,X67))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t175_relat_1])])).
% 0.39/0.58  fof(c_0_47, plain, ![X56]:v1_relat_1(k6_relat_1(X56)), inference(variable_rename,[status(thm)],[dt_k6_relat_1])).
% 0.39/0.58  fof(c_0_48, plain, ![X17, X18]:(~r1_tarski(X17,X18)|k2_xboole_0(X17,X18)=X18), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.39/0.58  cnf(c_0_49, negated_conjecture, (r1_tarski(esk2_0,k1_relat_1(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.39/0.58  cnf(c_0_50, negated_conjecture, (k1_relat_1(esk3_0)=k10_relat_1(esk3_0,k2_relat_1(esk3_0))), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.39/0.58  fof(c_0_51, plain, ![X19, X20, X21]:(((r1_tarski(X19,esk1_3(X19,X20,X21))|(~r1_tarski(X19,X20)|~r1_tarski(X21,X20))|X20=k2_xboole_0(X19,X21))&(r1_tarski(X21,esk1_3(X19,X20,X21))|(~r1_tarski(X19,X20)|~r1_tarski(X21,X20))|X20=k2_xboole_0(X19,X21)))&(~r1_tarski(X20,esk1_3(X19,X20,X21))|(~r1_tarski(X19,X20)|~r1_tarski(X21,X20))|X20=k2_xboole_0(X19,X21))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t14_xboole_1])])])])).
% 0.39/0.58  cnf(c_0_52, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.39/0.58  fof(c_0_53, plain, ![X63, X64]:(~v1_relat_1(X64)|r1_tarski(k10_relat_1(X64,X63),k1_relat_1(X64))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t167_relat_1])])).
% 0.39/0.58  fof(c_0_54, plain, ![X71]:(k1_relat_1(k6_relat_1(X71))=X71&k2_relat_1(k6_relat_1(X71))=X71), inference(variable_rename,[status(thm)],[t71_relat_1])).
% 0.39/0.58  cnf(c_0_55, plain, (k1_relat_1(k5_relat_1(X1,X2))=k10_relat_1(X1,k1_relat_1(X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.39/0.58  cnf(c_0_56, plain, (k7_relat_1(X1,X2)=k5_relat_1(k6_relat_1(X2),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.39/0.58  cnf(c_0_57, plain, (k1_relat_1(k7_relat_1(X1,X2))=k10_relat_1(k7_relat_1(X1,X2),k2_relat_1(k7_relat_1(X1,X2)))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_32, c_0_37])).
% 0.39/0.58  cnf(c_0_58, plain, (k10_relat_1(k7_relat_1(X1,X2),X3)=k3_xboole_0(X2,k10_relat_1(X1,X3))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.39/0.58  cnf(c_0_59, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_39, c_0_40])).
% 0.39/0.58  cnf(c_0_60, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.39/0.58  cnf(c_0_61, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.39/0.58  cnf(c_0_62, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.39/0.58  cnf(c_0_63, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.39/0.58  cnf(c_0_64, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.39/0.58  fof(c_0_65, plain, ![X12, X13]:k4_xboole_0(X12,X13)=k5_xboole_0(X12,k3_xboole_0(X12,X13)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.39/0.58  fof(c_0_66, plain, ![X59]:(~v1_relat_1(X59)|k9_relat_1(X59,k1_relat_1(X59))=k2_relat_1(X59)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_relat_1])])).
% 0.39/0.58  cnf(c_0_67, plain, (k10_relat_1(X1,k2_xboole_0(X2,X3))=k2_xboole_0(k10_relat_1(X1,X2),k10_relat_1(X1,X3))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.39/0.58  cnf(c_0_68, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.39/0.58  cnf(c_0_69, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.39/0.58  cnf(c_0_70, negated_conjecture, (r1_tarski(esk2_0,k10_relat_1(esk3_0,k2_relat_1(esk3_0)))), inference(rw,[status(thm)],[c_0_49, c_0_50])).
% 0.39/0.58  cnf(c_0_71, plain, (X1=k2_xboole_0(X2,X3)|~r1_tarski(X1,esk1_3(X2,X1,X3))|~r1_tarski(X2,X1)|~r1_tarski(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.39/0.58  cnf(c_0_72, plain, (r1_tarski(X1,esk1_3(X1,X2,X3))|X2=k2_xboole_0(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.39/0.58  cnf(c_0_73, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_52])).
% 0.39/0.58  cnf(c_0_74, plain, (r1_tarski(k10_relat_1(X1,X2),k1_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.39/0.58  cnf(c_0_75, plain, (k1_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.39/0.58  cnf(c_0_76, negated_conjecture, (k1_relat_1(k5_relat_1(X1,esk3_0))=k10_relat_1(X1,k10_relat_1(esk3_0,k2_relat_1(esk3_0)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_33]), c_0_50])).
% 0.39/0.58  cnf(c_0_77, negated_conjecture, (k5_relat_1(k6_relat_1(X1),esk3_0)=k7_relat_1(esk3_0,X1)), inference(spm,[status(thm)],[c_0_56, c_0_33])).
% 0.39/0.58  cnf(c_0_78, negated_conjecture, (k1_relat_1(k7_relat_1(esk3_0,X1))=k10_relat_1(k7_relat_1(esk3_0,X1),k2_relat_1(k7_relat_1(esk3_0,X1)))), inference(spm,[status(thm)],[c_0_57, c_0_33])).
% 0.39/0.58  cnf(c_0_79, plain, (k10_relat_1(k7_relat_1(X1,X2),X3)=k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,k10_relat_1(X1,X3)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58, c_0_59]), c_0_60]), c_0_61]), c_0_62]), c_0_63]), c_0_64])).
% 0.39/0.58  fof(c_0_80, plain, ![X60, X61, X62]:(~v1_relat_1(X60)|(~r1_tarski(X61,X62)|k9_relat_1(k7_relat_1(X60,X62),X61)=k9_relat_1(X60,X61))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t162_relat_1])])])).
% 0.39/0.58  fof(c_0_81, plain, ![X23, X24]:(~r1_tarski(X23,X24)|k3_xboole_0(X23,X24)=X23), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.39/0.58  fof(c_0_82, plain, ![X10, X11]:((k4_xboole_0(X10,X11)!=k1_xboole_0|r1_tarski(X10,X11))&(~r1_tarski(X10,X11)|k4_xboole_0(X10,X11)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.39/0.58  cnf(c_0_83, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.39/0.58  cnf(c_0_84, plain, (k9_relat_1(X1,k1_relat_1(X1))=k2_relat_1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_66])).
% 0.39/0.58  cnf(c_0_85, plain, (k10_relat_1(k6_relat_1(X1),k2_xboole_0(X2,X3))=k2_xboole_0(k10_relat_1(k6_relat_1(X1),X2),k10_relat_1(k6_relat_1(X1),X3))), inference(spm,[status(thm)],[c_0_67, c_0_68])).
% 0.39/0.58  cnf(c_0_86, negated_conjecture, (k2_xboole_0(esk2_0,k10_relat_1(esk3_0,k2_relat_1(esk3_0)))=k10_relat_1(esk3_0,k2_relat_1(esk3_0))), inference(spm,[status(thm)],[c_0_69, c_0_70])).
% 0.39/0.58  cnf(c_0_87, plain, (k2_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.39/0.58  cnf(c_0_88, plain, (k2_xboole_0(X1,X2)=X1|~r1_tarski(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_73])])).
% 0.39/0.58  cnf(c_0_89, plain, (r1_tarski(k10_relat_1(k6_relat_1(X1),X2),X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_68]), c_0_75])).
% 0.39/0.58  cnf(c_0_90, negated_conjecture, (k10_relat_1(k7_relat_1(esk3_0,X1),k2_relat_1(k7_relat_1(esk3_0,X1)))=k10_relat_1(k6_relat_1(X1),k10_relat_1(esk3_0,k2_relat_1(esk3_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_68]), c_0_77]), c_0_78])).
% 0.39/0.58  cnf(c_0_91, negated_conjecture, (k10_relat_1(k7_relat_1(esk3_0,X1),X2)=k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k10_relat_1(esk3_0,X2)))), inference(spm,[status(thm)],[c_0_79, c_0_33])).
% 0.39/0.58  cnf(c_0_92, plain, (k9_relat_1(k7_relat_1(X1,X3),X2)=k9_relat_1(X1,X2)|~v1_relat_1(X1)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_80])).
% 0.39/0.58  cnf(c_0_93, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_81])).
% 0.39/0.58  fof(c_0_94, plain, ![X25, X26]:r1_tarski(X25,k2_xboole_0(X25,X26)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.39/0.58  cnf(c_0_95, plain, (r1_tarski(X1,X2)|k4_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_82])).
% 0.39/0.58  cnf(c_0_96, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2)))), inference(rw,[status(thm)],[c_0_83, c_0_59])).
% 0.39/0.58  cnf(c_0_97, plain, (k9_relat_1(k7_relat_1(X1,X2),k1_relat_1(k7_relat_1(X1,X2)))=k2_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_84, c_0_37])).
% 0.39/0.58  cnf(c_0_98, negated_conjecture, (k2_xboole_0(k10_relat_1(k6_relat_1(X1),esk2_0),k10_relat_1(k6_relat_1(X1),k10_relat_1(esk3_0,k2_relat_1(esk3_0))))=k10_relat_1(k6_relat_1(X1),k10_relat_1(esk3_0,k2_relat_1(esk3_0)))), inference(spm,[status(thm)],[c_0_85, c_0_86])).
% 0.39/0.58  cnf(c_0_99, plain, (k10_relat_1(k6_relat_1(X1),X1)=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_68]), c_0_75]), c_0_87])).
% 0.39/0.58  cnf(c_0_100, plain, (k2_xboole_0(X1,k10_relat_1(k6_relat_1(X1),X2))=X1), inference(spm,[status(thm)],[c_0_88, c_0_89])).
% 0.39/0.58  cnf(c_0_101, negated_conjecture, (k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k10_relat_1(esk3_0,k2_relat_1(k7_relat_1(esk3_0,X1)))))=k10_relat_1(k6_relat_1(X1),k10_relat_1(esk3_0,k2_relat_1(esk3_0)))), inference(rw,[status(thm)],[c_0_90, c_0_91])).
% 0.39/0.58  cnf(c_0_102, negated_conjecture, (k9_relat_1(k7_relat_1(esk3_0,X1),X2)=k9_relat_1(esk3_0,X2)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_92, c_0_33])).
% 0.39/0.58  cnf(c_0_103, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_82])).
% 0.39/0.58  cnf(c_0_104, plain, (k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))=X1|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_93, c_0_59]), c_0_60]), c_0_61]), c_0_62]), c_0_63]), c_0_64])).
% 0.39/0.58  cnf(c_0_105, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_94])).
% 0.39/0.58  cnf(c_0_106, negated_conjecture, (~r1_tarski(esk2_0,k10_relat_1(esk3_0,k9_relat_1(esk3_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.39/0.58  cnf(c_0_107, plain, (r1_tarski(X1,X2)|k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))!=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_95, c_0_96]), c_0_60]), c_0_61]), c_0_62]), c_0_63]), c_0_64])).
% 0.39/0.58  cnf(c_0_108, negated_conjecture, (k9_relat_1(k7_relat_1(esk3_0,X1),k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k10_relat_1(esk3_0,k2_relat_1(k7_relat_1(esk3_0,X1))))))=k2_relat_1(k7_relat_1(esk3_0,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97, c_0_33]), c_0_78]), c_0_91])).
% 0.39/0.58  cnf(c_0_109, negated_conjecture, (k1_setfam_1(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,k10_relat_1(esk3_0,k2_relat_1(k7_relat_1(esk3_0,esk2_0)))))=esk2_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_99]), c_0_100]), c_0_101])).
% 0.39/0.58  cnf(c_0_110, negated_conjecture, (k9_relat_1(k7_relat_1(esk3_0,X1),X1)=k9_relat_1(esk3_0,X1)), inference(spm,[status(thm)],[c_0_102, c_0_73])).
% 0.39/0.58  cnf(c_0_111, plain, (k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))=k1_xboole_0|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_103, c_0_96]), c_0_60]), c_0_61]), c_0_62]), c_0_63]), c_0_64])).
% 0.39/0.58  cnf(c_0_112, plain, (k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k2_xboole_0(X1,X2)))=X1), inference(spm,[status(thm)],[c_0_104, c_0_105])).
% 0.39/0.58  cnf(c_0_113, negated_conjecture, (k5_xboole_0(esk2_0,k1_setfam_1(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,k10_relat_1(esk3_0,k9_relat_1(esk3_0,esk2_0)))))!=k1_xboole_0), inference(spm,[status(thm)],[c_0_106, c_0_107])).
% 0.39/0.58  cnf(c_0_114, negated_conjecture, (k9_relat_1(esk3_0,esk2_0)=k2_relat_1(k7_relat_1(esk3_0,esk2_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108, c_0_109]), c_0_110])).
% 0.39/0.58  cnf(c_0_115, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111, c_0_105]), c_0_112])).
% 0.39/0.58  cnf(c_0_116, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_113, c_0_114]), c_0_109]), c_0_115])]), ['proof']).
% 0.39/0.58  # SZS output end CNFRefutation
% 0.39/0.58  # Proof object total steps             : 117
% 0.39/0.58  # Proof object clause steps            : 64
% 0.39/0.58  # Proof object formula steps           : 53
% 0.39/0.58  # Proof object conjectures             : 23
% 0.39/0.58  # Proof object clause conjectures      : 20
% 0.39/0.58  # Proof object formula conjectures     : 3
% 0.39/0.58  # Proof object initial clauses used    : 31
% 0.39/0.58  # Proof object initial formulas used   : 26
% 0.39/0.58  # Proof object generating inferences   : 23
% 0.39/0.58  # Proof object simplifying inferences  : 47
% 0.39/0.58  # Training examples: 0 positive, 0 negative
% 0.39/0.58  # Parsed axioms                        : 28
% 0.39/0.58  # Removed by relevancy pruning/SinE    : 0
% 0.39/0.58  # Initial clauses                      : 36
% 0.39/0.58  # Removed in clause preprocessing      : 8
% 0.39/0.58  # Initial clauses in saturation        : 28
% 0.39/0.58  # Processed clauses                    : 1734
% 0.39/0.58  # ...of these trivial                  : 91
% 0.39/0.58  # ...subsumed                          : 1116
% 0.39/0.58  # ...remaining for further processing  : 527
% 0.39/0.58  # Other redundant clauses eliminated   : 2
% 0.39/0.58  # Clauses deleted for lack of memory   : 0
% 0.39/0.58  # Backward-subsumed                    : 0
% 0.39/0.58  # Backward-rewritten                   : 81
% 0.39/0.58  # Generated clauses                    : 17002
% 0.39/0.58  # ...of the previous two non-trivial   : 13261
% 0.39/0.58  # Contextual simplify-reflections      : 0
% 0.39/0.58  # Paramodulations                      : 17000
% 0.39/0.58  # Factorizations                       : 0
% 0.39/0.58  # Equation resolutions                 : 2
% 0.39/0.58  # Propositional unsat checks           : 0
% 0.39/0.58  #    Propositional check models        : 0
% 0.39/0.58  #    Propositional check unsatisfiable : 0
% 0.39/0.58  #    Propositional clauses             : 0
% 0.39/0.58  #    Propositional clauses after purity: 0
% 0.39/0.58  #    Propositional unsat core size     : 0
% 0.39/0.58  #    Propositional preprocessing time  : 0.000
% 0.39/0.58  #    Propositional encoding time       : 0.000
% 0.39/0.58  #    Propositional solver time         : 0.000
% 0.39/0.58  #    Success case prop preproc time    : 0.000
% 0.39/0.58  #    Success case prop encoding time   : 0.000
% 0.39/0.58  #    Success case prop solver time     : 0.000
% 0.39/0.58  # Current number of processed clauses  : 417
% 0.39/0.58  #    Positive orientable unit clauses  : 211
% 0.39/0.58  #    Positive unorientable unit clauses: 2
% 0.39/0.58  #    Negative unit clauses             : 0
% 0.39/0.58  #    Non-unit-clauses                  : 204
% 0.39/0.58  # Current number of unprocessed clauses: 11234
% 0.39/0.58  # ...number of literals in the above   : 19366
% 0.39/0.58  # Current number of archived formulas  : 0
% 0.39/0.58  # Current number of archived clauses   : 116
% 0.39/0.58  # Clause-clause subsumption calls (NU) : 8267
% 0.39/0.58  # Rec. Clause-clause subsumption calls : 5410
% 0.39/0.58  # Non-unit clause-clause subsumptions  : 580
% 0.39/0.58  # Unit Clause-clause subsumption calls : 168
% 0.39/0.58  # Rewrite failures with RHS unbound    : 0
% 0.39/0.58  # BW rewrite match attempts            : 1050
% 0.39/0.58  # BW rewrite match successes           : 61
% 0.39/0.58  # Condensation attempts                : 0
% 0.39/0.58  # Condensation successes               : 0
% 0.39/0.58  # Termbank termtop insertions          : 431951
% 0.39/0.58  
% 0.39/0.58  # -------------------------------------------------
% 0.39/0.58  # User time                : 0.219 s
% 0.39/0.58  # System time              : 0.014 s
% 0.39/0.58  # Total time               : 0.233 s
% 0.39/0.58  # Maximum resident set size: 1600 pages
%------------------------------------------------------------------------------
