%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:50:11 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 442 expanded)
%              Number of clauses        :   53 ( 181 expanded)
%              Number of leaves         :   23 ( 127 expanded)
%              Depth                    :   10
%              Number of atoms          :  152 ( 538 expanded)
%              Number of equality atoms :   67 ( 383 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t124_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k8_relat_1(X1,X2) = k3_xboole_0(X2,k2_zfmisc_1(k1_relat_1(X2),X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t124_relat_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(t81_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_enumset1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(t47_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(t131_relat_1,conjecture,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r1_tarski(X1,X2)
       => r1_tarski(k8_relat_1(X1,X3),k8_relat_1(X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t131_relat_1)).

fof(t93_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t93_zfmisc_1)).

fof(t127_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => k8_relat_1(X1,k8_relat_1(X2,X3)) = k8_relat_1(k3_xboole_0(X1,X2),X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t127_relat_1)).

fof(t63_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_xboole_0(X2,X3) )
     => r1_xboole_0(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(t79_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(t101_xboole_1,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k4_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t101_xboole_1)).

fof(fc2_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_relat_1)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(t5_boole,axiom,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(t123_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k8_relat_1(X1,X2) = k5_relat_1(X2,k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).

fof(t76_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k5_relat_1(X2,k6_relat_1(X1)),X2)
        & r1_tarski(k5_relat_1(k6_relat_1(X1),X2),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_relat_1)).

fof(c_0_23,plain,(
    ! [X55,X56] : k1_setfam_1(k2_tarski(X55,X56)) = k3_xboole_0(X55,X56) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_24,plain,(
    ! [X32,X33] : k1_enumset1(X32,X32,X33) = k2_tarski(X32,X33) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_25,plain,(
    ! [X61,X62] :
      ( ~ v1_relat_1(X62)
      | k8_relat_1(X61,X62) = k3_xboole_0(X62,k2_zfmisc_1(k1_relat_1(X62),X61)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t124_relat_1])])).

cnf(c_0_26,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_27,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_28,plain,(
    ! [X34,X35,X36] : k2_enumset1(X34,X34,X35,X36) = k1_enumset1(X34,X35,X36) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_29,plain,(
    ! [X37,X38,X39,X40] : k3_enumset1(X37,X37,X38,X39,X40) = k2_enumset1(X37,X38,X39,X40) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_30,plain,(
    ! [X41,X42,X43,X44,X45] : k4_enumset1(X41,X41,X42,X43,X44,X45) = k3_enumset1(X41,X42,X43,X44,X45) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_31,plain,(
    ! [X46,X47,X48,X49,X50,X51] : k6_enumset1(X46,X46,X46,X47,X48,X49,X50,X51) = k4_enumset1(X46,X47,X48,X49,X50,X51) ),
    inference(variable_rename,[status(thm)],[t81_enumset1])).

fof(c_0_32,plain,(
    ! [X22,X23] : k4_xboole_0(X22,k4_xboole_0(X22,X23)) = k3_xboole_0(X22,X23) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_33,plain,(
    ! [X9,X10,X12,X13,X14] :
      ( ( r1_xboole_0(X9,X10)
        | r2_hidden(esk1_2(X9,X10),k3_xboole_0(X9,X10)) )
      & ( ~ r2_hidden(X14,k3_xboole_0(X12,X13))
        | ~ r1_xboole_0(X12,X13) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

fof(c_0_34,plain,(
    ! [X20,X21] : k4_xboole_0(X20,k3_xboole_0(X20,X21)) = k4_xboole_0(X20,X21) ),
    inference(variable_rename,[status(thm)],[t47_xboole_1])).

cnf(c_0_35,plain,
    ( k8_relat_1(X2,X1) = k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_36,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_37,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_38,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_39,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_40,plain,
    ( k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_41,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_42,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( v1_relat_1(X3)
       => ( r1_tarski(X1,X2)
         => r1_tarski(k8_relat_1(X1,X3),k8_relat_1(X2,X3)) ) ) ),
    inference(assume_negation,[status(cth)],[t131_relat_1])).

cnf(c_0_43,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_44,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

fof(c_0_45,plain,(
    ! [X53,X54] : k3_tarski(k2_tarski(X53,X54)) = k2_xboole_0(X53,X54) ),
    inference(variable_rename,[status(thm)],[t93_zfmisc_1])).

cnf(c_0_46,plain,
    ( k8_relat_1(X2,X1) = k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k2_zfmisc_1(k1_relat_1(X1),X2)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_36]),c_0_37]),c_0_38]),c_0_39]),c_0_40])).

cnf(c_0_47,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_36]),c_0_37]),c_0_38]),c_0_39]),c_0_40])).

fof(c_0_48,negated_conjecture,
    ( v1_relat_1(esk5_0)
    & r1_tarski(esk3_0,esk4_0)
    & ~ r1_tarski(k8_relat_1(esk3_0,esk5_0),k8_relat_1(esk4_0,esk5_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_42])])])).

fof(c_0_49,plain,(
    ! [X63,X64,X65] :
      ( ~ v1_relat_1(X65)
      | k8_relat_1(X63,k8_relat_1(X64,X65)) = k8_relat_1(k3_xboole_0(X63,X64),X65) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t127_relat_1])])).

cnf(c_0_50,plain,
    ( ~ r1_xboole_0(X2,X3)
    | ~ r2_hidden(X1,k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_36]),c_0_37]),c_0_38]),c_0_39]),c_0_40])).

cnf(c_0_51,plain,
    ( k4_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44,c_0_36]),c_0_37]),c_0_38]),c_0_39]),c_0_40])).

fof(c_0_52,plain,(
    ! [X25,X26,X27] :
      ( ~ r1_tarski(X25,X26)
      | ~ r1_xboole_0(X26,X27)
      | r1_xboole_0(X25,X27) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_xboole_1])])).

fof(c_0_53,plain,(
    ! [X7,X8] :
      ( ~ r1_xboole_0(X7,X8)
      | r1_xboole_0(X8,X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

fof(c_0_54,plain,(
    ! [X28,X29] : r1_xboole_0(k4_xboole_0(X28,X29),X29) ),
    inference(variable_rename,[status(thm)],[t79_xboole_1])).

fof(c_0_55,plain,(
    ! [X17,X18] : k5_xboole_0(X17,X18) = k4_xboole_0(k2_xboole_0(X17,X18),k3_xboole_0(X17,X18)) ),
    inference(variable_rename,[status(thm)],[t101_xboole_1])).

cnf(c_0_56,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

fof(c_0_57,plain,(
    ! [X57,X58] :
      ( ~ v1_relat_1(X57)
      | v1_relat_1(k4_xboole_0(X57,X58)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc2_relat_1])])).

cnf(c_0_58,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X2))) = k8_relat_1(X2,X1)
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_59,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_60,plain,
    ( k8_relat_1(X2,k8_relat_1(X3,X1)) = k8_relat_1(k3_xboole_0(X2,X3),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_61,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))
    | ~ r1_xboole_0(X2,X3) ),
    inference(rw,[status(thm)],[c_0_50,c_0_47])).

cnf(c_0_62,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_51,c_0_47])).

fof(c_0_63,plain,(
    ! [X15] :
      ( X15 = k1_xboole_0
      | r2_hidden(esk2_1(X15),X15) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

cnf(c_0_64,plain,
    ( r1_xboole_0(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_65,negated_conjecture,
    ( r1_tarski(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_66,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_67,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

fof(c_0_68,plain,(
    ! [X24] : k5_xboole_0(X24,k1_xboole_0) = X24 ),
    inference(variable_rename,[status(thm)],[t5_boole])).

cnf(c_0_69,plain,
    ( k5_xboole_0(X1,X2) = k4_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_70,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_56,c_0_27])).

fof(c_0_71,plain,(
    ! [X19] : k2_xboole_0(X19,k1_xboole_0) = X19 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

fof(c_0_72,plain,(
    ! [X59,X60] :
      ( ~ v1_relat_1(X60)
      | k8_relat_1(X59,X60) = k5_relat_1(X60,k6_relat_1(X59)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t123_relat_1])])).

cnf(c_0_73,plain,
    ( v1_relat_1(k4_xboole_0(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_74,negated_conjecture,
    ( k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,k2_zfmisc_1(k1_relat_1(esk5_0),X1))) = k8_relat_1(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_75,plain,
    ( k8_relat_1(X2,k8_relat_1(X3,X1)) = k8_relat_1(k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)),X1)
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_60,c_0_36]),c_0_37]),c_0_38]),c_0_39]),c_0_40])).

cnf(c_0_76,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,k4_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_77,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk2_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_78,negated_conjecture,
    ( r1_xboole_0(esk3_0,X1)
    | ~ r1_xboole_0(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_79,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_80,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_81,plain,
    ( k5_xboole_0(X1,X2) = k4_xboole_0(k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)),k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_69,c_0_70]),c_0_36]),c_0_37]),c_0_37]),c_0_38]),c_0_38])).

cnf(c_0_82,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

fof(c_0_83,plain,(
    ! [X66,X67] :
      ( ( r1_tarski(k5_relat_1(X67,k6_relat_1(X66)),X67)
        | ~ v1_relat_1(X67) )
      & ( r1_tarski(k5_relat_1(k6_relat_1(X66),X67),X67)
        | ~ v1_relat_1(X67) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t76_relat_1])])])).

cnf(c_0_84,plain,
    ( k8_relat_1(X2,X1) = k5_relat_1(X1,k6_relat_1(X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_85,negated_conjecture,
    ( v1_relat_1(k8_relat_1(X1,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_59])])).

cnf(c_0_86,plain,
    ( k8_relat_1(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3) = k8_relat_1(X1,k8_relat_1(X2,X3))
    | ~ v1_relat_1(X3) ),
    inference(rw,[status(thm)],[c_0_75,c_0_47])).

cnf(c_0_87,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,k4_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_76,c_0_77])).

cnf(c_0_88,negated_conjecture,
    ( r1_xboole_0(esk3_0,k4_xboole_0(X1,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_78,c_0_79])).

cnf(c_0_89,plain,
    ( k4_xboole_0(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k1_xboole_0)),k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k1_xboole_0))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_80,c_0_81]),c_0_39]),c_0_39]),c_0_40]),c_0_40])).

cnf(c_0_90,plain,
    ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k1_xboole_0)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_82,c_0_70]),c_0_37]),c_0_38]),c_0_39]),c_0_40])).

cnf(c_0_91,plain,
    ( r1_tarski(k5_relat_1(X1,k6_relat_1(X2)),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_83])).

cnf(c_0_92,negated_conjecture,
    ( k5_relat_1(k8_relat_1(X1,esk5_0),k6_relat_1(X2)) = k8_relat_1(X2,k8_relat_1(X1,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_84,c_0_85])).

cnf(c_0_93,negated_conjecture,
    ( k8_relat_1(k4_xboole_0(X1,k4_xboole_0(X1,X2)),esk5_0) = k8_relat_1(X1,k8_relat_1(X2,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_86,c_0_59])).

cnf(c_0_94,negated_conjecture,
    ( k4_xboole_0(esk3_0,esk4_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_87,c_0_88])).

cnf(c_0_95,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_89,c_0_90]),c_0_47]),c_0_62])).

cnf(c_0_96,negated_conjecture,
    ( r1_tarski(k8_relat_1(X1,k8_relat_1(X2,esk5_0)),k8_relat_1(X2,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_92]),c_0_85])])).

cnf(c_0_97,negated_conjecture,
    ( k8_relat_1(esk3_0,k8_relat_1(esk4_0,esk5_0)) = k8_relat_1(esk3_0,esk5_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_94]),c_0_95])).

cnf(c_0_98,negated_conjecture,
    ( ~ r1_tarski(k8_relat_1(esk3_0,esk5_0),k8_relat_1(esk4_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_99,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_97]),c_0_98]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:31:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.40  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S032I
% 0.19/0.40  # and selection function SelectUnlessUniqMax.
% 0.19/0.40  #
% 0.19/0.40  # Preprocessing time       : 0.027 s
% 0.19/0.40  # Presaturation interreduction done
% 0.19/0.40  
% 0.19/0.40  # Proof found!
% 0.19/0.40  # SZS status Theorem
% 0.19/0.40  # SZS output start CNFRefutation
% 0.19/0.40  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.19/0.40  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.19/0.40  fof(t124_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k8_relat_1(X1,X2)=k3_xboole_0(X2,k2_zfmisc_1(k1_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t124_relat_1)).
% 0.19/0.40  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.19/0.40  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.19/0.40  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 0.19/0.40  fof(t81_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_enumset1)).
% 0.19/0.40  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.19/0.40  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 0.19/0.40  fof(t47_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 0.19/0.40  fof(t131_relat_1, conjecture, ![X1, X2, X3]:(v1_relat_1(X3)=>(r1_tarski(X1,X2)=>r1_tarski(k8_relat_1(X1,X3),k8_relat_1(X2,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t131_relat_1)).
% 0.19/0.40  fof(t93_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t93_zfmisc_1)).
% 0.19/0.40  fof(t127_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>k8_relat_1(X1,k8_relat_1(X2,X3))=k8_relat_1(k3_xboole_0(X1,X2),X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t127_relat_1)).
% 0.19/0.40  fof(t63_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_xboole_0(X2,X3))=>r1_xboole_0(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 0.19/0.40  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 0.19/0.40  fof(t79_xboole_1, axiom, ![X1, X2]:r1_xboole_0(k4_xboole_0(X1,X2),X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 0.19/0.40  fof(t101_xboole_1, axiom, ![X1, X2]:k5_xboole_0(X1,X2)=k4_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t101_xboole_1)).
% 0.19/0.40  fof(fc2_relat_1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k4_xboole_0(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_relat_1)).
% 0.19/0.40  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 0.19/0.40  fof(t5_boole, axiom, ![X1]:k5_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 0.19/0.40  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 0.19/0.40  fof(t123_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k8_relat_1(X1,X2)=k5_relat_1(X2,k6_relat_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_relat_1)).
% 0.19/0.40  fof(t76_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k5_relat_1(X2,k6_relat_1(X1)),X2)&r1_tarski(k5_relat_1(k6_relat_1(X1),X2),X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_relat_1)).
% 0.19/0.40  fof(c_0_23, plain, ![X55, X56]:k1_setfam_1(k2_tarski(X55,X56))=k3_xboole_0(X55,X56), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.19/0.40  fof(c_0_24, plain, ![X32, X33]:k1_enumset1(X32,X32,X33)=k2_tarski(X32,X33), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.19/0.40  fof(c_0_25, plain, ![X61, X62]:(~v1_relat_1(X62)|k8_relat_1(X61,X62)=k3_xboole_0(X62,k2_zfmisc_1(k1_relat_1(X62),X61))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t124_relat_1])])).
% 0.19/0.40  cnf(c_0_26, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.40  cnf(c_0_27, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.40  fof(c_0_28, plain, ![X34, X35, X36]:k2_enumset1(X34,X34,X35,X36)=k1_enumset1(X34,X35,X36), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.19/0.40  fof(c_0_29, plain, ![X37, X38, X39, X40]:k3_enumset1(X37,X37,X38,X39,X40)=k2_enumset1(X37,X38,X39,X40), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.19/0.40  fof(c_0_30, plain, ![X41, X42, X43, X44, X45]:k4_enumset1(X41,X41,X42,X43,X44,X45)=k3_enumset1(X41,X42,X43,X44,X45), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.19/0.40  fof(c_0_31, plain, ![X46, X47, X48, X49, X50, X51]:k6_enumset1(X46,X46,X46,X47,X48,X49,X50,X51)=k4_enumset1(X46,X47,X48,X49,X50,X51), inference(variable_rename,[status(thm)],[t81_enumset1])).
% 0.19/0.40  fof(c_0_32, plain, ![X22, X23]:k4_xboole_0(X22,k4_xboole_0(X22,X23))=k3_xboole_0(X22,X23), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.19/0.40  fof(c_0_33, plain, ![X9, X10, X12, X13, X14]:((r1_xboole_0(X9,X10)|r2_hidden(esk1_2(X9,X10),k3_xboole_0(X9,X10)))&(~r2_hidden(X14,k3_xboole_0(X12,X13))|~r1_xboole_0(X12,X13))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 0.19/0.40  fof(c_0_34, plain, ![X20, X21]:k4_xboole_0(X20,k3_xboole_0(X20,X21))=k4_xboole_0(X20,X21), inference(variable_rename,[status(thm)],[t47_xboole_1])).
% 0.19/0.40  cnf(c_0_35, plain, (k8_relat_1(X2,X1)=k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.40  cnf(c_0_36, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_26, c_0_27])).
% 0.19/0.40  cnf(c_0_37, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.40  cnf(c_0_38, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.40  cnf(c_0_39, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.40  cnf(c_0_40, plain, (k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.40  cnf(c_0_41, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.40  fof(c_0_42, negated_conjecture, ~(![X1, X2, X3]:(v1_relat_1(X3)=>(r1_tarski(X1,X2)=>r1_tarski(k8_relat_1(X1,X3),k8_relat_1(X2,X3))))), inference(assume_negation,[status(cth)],[t131_relat_1])).
% 0.19/0.40  cnf(c_0_43, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.40  cnf(c_0_44, plain, (k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.19/0.40  fof(c_0_45, plain, ![X53, X54]:k3_tarski(k2_tarski(X53,X54))=k2_xboole_0(X53,X54), inference(variable_rename,[status(thm)],[t93_zfmisc_1])).
% 0.19/0.40  cnf(c_0_46, plain, (k8_relat_1(X2,X1)=k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k2_zfmisc_1(k1_relat_1(X1),X2)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_36]), c_0_37]), c_0_38]), c_0_39]), c_0_40])).
% 0.19/0.40  cnf(c_0_47, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_36]), c_0_37]), c_0_38]), c_0_39]), c_0_40])).
% 0.19/0.40  fof(c_0_48, negated_conjecture, (v1_relat_1(esk5_0)&(r1_tarski(esk3_0,esk4_0)&~r1_tarski(k8_relat_1(esk3_0,esk5_0),k8_relat_1(esk4_0,esk5_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_42])])])).
% 0.19/0.40  fof(c_0_49, plain, ![X63, X64, X65]:(~v1_relat_1(X65)|k8_relat_1(X63,k8_relat_1(X64,X65))=k8_relat_1(k3_xboole_0(X63,X64),X65)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t127_relat_1])])).
% 0.19/0.40  cnf(c_0_50, plain, (~r1_xboole_0(X2,X3)|~r2_hidden(X1,k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43, c_0_36]), c_0_37]), c_0_38]), c_0_39]), c_0_40])).
% 0.19/0.40  cnf(c_0_51, plain, (k4_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44, c_0_36]), c_0_37]), c_0_38]), c_0_39]), c_0_40])).
% 0.19/0.40  fof(c_0_52, plain, ![X25, X26, X27]:(~r1_tarski(X25,X26)|~r1_xboole_0(X26,X27)|r1_xboole_0(X25,X27)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_xboole_1])])).
% 0.19/0.40  fof(c_0_53, plain, ![X7, X8]:(~r1_xboole_0(X7,X8)|r1_xboole_0(X8,X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 0.19/0.40  fof(c_0_54, plain, ![X28, X29]:r1_xboole_0(k4_xboole_0(X28,X29),X29), inference(variable_rename,[status(thm)],[t79_xboole_1])).
% 0.19/0.40  fof(c_0_55, plain, ![X17, X18]:k5_xboole_0(X17,X18)=k4_xboole_0(k2_xboole_0(X17,X18),k3_xboole_0(X17,X18)), inference(variable_rename,[status(thm)],[t101_xboole_1])).
% 0.19/0.40  cnf(c_0_56, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.19/0.40  fof(c_0_57, plain, ![X57, X58]:(~v1_relat_1(X57)|v1_relat_1(k4_xboole_0(X57,X58))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc2_relat_1])])).
% 0.19/0.40  cnf(c_0_58, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X2)))=k8_relat_1(X2,X1)|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_46, c_0_47])).
% 0.19/0.40  cnf(c_0_59, negated_conjecture, (v1_relat_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.19/0.40  cnf(c_0_60, plain, (k8_relat_1(X2,k8_relat_1(X3,X1))=k8_relat_1(k3_xboole_0(X2,X3),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.19/0.40  cnf(c_0_61, plain, (~r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))|~r1_xboole_0(X2,X3)), inference(rw,[status(thm)],[c_0_50, c_0_47])).
% 0.19/0.40  cnf(c_0_62, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2)))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_51, c_0_47])).
% 0.19/0.40  fof(c_0_63, plain, ![X15]:(X15=k1_xboole_0|r2_hidden(esk2_1(X15),X15)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 0.19/0.40  cnf(c_0_64, plain, (r1_xboole_0(X1,X3)|~r1_tarski(X1,X2)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.19/0.40  cnf(c_0_65, negated_conjecture, (r1_tarski(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.19/0.40  cnf(c_0_66, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.19/0.40  cnf(c_0_67, plain, (r1_xboole_0(k4_xboole_0(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.19/0.40  fof(c_0_68, plain, ![X24]:k5_xboole_0(X24,k1_xboole_0)=X24, inference(variable_rename,[status(thm)],[t5_boole])).
% 0.19/0.40  cnf(c_0_69, plain, (k5_xboole_0(X1,X2)=k4_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.19/0.40  cnf(c_0_70, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_56, c_0_27])).
% 0.19/0.40  fof(c_0_71, plain, ![X19]:k2_xboole_0(X19,k1_xboole_0)=X19, inference(variable_rename,[status(thm)],[t1_boole])).
% 0.19/0.40  fof(c_0_72, plain, ![X59, X60]:(~v1_relat_1(X60)|k8_relat_1(X59,X60)=k5_relat_1(X60,k6_relat_1(X59))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t123_relat_1])])).
% 0.19/0.40  cnf(c_0_73, plain, (v1_relat_1(k4_xboole_0(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.19/0.40  cnf(c_0_74, negated_conjecture, (k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,k2_zfmisc_1(k1_relat_1(esk5_0),X1)))=k8_relat_1(X1,esk5_0)), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.19/0.40  cnf(c_0_75, plain, (k8_relat_1(X2,k8_relat_1(X3,X1))=k8_relat_1(k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)),X1)|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_60, c_0_36]), c_0_37]), c_0_38]), c_0_39]), c_0_40])).
% 0.19/0.40  cnf(c_0_76, plain, (~r2_hidden(X1,k4_xboole_0(X2,X3))|~r1_xboole_0(X2,k4_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 0.19/0.40  cnf(c_0_77, plain, (X1=k1_xboole_0|r2_hidden(esk2_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.19/0.40  cnf(c_0_78, negated_conjecture, (r1_xboole_0(esk3_0,X1)|~r1_xboole_0(esk4_0,X1)), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 0.19/0.40  cnf(c_0_79, plain, (r1_xboole_0(X1,k4_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 0.19/0.40  cnf(c_0_80, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.19/0.40  cnf(c_0_81, plain, (k5_xboole_0(X1,X2)=k4_xboole_0(k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)),k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_69, c_0_70]), c_0_36]), c_0_37]), c_0_37]), c_0_38]), c_0_38])).
% 0.19/0.40  cnf(c_0_82, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_71])).
% 0.19/0.40  fof(c_0_83, plain, ![X66, X67]:((r1_tarski(k5_relat_1(X67,k6_relat_1(X66)),X67)|~v1_relat_1(X67))&(r1_tarski(k5_relat_1(k6_relat_1(X66),X67),X67)|~v1_relat_1(X67))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t76_relat_1])])])).
% 0.19/0.40  cnf(c_0_84, plain, (k8_relat_1(X2,X1)=k5_relat_1(X1,k6_relat_1(X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_72])).
% 0.19/0.40  cnf(c_0_85, negated_conjecture, (v1_relat_1(k8_relat_1(X1,esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_59])])).
% 0.19/0.40  cnf(c_0_86, plain, (k8_relat_1(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3)=k8_relat_1(X1,k8_relat_1(X2,X3))|~v1_relat_1(X3)), inference(rw,[status(thm)],[c_0_75, c_0_47])).
% 0.19/0.40  cnf(c_0_87, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,k4_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_76, c_0_77])).
% 0.19/0.40  cnf(c_0_88, negated_conjecture, (r1_xboole_0(esk3_0,k4_xboole_0(X1,esk4_0))), inference(spm,[status(thm)],[c_0_78, c_0_79])).
% 0.19/0.40  cnf(c_0_89, plain, (k4_xboole_0(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k1_xboole_0)),k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k1_xboole_0)))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_80, c_0_81]), c_0_39]), c_0_39]), c_0_40]), c_0_40])).
% 0.19/0.40  cnf(c_0_90, plain, (k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k1_xboole_0))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_82, c_0_70]), c_0_37]), c_0_38]), c_0_39]), c_0_40])).
% 0.19/0.40  cnf(c_0_91, plain, (r1_tarski(k5_relat_1(X1,k6_relat_1(X2)),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_83])).
% 0.19/0.40  cnf(c_0_92, negated_conjecture, (k5_relat_1(k8_relat_1(X1,esk5_0),k6_relat_1(X2))=k8_relat_1(X2,k8_relat_1(X1,esk5_0))), inference(spm,[status(thm)],[c_0_84, c_0_85])).
% 0.19/0.40  cnf(c_0_93, negated_conjecture, (k8_relat_1(k4_xboole_0(X1,k4_xboole_0(X1,X2)),esk5_0)=k8_relat_1(X1,k8_relat_1(X2,esk5_0))), inference(spm,[status(thm)],[c_0_86, c_0_59])).
% 0.19/0.40  cnf(c_0_94, negated_conjecture, (k4_xboole_0(esk3_0,esk4_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_87, c_0_88])).
% 0.19/0.40  cnf(c_0_95, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_89, c_0_90]), c_0_47]), c_0_62])).
% 0.19/0.40  cnf(c_0_96, negated_conjecture, (r1_tarski(k8_relat_1(X1,k8_relat_1(X2,esk5_0)),k8_relat_1(X2,esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_92]), c_0_85])])).
% 0.19/0.40  cnf(c_0_97, negated_conjecture, (k8_relat_1(esk3_0,k8_relat_1(esk4_0,esk5_0))=k8_relat_1(esk3_0,esk5_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_94]), c_0_95])).
% 0.19/0.40  cnf(c_0_98, negated_conjecture, (~r1_tarski(k8_relat_1(esk3_0,esk5_0),k8_relat_1(esk4_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.19/0.40  cnf(c_0_99, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_97]), c_0_98]), ['proof']).
% 0.19/0.40  # SZS output end CNFRefutation
% 0.19/0.40  # Proof object total steps             : 100
% 0.19/0.40  # Proof object clause steps            : 53
% 0.19/0.40  # Proof object formula steps           : 47
% 0.19/0.40  # Proof object conjectures             : 16
% 0.19/0.40  # Proof object clause conjectures      : 13
% 0.19/0.40  # Proof object formula conjectures     : 3
% 0.19/0.40  # Proof object initial clauses used    : 25
% 0.19/0.40  # Proof object initial formulas used   : 23
% 0.19/0.40  # Proof object generating inferences   : 13
% 0.19/0.40  # Proof object simplifying inferences  : 56
% 0.19/0.40  # Training examples: 0 positive, 0 negative
% 0.19/0.40  # Parsed axioms                        : 26
% 0.19/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.40  # Initial clauses                      : 30
% 0.19/0.40  # Removed in clause preprocessing      : 9
% 0.19/0.40  # Initial clauses in saturation        : 21
% 0.19/0.40  # Processed clauses                    : 502
% 0.19/0.40  # ...of these trivial                  : 21
% 0.19/0.40  # ...subsumed                          : 277
% 0.19/0.40  # ...remaining for further processing  : 204
% 0.19/0.40  # Other redundant clauses eliminated   : 0
% 0.19/0.40  # Clauses deleted for lack of memory   : 0
% 0.19/0.40  # Backward-subsumed                    : 1
% 0.19/0.40  # Backward-rewritten                   : 19
% 0.19/0.40  # Generated clauses                    : 1644
% 0.19/0.40  # ...of the previous two non-trivial   : 933
% 0.19/0.40  # Contextual simplify-reflections      : 0
% 0.19/0.40  # Paramodulations                      : 1644
% 0.19/0.40  # Factorizations                       : 0
% 0.19/0.40  # Equation resolutions                 : 0
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
% 0.19/0.40  # Current number of processed clauses  : 163
% 0.19/0.40  #    Positive orientable unit clauses  : 66
% 0.19/0.40  #    Positive unorientable unit clauses: 0
% 0.19/0.40  #    Negative unit clauses             : 2
% 0.19/0.40  #    Non-unit-clauses                  : 95
% 0.19/0.40  # Current number of unprocessed clauses: 447
% 0.19/0.40  # ...number of literals in the above   : 923
% 0.19/0.40  # Current number of archived formulas  : 0
% 0.19/0.40  # Current number of archived clauses   : 50
% 0.19/0.40  # Clause-clause subsumption calls (NU) : 3231
% 0.19/0.40  # Rec. Clause-clause subsumption calls : 2857
% 0.19/0.40  # Non-unit clause-clause subsumptions  : 246
% 0.19/0.40  # Unit Clause-clause subsumption calls : 112
% 0.19/0.40  # Rewrite failures with RHS unbound    : 0
% 0.19/0.40  # BW rewrite match attempts            : 49
% 0.19/0.40  # BW rewrite match successes           : 19
% 0.19/0.40  # Condensation attempts                : 0
% 0.19/0.40  # Condensation successes               : 0
% 0.19/0.40  # Termbank termtop insertions          : 20618
% 0.19/0.40  
% 0.19/0.40  # -------------------------------------------------
% 0.19/0.40  # User time                : 0.048 s
% 0.19/0.40  # System time              : 0.007 s
% 0.19/0.40  # Total time               : 0.056 s
% 0.19/0.40  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
