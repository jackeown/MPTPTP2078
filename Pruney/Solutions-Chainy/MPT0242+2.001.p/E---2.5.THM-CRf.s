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
% DateTime   : Thu Dec  3 10:39:28 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  167 (2886 expanded)
%              Number of clauses        :  106 (1263 expanded)
%              Number of leaves         :   30 ( 810 expanded)
%              Depth                    :   17
%              Number of atoms          :  270 (3105 expanded)
%              Number of equality atoms :  142 (2789 expanded)
%              Maximal formula depth    :   16 (   3 average)
%              Maximal clause size      :   20 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(idempotence_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(d6_xboole_0,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).

fof(t92_xboole_1,axiom,(
    ! [X1] : k5_xboole_0(X1,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(t106_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k4_xboole_0(X2,X3))
     => ( r1_tarski(X1,X2)
        & r1_xboole_0(X1,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(t37_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( r1_tarski(k1_tarski(X1),X2)
    <=> r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_zfmisc_1)).

fof(t57_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_tarski(X1,X2),k3_enumset1(X3,X4,X5,X6,X7)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_enumset1)).

fof(t86_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_enumset1)).

fof(t49_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(t83_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k4_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(t65_xboole_1,axiom,(
    ! [X1] : r1_xboole_0(X1,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(t82_enumset1,axiom,(
    ! [X1] : k2_enumset1(X1,X1,X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_enumset1)).

fof(t85_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k5_enumset1(X1,X1,X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_enumset1)).

fof(t64_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] : k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_enumset1(X1,X2,X3),k3_enumset1(X4,X5,X6,X7,X8)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_enumset1)).

fof(t42_enumset1,axiom,(
    ! [X1,X2,X3] : k1_enumset1(X1,X2,X3) = k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).

fof(t66_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] : k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_enumset1)).

fof(t21_xboole_1,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,k2_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

fof(l29_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k3_xboole_0(X1,k1_tarski(X2)) = k1_tarski(X2)
     => r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l29_zfmisc_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(l33_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(k1_tarski(X1),X2) = k1_tarski(X1)
    <=> ~ r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l33_zfmisc_1)).

fof(t54_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(X1,k3_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_xboole_1)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(l3_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,k1_tarski(X2))
    <=> ( X1 = k1_xboole_0
        | X1 = k1_tarski(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(t29_xboole_1,axiom,(
    ! [X1,X2,X3] : r1_tarski(k3_xboole_0(X1,X2),k2_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_xboole_1)).

fof(t32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k4_xboole_0(X2,X1)
     => X1 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_xboole_1)).

fof(c_0_30,plain,(
    ! [X97,X98] : k3_tarski(k2_tarski(X97,X98)) = k2_xboole_0(X97,X98) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_31,plain,(
    ! [X79,X80] : k1_enumset1(X79,X79,X80) = k2_tarski(X79,X80) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_32,plain,(
    ! [X48,X49] : r1_tarski(X48,k2_xboole_0(X48,X49)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

cnf(c_0_33,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_34,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_35,plain,(
    ! [X20] : k2_xboole_0(X20,X20) = X20 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).

fof(c_0_36,plain,(
    ! [X18,X19] : k5_xboole_0(X18,X19) = k2_xboole_0(k4_xboole_0(X18,X19),k4_xboole_0(X19,X18)) ),
    inference(variable_rename,[status(thm)],[d6_xboole_0])).

cnf(c_0_37,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_38,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_39,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

fof(c_0_40,plain,(
    ! [X52] : k5_xboole_0(X52,X52) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t92_xboole_1])).

cnf(c_0_41,plain,
    ( k5_xboole_0(X1,X2) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

fof(c_0_42,plain,(
    ! [X27,X28,X29] :
      ( ( r1_tarski(X27,X28)
        | ~ r1_tarski(X27,k4_xboole_0(X28,X29)) )
      & ( r1_xboole_0(X27,X29)
        | ~ r1_tarski(X27,k4_xboole_0(X28,X29)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t106_xboole_1])])])).

cnf(c_0_43,plain,
    ( r1_tarski(X1,k3_tarski(k1_enumset1(X1,X1,X2))) ),
    inference(rw,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_44,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X1)) = X1 ),
    inference(rw,[status(thm)],[c_0_39,c_0_38])).

cnf(c_0_45,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_46,plain,
    ( k5_xboole_0(X1,X2) = k3_tarski(k1_enumset1(k4_xboole_0(X1,X2),k4_xboole_0(X1,X2),k4_xboole_0(X2,X1))) ),
    inference(rw,[status(thm)],[c_0_41,c_0_38])).

fof(c_0_47,plain,(
    ! [X21,X22,X24,X25,X26] :
      ( ( r1_xboole_0(X21,X22)
        | r2_hidden(esk2_2(X21,X22),k3_xboole_0(X21,X22)) )
      & ( ~ r2_hidden(X26,k3_xboole_0(X24,X25))
        | ~ r1_xboole_0(X24,X25) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

cnf(c_0_48,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_tarski(X1,k4_xboole_0(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_49,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_50,plain,
    ( k3_tarski(k1_enumset1(k4_xboole_0(X1,X1),k4_xboole_0(X1,X1),k4_xboole_0(X1,X1))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_45,c_0_46])).

fof(c_0_51,negated_conjecture,(
    ~ ! [X1,X2] :
        ( r1_tarski(k1_tarski(X1),X2)
      <=> r2_hidden(X1,X2) ) ),
    inference(assume_negation,[status(cth)],[t37_zfmisc_1])).

fof(c_0_52,plain,(
    ! [X56,X57,X58,X59,X60,X61,X62] : k5_enumset1(X56,X57,X58,X59,X60,X61,X62) = k2_xboole_0(k2_tarski(X56,X57),k3_enumset1(X58,X59,X60,X61,X62)) ),
    inference(variable_rename,[status(thm)],[t57_enumset1])).

fof(c_0_53,plain,(
    ! [X86,X87,X88,X89,X90] : k6_enumset1(X86,X86,X86,X86,X87,X88,X89,X90) = k3_enumset1(X86,X87,X88,X89,X90) ),
    inference(variable_rename,[status(thm)],[t86_enumset1])).

cnf(c_0_54,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_55,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

fof(c_0_56,plain,(
    ! [X41,X42,X43] : k3_xboole_0(X41,k4_xboole_0(X42,X43)) = k4_xboole_0(k3_xboole_0(X41,X42),X43) ),
    inference(variable_rename,[status(thm)],[t49_xboole_1])).

fof(c_0_57,plain,(
    ! [X38] : k3_xboole_0(X38,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

fof(c_0_58,plain,(
    ! [X50,X51] :
      ( ( ~ r1_xboole_0(X50,X51)
        | k4_xboole_0(X50,X51) = X50 )
      & ( k4_xboole_0(X50,X51) != X50
        | r1_xboole_0(X50,X51) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).

fof(c_0_59,plain,(
    ! [X47] : r1_xboole_0(X47,k1_xboole_0) ),
    inference(variable_rename,[status(thm)],[t65_xboole_1])).

cnf(c_0_60,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k4_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_61,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_50,c_0_44])).

fof(c_0_62,negated_conjecture,
    ( ( ~ r1_tarski(k1_tarski(esk3_0),esk4_0)
      | ~ r2_hidden(esk3_0,esk4_0) )
    & ( r1_tarski(k1_tarski(esk3_0),esk4_0)
      | r2_hidden(esk3_0,esk4_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_51])])])).

fof(c_0_63,plain,(
    ! [X81] : k2_enumset1(X81,X81,X81,X81) = k1_tarski(X81) ),
    inference(variable_rename,[status(thm)],[t82_enumset1])).

fof(c_0_64,plain,(
    ! [X82,X83,X84,X85] : k5_enumset1(X82,X82,X82,X82,X83,X84,X85) = k2_enumset1(X82,X83,X84,X85) ),
    inference(variable_rename,[status(thm)],[t85_enumset1])).

cnf(c_0_65,plain,
    ( k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_tarski(X1,X2),k3_enumset1(X3,X4,X5,X6,X7)) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_66,plain,
    ( k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

fof(c_0_67,plain,(
    ! [X63,X64,X65,X66,X67,X68,X69,X70] : k6_enumset1(X63,X64,X65,X66,X67,X68,X69,X70) = k2_xboole_0(k1_enumset1(X63,X64,X65),k3_enumset1(X66,X67,X68,X69,X70)) ),
    inference(variable_rename,[status(thm)],[t64_enumset1])).

fof(c_0_68,plain,(
    ! [X53,X54,X55] : k1_enumset1(X53,X54,X55) = k2_xboole_0(k1_tarski(X53),k2_tarski(X54,X55)) ),
    inference(variable_rename,[status(thm)],[t42_enumset1])).

fof(c_0_69,plain,(
    ! [X71,X72,X73,X74,X75,X76,X77,X78] : k6_enumset1(X71,X72,X73,X74,X75,X76,X77,X78) = k2_xboole_0(k3_enumset1(X71,X72,X73,X74,X75),k1_enumset1(X76,X77,X78)) ),
    inference(variable_rename,[status(thm)],[t66_enumset1])).

cnf(c_0_70,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(k4_xboole_0(X2,X3),X3)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_71,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_72,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_73,plain,
    ( k4_xboole_0(X1,X2) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_74,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

fof(c_0_75,plain,(
    ! [X31,X32] : k3_xboole_0(X31,k2_xboole_0(X31,X32)) = X31 ),
    inference(variable_rename,[status(thm)],[t21_xboole_1])).

cnf(c_0_76,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_77,negated_conjecture,
    ( r1_tarski(k1_tarski(esk3_0),esk4_0)
    | r2_hidden(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_78,plain,
    ( k2_enumset1(X1,X1,X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_79,plain,
    ( k5_enumset1(X1,X1,X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_80,plain,
    ( k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k3_tarski(k1_enumset1(k1_enumset1(X1,X1,X2),k1_enumset1(X1,X1,X2),k6_enumset1(X3,X3,X3,X3,X4,X5,X6,X7))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_65,c_0_34]),c_0_38]),c_0_66])).

cnf(c_0_81,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_enumset1(X1,X2,X3),k3_enumset1(X4,X5,X6,X7,X8)) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_82,plain,
    ( k1_enumset1(X1,X2,X3) = k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_83,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8)) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

fof(c_0_84,plain,(
    ! [X91,X92] :
      ( k3_xboole_0(X91,k1_tarski(X92)) != k1_tarski(X92)
      | r2_hidden(X92,X91) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l29_zfmisc_1])])).

cnf(c_0_85,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(k3_xboole_0(k4_xboole_0(X2,k4_xboole_0(X3,X4)),X3),X4)) ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_86,plain,
    ( k4_xboole_0(k3_xboole_0(X1,X2),X2) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_61]),c_0_72])).

cnf(c_0_87,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(spm,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_88,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

fof(c_0_89,plain,(
    ! [X33,X34] :
      ( ~ r1_tarski(X33,X34)
      | k3_xboole_0(X33,X34) = X33 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_90,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_76,c_0_49])).

cnf(c_0_91,negated_conjecture,
    ( r2_hidden(esk3_0,esk4_0)
    | r1_tarski(k3_tarski(k1_enumset1(k1_enumset1(esk3_0,esk3_0,esk3_0),k1_enumset1(esk3_0,esk3_0,esk3_0),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))),esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_77,c_0_78]),c_0_79]),c_0_80])).

cnf(c_0_92,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k3_tarski(k1_enumset1(k1_enumset1(X1,X2,X3),k1_enumset1(X1,X2,X3),k6_enumset1(X4,X4,X4,X4,X5,X6,X7,X8))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_81,c_0_38]),c_0_66])).

cnf(c_0_93,plain,
    ( k1_enumset1(X1,X2,X3) = k3_tarski(k1_enumset1(k3_tarski(k1_enumset1(k1_enumset1(X1,X1,X1),k1_enumset1(X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))),k3_tarski(k1_enumset1(k1_enumset1(X1,X1,X1),k1_enumset1(X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))),k1_enumset1(X2,X2,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_82,c_0_34]),c_0_78]),c_0_38]),c_0_79]),c_0_79]),c_0_80]),c_0_80])).

cnf(c_0_94,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k3_tarski(k1_enumset1(k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_83,c_0_38]),c_0_66]),c_0_66])).

fof(c_0_95,plain,(
    ! [X93,X94] :
      ( ( k4_xboole_0(k1_tarski(X93),X94) != k1_tarski(X93)
        | ~ r2_hidden(X93,X94) )
      & ( r2_hidden(X93,X94)
        | k4_xboole_0(k1_tarski(X93),X94) = k1_tarski(X93) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l33_zfmisc_1])])])).

cnf(c_0_96,plain,
    ( r2_hidden(X2,X1)
    | k3_xboole_0(X1,k1_tarski(X2)) != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_84])).

fof(c_0_97,plain,(
    ! [X44,X45,X46] : k4_xboole_0(X44,k3_xboole_0(X45,X46)) = k2_xboole_0(k4_xboole_0(X44,X45),k4_xboole_0(X44,X46)) ),
    inference(variable_rename,[status(thm)],[t54_xboole_1])).

cnf(c_0_98,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(k3_xboole_0(X2,k3_xboole_0(X3,X4)),X4)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_86]),c_0_87])).

cnf(c_0_99,plain,
    ( k3_xboole_0(X1,k3_tarski(k1_enumset1(X1,X1,X2))) = X1 ),
    inference(rw,[status(thm)],[c_0_88,c_0_38])).

cnf(c_0_100,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_89])).

fof(c_0_101,plain,(
    ! [X9,X10,X11,X12,X13,X14,X15,X16] :
      ( ( r2_hidden(X12,X9)
        | ~ r2_hidden(X12,X11)
        | X11 != k4_xboole_0(X9,X10) )
      & ( ~ r2_hidden(X12,X10)
        | ~ r2_hidden(X12,X11)
        | X11 != k4_xboole_0(X9,X10) )
      & ( ~ r2_hidden(X13,X9)
        | r2_hidden(X13,X10)
        | r2_hidden(X13,X11)
        | X11 != k4_xboole_0(X9,X10) )
      & ( ~ r2_hidden(esk1_3(X14,X15,X16),X16)
        | ~ r2_hidden(esk1_3(X14,X15,X16),X14)
        | r2_hidden(esk1_3(X14,X15,X16),X15)
        | X16 = k4_xboole_0(X14,X15) )
      & ( r2_hidden(esk1_3(X14,X15,X16),X14)
        | r2_hidden(esk1_3(X14,X15,X16),X16)
        | X16 = k4_xboole_0(X14,X15) )
      & ( ~ r2_hidden(esk1_3(X14,X15,X16),X15)
        | r2_hidden(esk1_3(X14,X15,X16),X16)
        | X16 = k4_xboole_0(X14,X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

cnf(c_0_102,plain,
    ( r1_xboole_0(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_48,c_0_90])).

cnf(c_0_103,negated_conjecture,
    ( r1_tarski(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),esk4_0)
    | r2_hidden(esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[c_0_91,c_0_92])).

cnf(c_0_104,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X2,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_93,c_0_92]),c_0_92]),c_0_94])).

cnf(c_0_105,plain,
    ( r2_hidden(X1,X2)
    | k4_xboole_0(k1_tarski(X1),X2) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_95])).

cnf(c_0_106,plain,
    ( r2_hidden(X2,X1)
    | k3_xboole_0(X1,k3_tarski(k1_enumset1(k1_enumset1(X2,X2,X2),k1_enumset1(X2,X2,X2),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)))) != k3_tarski(k1_enumset1(k1_enumset1(X2,X2,X2),k1_enumset1(X2,X2,X2),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_96,c_0_78]),c_0_78]),c_0_79]),c_0_79]),c_0_80]),c_0_80])).

fof(c_0_107,plain,(
    ! [X95,X96] :
      ( ( ~ r1_tarski(X95,k1_tarski(X96))
        | X95 = k1_xboole_0
        | X95 = k1_tarski(X96) )
      & ( X95 != k1_xboole_0
        | r1_tarski(X95,k1_tarski(X96)) )
      & ( X95 != k1_tarski(X96)
        | r1_tarski(X95,k1_tarski(X96)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_zfmisc_1])])])).

fof(c_0_108,plain,(
    ! [X30] : k2_xboole_0(X30,k1_xboole_0) = X30 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

cnf(c_0_109,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_97])).

cnf(c_0_110,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(k3_xboole_0(X2,X3),k3_tarski(k1_enumset1(X3,X3,X4)))) ),
    inference(spm,[status(thm)],[c_0_98,c_0_99])).

cnf(c_0_111,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_100,c_0_49])).

cnf(c_0_112,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_74]),c_0_72])).

cnf(c_0_113,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X1)
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_101])).

cnf(c_0_114,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_73,c_0_102])).

cnf(c_0_115,plain,
    ( k4_xboole_0(k1_tarski(X1),X2) != k1_tarski(X1)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_95])).

cnf(c_0_116,negated_conjecture,
    ( r1_tarski(k1_enumset1(esk3_0,esk3_0,esk3_0),esk4_0)
    | r2_hidden(esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[c_0_103,c_0_104])).

cnf(c_0_117,plain,
    ( k4_xboole_0(k3_tarski(k1_enumset1(k1_enumset1(X1,X1,X1),k1_enumset1(X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))),X2) = k3_tarski(k1_enumset1(k1_enumset1(X1,X1,X1),k1_enumset1(X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))
    | r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_105,c_0_78]),c_0_78]),c_0_79]),c_0_79]),c_0_80]),c_0_80])).

cnf(c_0_118,plain,
    ( r2_hidden(X1,X2)
    | k3_xboole_0(X2,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_106,c_0_92]),c_0_92])).

cnf(c_0_119,plain,
    ( X1 = k1_xboole_0
    | X1 = k1_tarski(X2)
    | ~ r1_tarski(X1,k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_107])).

cnf(c_0_120,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_108])).

cnf(c_0_121,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X2,X3)) = k3_tarski(k1_enumset1(k4_xboole_0(X1,X2),k4_xboole_0(X1,X2),k4_xboole_0(X1,X3))) ),
    inference(rw,[status(thm)],[c_0_109,c_0_38])).

cnf(c_0_122,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,k3_tarski(k1_enumset1(X2,X2,X3)))) ),
    inference(spm,[status(thm)],[c_0_110,c_0_111])).

cnf(c_0_123,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk1_3(k1_xboole_0,X2,X1),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112,c_0_113]),c_0_114])).

cnf(c_0_124,plain,
    ( k4_xboole_0(k3_tarski(k1_enumset1(k1_enumset1(X1,X1,X1),k1_enumset1(X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))),X2) != k3_tarski(k1_enumset1(k1_enumset1(X1,X1,X1),k1_enumset1(X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_115,c_0_78]),c_0_78]),c_0_79]),c_0_79]),c_0_80]),c_0_80])).

cnf(c_0_125,negated_conjecture,
    ( k3_xboole_0(k1_enumset1(esk3_0,esk3_0,esk3_0),esk4_0) = k1_enumset1(esk3_0,esk3_0,esk3_0)
    | r2_hidden(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_100,c_0_116])).

cnf(c_0_126,plain,
    ( k4_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)
    | r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_117,c_0_92]),c_0_92])).

cnf(c_0_127,plain,
    ( r2_hidden(X1,X2)
    | k3_xboole_0(X2,k1_enumset1(X1,X1,X1)) != k1_enumset1(X1,X1,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_118,c_0_104]),c_0_104])).

cnf(c_0_128,plain,
    ( k3_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_100,c_0_90])).

cnf(c_0_129,plain,
    ( X1 = k1_xboole_0
    | X1 = k3_tarski(k1_enumset1(k1_enumset1(X2,X2,X2),k1_enumset1(X2,X2,X2),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)))
    | ~ r1_tarski(X1,k3_tarski(k1_enumset1(k1_enumset1(X2,X2,X2),k1_enumset1(X2,X2,X2),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_119,c_0_78]),c_0_78]),c_0_79]),c_0_79]),c_0_80]),c_0_80])).

fof(c_0_130,plain,(
    ! [X35,X36,X37] : r1_tarski(k3_xboole_0(X35,X36),k2_xboole_0(X35,X37)) ),
    inference(variable_rename,[status(thm)],[t29_xboole_1])).

fof(c_0_131,plain,(
    ! [X39,X40] :
      ( k4_xboole_0(X39,X40) != k4_xboole_0(X40,X39)
      | X39 = X40 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t32_xboole_1])])).

cnf(c_0_132,plain,
    ( k3_tarski(k1_enumset1(X1,X1,k1_xboole_0)) = X1 ),
    inference(rw,[status(thm)],[c_0_120,c_0_38])).

cnf(c_0_133,plain,
    ( k3_tarski(k1_enumset1(k4_xboole_0(X1,X2),k4_xboole_0(X1,X2),X1)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_121,c_0_87]),c_0_72]),c_0_87])).

cnf(c_0_134,plain,
    ( k4_xboole_0(X1,k3_tarski(k1_enumset1(X1,X1,X2))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_122,c_0_123])).

cnf(c_0_135,plain,
    ( k4_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2) != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_124,c_0_92]),c_0_92])).

cnf(c_0_136,negated_conjecture,
    ( k4_xboole_0(k1_enumset1(esk3_0,esk3_0,esk3_0),esk4_0) = k1_xboole_0
    | r2_hidden(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_86,c_0_125])).

cnf(c_0_137,plain,
    ( k4_xboole_0(k1_enumset1(X1,X1,X1),X2) = k1_enumset1(X1,X1,X1)
    | r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_126,c_0_104]),c_0_104])).

cnf(c_0_138,plain,
    ( k1_enumset1(X1,X1,X1) != k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_127,c_0_128]),c_0_112])).

cnf(c_0_139,plain,
    ( X1 = k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)
    | X1 = k1_xboole_0
    | ~ r1_tarski(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_129,c_0_92]),c_0_92])).

cnf(c_0_140,negated_conjecture,
    ( ~ r1_tarski(k1_tarski(esk3_0),esk4_0)
    | ~ r2_hidden(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_141,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),k2_xboole_0(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_130])).

cnf(c_0_142,plain,
    ( X1 = X2
    | k4_xboole_0(X1,X2) != k4_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_131])).

cnf(c_0_143,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X2,X1)) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_121,c_0_61]),c_0_132])).

cnf(c_0_144,plain,
    ( k4_xboole_0(k3_xboole_0(k4_xboole_0(X1,X2),X1),k3_xboole_0(X2,X3)) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_121]),c_0_71])).

cnf(c_0_145,plain,
    ( k3_tarski(k1_enumset1(k1_xboole_0,k1_xboole_0,X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_133,c_0_134])).

cnf(c_0_146,plain,
    ( k4_xboole_0(k1_enumset1(X1,X1,X1),X2) != k1_enumset1(X1,X1,X1)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_135,c_0_104]),c_0_104])).

cnf(c_0_147,negated_conjecture,
    ( r2_hidden(esk3_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_136,c_0_137]),c_0_138])).

cnf(c_0_148,plain,
    ( X1 = k1_enumset1(X2,X2,X2)
    | X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_enumset1(X2,X2,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_139,c_0_104]),c_0_104])).

cnf(c_0_149,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_60,c_0_49])).

cnf(c_0_150,negated_conjecture,
    ( ~ r2_hidden(esk3_0,esk4_0)
    | ~ r1_tarski(k3_tarski(k1_enumset1(k1_enumset1(esk3_0,esk3_0,esk3_0),k1_enumset1(esk3_0,esk3_0,esk3_0),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))),esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_140,c_0_78]),c_0_79]),c_0_80])).

cnf(c_0_151,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),k3_tarski(k1_enumset1(X1,X1,X3))) ),
    inference(rw,[status(thm)],[c_0_141,c_0_38])).

cnf(c_0_152,plain,
    ( k3_xboole_0(X1,X2) = X2
    | k4_xboole_0(X2,X1) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_142,c_0_86]),c_0_143])).

cnf(c_0_153,plain,
    ( k4_xboole_0(k3_xboole_0(X1,X2),X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_86,c_0_144])).

cnf(c_0_154,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_121,c_0_61]),c_0_145])).

cnf(c_0_155,negated_conjecture,
    ( k4_xboole_0(k1_enumset1(esk3_0,esk3_0,esk3_0),esk4_0) != k1_enumset1(esk3_0,esk3_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_146,c_0_147])).

cnf(c_0_156,plain,
    ( k4_xboole_0(k1_enumset1(X1,X1,X1),X2) = k1_enumset1(X1,X1,X1)
    | k4_xboole_0(k1_enumset1(X1,X1,X1),X2) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_148,c_0_149])).

cnf(c_0_157,negated_conjecture,
    ( ~ r1_tarski(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),esk4_0)
    | ~ r2_hidden(esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[c_0_150,c_0_92])).

cnf(c_0_158,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_151,c_0_44])).

cnf(c_0_159,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,X1)) = k3_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_152,c_0_86])).

cnf(c_0_160,plain,
    ( k3_xboole_0(X1,X2) = X1
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_142,c_0_153]),c_0_154])).

cnf(c_0_161,negated_conjecture,
    ( k4_xboole_0(k1_enumset1(esk3_0,esk3_0,esk3_0),esk4_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_155,c_0_156])).

cnf(c_0_162,negated_conjecture,
    ( ~ r1_tarski(k1_enumset1(esk3_0,esk3_0,esk3_0),esk4_0)
    | ~ r2_hidden(esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[c_0_157,c_0_104])).

cnf(c_0_163,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_158,c_0_159])).

cnf(c_0_164,negated_conjecture,
    ( k3_xboole_0(k1_enumset1(esk3_0,esk3_0,esk3_0),esk4_0) = k1_enumset1(esk3_0,esk3_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_160,c_0_161])).

cnf(c_0_165,negated_conjecture,
    ( ~ r1_tarski(k1_enumset1(esk3_0,esk3_0,esk3_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_162,c_0_147])])).

cnf(c_0_166,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_163,c_0_164]),c_0_165]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 09:41:20 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.44  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S054N
% 0.20/0.44  # and selection function GSelectMinInfpos.
% 0.20/0.44  #
% 0.20/0.44  # Preprocessing time       : 0.028 s
% 0.20/0.44  # Presaturation interreduction done
% 0.20/0.44  
% 0.20/0.44  # Proof found!
% 0.20/0.44  # SZS status Theorem
% 0.20/0.44  # SZS output start CNFRefutation
% 0.20/0.44  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.20/0.44  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.20/0.44  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.20/0.44  fof(idempotence_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 0.20/0.44  fof(d6_xboole_0, axiom, ![X1, X2]:k5_xboole_0(X1,X2)=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_xboole_0)).
% 0.20/0.44  fof(t92_xboole_1, axiom, ![X1]:k5_xboole_0(X1,X1)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 0.20/0.44  fof(t106_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k4_xboole_0(X2,X3))=>(r1_tarski(X1,X2)&r1_xboole_0(X1,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 0.20/0.44  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 0.20/0.44  fof(t37_zfmisc_1, conjecture, ![X1, X2]:(r1_tarski(k1_tarski(X1),X2)<=>r2_hidden(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_zfmisc_1)).
% 0.20/0.44  fof(t57_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k2_tarski(X1,X2),k3_enumset1(X3,X4,X5,X6,X7)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_enumset1)).
% 0.20/0.44  fof(t86_enumset1, axiom, ![X1, X2, X3, X4, X5]:k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_enumset1)).
% 0.20/0.44  fof(t49_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 0.20/0.44  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 0.20/0.44  fof(t83_xboole_1, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k4_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 0.20/0.44  fof(t65_xboole_1, axiom, ![X1]:r1_xboole_0(X1,k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 0.20/0.44  fof(t82_enumset1, axiom, ![X1]:k2_enumset1(X1,X1,X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t82_enumset1)).
% 0.20/0.44  fof(t85_enumset1, axiom, ![X1, X2, X3, X4]:k5_enumset1(X1,X1,X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t85_enumset1)).
% 0.20/0.44  fof(t64_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8]:k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k1_enumset1(X1,X2,X3),k3_enumset1(X4,X5,X6,X7,X8)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_enumset1)).
% 0.20/0.44  fof(t42_enumset1, axiom, ![X1, X2, X3]:k1_enumset1(X1,X2,X3)=k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_enumset1)).
% 0.20/0.44  fof(t66_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8]:k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_enumset1)).
% 0.20/0.44  fof(t21_xboole_1, axiom, ![X1, X2]:k3_xboole_0(X1,k2_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_xboole_1)).
% 0.20/0.44  fof(l29_zfmisc_1, axiom, ![X1, X2]:(k3_xboole_0(X1,k1_tarski(X2))=k1_tarski(X2)=>r2_hidden(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l29_zfmisc_1)).
% 0.20/0.44  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.20/0.44  fof(l33_zfmisc_1, axiom, ![X1, X2]:(k4_xboole_0(k1_tarski(X1),X2)=k1_tarski(X1)<=>~(r2_hidden(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l33_zfmisc_1)).
% 0.20/0.44  fof(t54_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(X1,k3_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t54_xboole_1)).
% 0.20/0.44  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.20/0.44  fof(l3_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(X1,k1_tarski(X2))<=>(X1=k1_xboole_0|X1=k1_tarski(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 0.20/0.44  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 0.20/0.44  fof(t29_xboole_1, axiom, ![X1, X2, X3]:r1_tarski(k3_xboole_0(X1,X2),k2_xboole_0(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_xboole_1)).
% 0.20/0.44  fof(t32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k4_xboole_0(X2,X1)=>X1=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_xboole_1)).
% 0.20/0.44  fof(c_0_30, plain, ![X97, X98]:k3_tarski(k2_tarski(X97,X98))=k2_xboole_0(X97,X98), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.20/0.44  fof(c_0_31, plain, ![X79, X80]:k1_enumset1(X79,X79,X80)=k2_tarski(X79,X80), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.20/0.44  fof(c_0_32, plain, ![X48, X49]:r1_tarski(X48,k2_xboole_0(X48,X49)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.20/0.44  cnf(c_0_33, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.44  cnf(c_0_34, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.20/0.44  fof(c_0_35, plain, ![X20]:k2_xboole_0(X20,X20)=X20, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).
% 0.20/0.44  fof(c_0_36, plain, ![X18, X19]:k5_xboole_0(X18,X19)=k2_xboole_0(k4_xboole_0(X18,X19),k4_xboole_0(X19,X18)), inference(variable_rename,[status(thm)],[d6_xboole_0])).
% 0.20/0.44  cnf(c_0_37, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.44  cnf(c_0_38, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_33, c_0_34])).
% 0.20/0.44  cnf(c_0_39, plain, (k2_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.20/0.44  fof(c_0_40, plain, ![X52]:k5_xboole_0(X52,X52)=k1_xboole_0, inference(variable_rename,[status(thm)],[t92_xboole_1])).
% 0.20/0.44  cnf(c_0_41, plain, (k5_xboole_0(X1,X2)=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.20/0.44  fof(c_0_42, plain, ![X27, X28, X29]:((r1_tarski(X27,X28)|~r1_tarski(X27,k4_xboole_0(X28,X29)))&(r1_xboole_0(X27,X29)|~r1_tarski(X27,k4_xboole_0(X28,X29)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t106_xboole_1])])])).
% 0.20/0.44  cnf(c_0_43, plain, (r1_tarski(X1,k3_tarski(k1_enumset1(X1,X1,X2)))), inference(rw,[status(thm)],[c_0_37, c_0_38])).
% 0.20/0.44  cnf(c_0_44, plain, (k3_tarski(k1_enumset1(X1,X1,X1))=X1), inference(rw,[status(thm)],[c_0_39, c_0_38])).
% 0.20/0.44  cnf(c_0_45, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.20/0.44  cnf(c_0_46, plain, (k5_xboole_0(X1,X2)=k3_tarski(k1_enumset1(k4_xboole_0(X1,X2),k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)))), inference(rw,[status(thm)],[c_0_41, c_0_38])).
% 0.20/0.44  fof(c_0_47, plain, ![X21, X22, X24, X25, X26]:((r1_xboole_0(X21,X22)|r2_hidden(esk2_2(X21,X22),k3_xboole_0(X21,X22)))&(~r2_hidden(X26,k3_xboole_0(X24,X25))|~r1_xboole_0(X24,X25))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 0.20/0.44  cnf(c_0_48, plain, (r1_xboole_0(X1,X2)|~r1_tarski(X1,k4_xboole_0(X3,X2))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.20/0.44  cnf(c_0_49, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.20/0.44  cnf(c_0_50, plain, (k3_tarski(k1_enumset1(k4_xboole_0(X1,X1),k4_xboole_0(X1,X1),k4_xboole_0(X1,X1)))=k1_xboole_0), inference(rw,[status(thm)],[c_0_45, c_0_46])).
% 0.20/0.44  fof(c_0_51, negated_conjecture, ~(![X1, X2]:(r1_tarski(k1_tarski(X1),X2)<=>r2_hidden(X1,X2))), inference(assume_negation,[status(cth)],[t37_zfmisc_1])).
% 0.20/0.44  fof(c_0_52, plain, ![X56, X57, X58, X59, X60, X61, X62]:k5_enumset1(X56,X57,X58,X59,X60,X61,X62)=k2_xboole_0(k2_tarski(X56,X57),k3_enumset1(X58,X59,X60,X61,X62)), inference(variable_rename,[status(thm)],[t57_enumset1])).
% 0.20/0.44  fof(c_0_53, plain, ![X86, X87, X88, X89, X90]:k6_enumset1(X86,X86,X86,X86,X87,X88,X89,X90)=k3_enumset1(X86,X87,X88,X89,X90), inference(variable_rename,[status(thm)],[t86_enumset1])).
% 0.20/0.44  cnf(c_0_54, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.20/0.44  cnf(c_0_55, plain, (r1_xboole_0(k4_xboole_0(X1,X2),X2)), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.20/0.44  fof(c_0_56, plain, ![X41, X42, X43]:k3_xboole_0(X41,k4_xboole_0(X42,X43))=k4_xboole_0(k3_xboole_0(X41,X42),X43), inference(variable_rename,[status(thm)],[t49_xboole_1])).
% 0.20/0.44  fof(c_0_57, plain, ![X38]:k3_xboole_0(X38,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 0.20/0.44  fof(c_0_58, plain, ![X50, X51]:((~r1_xboole_0(X50,X51)|k4_xboole_0(X50,X51)=X50)&(k4_xboole_0(X50,X51)!=X50|r1_xboole_0(X50,X51))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).
% 0.20/0.44  fof(c_0_59, plain, ![X47]:r1_xboole_0(X47,k1_xboole_0), inference(variable_rename,[status(thm)],[t65_xboole_1])).
% 0.20/0.44  cnf(c_0_60, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k4_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.20/0.44  cnf(c_0_61, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[c_0_50, c_0_44])).
% 0.20/0.44  fof(c_0_62, negated_conjecture, ((~r1_tarski(k1_tarski(esk3_0),esk4_0)|~r2_hidden(esk3_0,esk4_0))&(r1_tarski(k1_tarski(esk3_0),esk4_0)|r2_hidden(esk3_0,esk4_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_51])])])).
% 0.20/0.44  fof(c_0_63, plain, ![X81]:k2_enumset1(X81,X81,X81,X81)=k1_tarski(X81), inference(variable_rename,[status(thm)],[t82_enumset1])).
% 0.20/0.44  fof(c_0_64, plain, ![X82, X83, X84, X85]:k5_enumset1(X82,X82,X82,X82,X83,X84,X85)=k2_enumset1(X82,X83,X84,X85), inference(variable_rename,[status(thm)],[t85_enumset1])).
% 0.20/0.44  cnf(c_0_65, plain, (k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k2_tarski(X1,X2),k3_enumset1(X3,X4,X5,X6,X7))), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.20/0.44  cnf(c_0_66, plain, (k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.20/0.44  fof(c_0_67, plain, ![X63, X64, X65, X66, X67, X68, X69, X70]:k6_enumset1(X63,X64,X65,X66,X67,X68,X69,X70)=k2_xboole_0(k1_enumset1(X63,X64,X65),k3_enumset1(X66,X67,X68,X69,X70)), inference(variable_rename,[status(thm)],[t64_enumset1])).
% 0.20/0.44  fof(c_0_68, plain, ![X53, X54, X55]:k1_enumset1(X53,X54,X55)=k2_xboole_0(k1_tarski(X53),k2_tarski(X54,X55)), inference(variable_rename,[status(thm)],[t42_enumset1])).
% 0.20/0.44  fof(c_0_69, plain, ![X71, X72, X73, X74, X75, X76, X77, X78]:k6_enumset1(X71,X72,X73,X74,X75,X76,X77,X78)=k2_xboole_0(k3_enumset1(X71,X72,X73,X74,X75),k1_enumset1(X76,X77,X78)), inference(variable_rename,[status(thm)],[t66_enumset1])).
% 0.20/0.44  cnf(c_0_70, plain, (~r2_hidden(X1,k3_xboole_0(k4_xboole_0(X2,X3),X3))), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.20/0.44  cnf(c_0_71, plain, (k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.20/0.44  cnf(c_0_72, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.20/0.44  cnf(c_0_73, plain, (k4_xboole_0(X1,X2)=X1|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.20/0.44  cnf(c_0_74, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.20/0.44  fof(c_0_75, plain, ![X31, X32]:k3_xboole_0(X31,k2_xboole_0(X31,X32))=X31, inference(variable_rename,[status(thm)],[t21_xboole_1])).
% 0.20/0.44  cnf(c_0_76, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.20/0.44  cnf(c_0_77, negated_conjecture, (r1_tarski(k1_tarski(esk3_0),esk4_0)|r2_hidden(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.20/0.44  cnf(c_0_78, plain, (k2_enumset1(X1,X1,X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.20/0.44  cnf(c_0_79, plain, (k5_enumset1(X1,X1,X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.20/0.44  cnf(c_0_80, plain, (k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k3_tarski(k1_enumset1(k1_enumset1(X1,X1,X2),k1_enumset1(X1,X1,X2),k6_enumset1(X3,X3,X3,X3,X4,X5,X6,X7)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_65, c_0_34]), c_0_38]), c_0_66])).
% 0.20/0.44  cnf(c_0_81, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k1_enumset1(X1,X2,X3),k3_enumset1(X4,X5,X6,X7,X8))), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.20/0.44  cnf(c_0_82, plain, (k1_enumset1(X1,X2,X3)=k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.20/0.44  cnf(c_0_83, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8))), inference(split_conjunct,[status(thm)],[c_0_69])).
% 0.20/0.44  fof(c_0_84, plain, ![X91, X92]:(k3_xboole_0(X91,k1_tarski(X92))!=k1_tarski(X92)|r2_hidden(X92,X91)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l29_zfmisc_1])])).
% 0.20/0.44  cnf(c_0_85, plain, (~r2_hidden(X1,k4_xboole_0(k3_xboole_0(k4_xboole_0(X2,k4_xboole_0(X3,X4)),X3),X4))), inference(spm,[status(thm)],[c_0_70, c_0_71])).
% 0.20/0.44  cnf(c_0_86, plain, (k4_xboole_0(k3_xboole_0(X1,X2),X2)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_61]), c_0_72])).
% 0.20/0.44  cnf(c_0_87, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(spm,[status(thm)],[c_0_73, c_0_74])).
% 0.20/0.44  cnf(c_0_88, plain, (k3_xboole_0(X1,k2_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_75])).
% 0.20/0.44  fof(c_0_89, plain, ![X33, X34]:(~r1_tarski(X33,X34)|k3_xboole_0(X33,X34)=X33), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.20/0.44  cnf(c_0_90, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_76, c_0_49])).
% 0.20/0.44  cnf(c_0_91, negated_conjecture, (r2_hidden(esk3_0,esk4_0)|r1_tarski(k3_tarski(k1_enumset1(k1_enumset1(esk3_0,esk3_0,esk3_0),k1_enumset1(esk3_0,esk3_0,esk3_0),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))),esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_77, c_0_78]), c_0_79]), c_0_80])).
% 0.20/0.44  cnf(c_0_92, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k3_tarski(k1_enumset1(k1_enumset1(X1,X2,X3),k1_enumset1(X1,X2,X3),k6_enumset1(X4,X4,X4,X4,X5,X6,X7,X8)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_81, c_0_38]), c_0_66])).
% 0.20/0.44  cnf(c_0_93, plain, (k1_enumset1(X1,X2,X3)=k3_tarski(k1_enumset1(k3_tarski(k1_enumset1(k1_enumset1(X1,X1,X1),k1_enumset1(X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))),k3_tarski(k1_enumset1(k1_enumset1(X1,X1,X1),k1_enumset1(X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))),k1_enumset1(X2,X2,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_82, c_0_34]), c_0_78]), c_0_38]), c_0_79]), c_0_79]), c_0_80]), c_0_80])).
% 0.20/0.44  cnf(c_0_94, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k3_tarski(k1_enumset1(k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_83, c_0_38]), c_0_66]), c_0_66])).
% 0.20/0.44  fof(c_0_95, plain, ![X93, X94]:((k4_xboole_0(k1_tarski(X93),X94)!=k1_tarski(X93)|~r2_hidden(X93,X94))&(r2_hidden(X93,X94)|k4_xboole_0(k1_tarski(X93),X94)=k1_tarski(X93))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l33_zfmisc_1])])])).
% 0.20/0.44  cnf(c_0_96, plain, (r2_hidden(X2,X1)|k3_xboole_0(X1,k1_tarski(X2))!=k1_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_84])).
% 0.20/0.44  fof(c_0_97, plain, ![X44, X45, X46]:k4_xboole_0(X44,k3_xboole_0(X45,X46))=k2_xboole_0(k4_xboole_0(X44,X45),k4_xboole_0(X44,X46)), inference(variable_rename,[status(thm)],[t54_xboole_1])).
% 0.20/0.44  cnf(c_0_98, plain, (~r2_hidden(X1,k4_xboole_0(k3_xboole_0(X2,k3_xboole_0(X3,X4)),X4))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_86]), c_0_87])).
% 0.20/0.44  cnf(c_0_99, plain, (k3_xboole_0(X1,k3_tarski(k1_enumset1(X1,X1,X2)))=X1), inference(rw,[status(thm)],[c_0_88, c_0_38])).
% 0.20/0.44  cnf(c_0_100, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_89])).
% 0.20/0.44  fof(c_0_101, plain, ![X9, X10, X11, X12, X13, X14, X15, X16]:((((r2_hidden(X12,X9)|~r2_hidden(X12,X11)|X11!=k4_xboole_0(X9,X10))&(~r2_hidden(X12,X10)|~r2_hidden(X12,X11)|X11!=k4_xboole_0(X9,X10)))&(~r2_hidden(X13,X9)|r2_hidden(X13,X10)|r2_hidden(X13,X11)|X11!=k4_xboole_0(X9,X10)))&((~r2_hidden(esk1_3(X14,X15,X16),X16)|(~r2_hidden(esk1_3(X14,X15,X16),X14)|r2_hidden(esk1_3(X14,X15,X16),X15))|X16=k4_xboole_0(X14,X15))&((r2_hidden(esk1_3(X14,X15,X16),X14)|r2_hidden(esk1_3(X14,X15,X16),X16)|X16=k4_xboole_0(X14,X15))&(~r2_hidden(esk1_3(X14,X15,X16),X15)|r2_hidden(esk1_3(X14,X15,X16),X16)|X16=k4_xboole_0(X14,X15))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.20/0.44  cnf(c_0_102, plain, (r1_xboole_0(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_48, c_0_90])).
% 0.20/0.44  cnf(c_0_103, negated_conjecture, (r1_tarski(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),esk4_0)|r2_hidden(esk3_0,esk4_0)), inference(rw,[status(thm)],[c_0_91, c_0_92])).
% 0.20/0.44  cnf(c_0_104, plain, (k6_enumset1(X1,X1,X1,X1,X1,X2,X2,X3)=k1_enumset1(X1,X2,X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_93, c_0_92]), c_0_92]), c_0_94])).
% 0.20/0.44  cnf(c_0_105, plain, (r2_hidden(X1,X2)|k4_xboole_0(k1_tarski(X1),X2)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_95])).
% 0.20/0.44  cnf(c_0_106, plain, (r2_hidden(X2,X1)|k3_xboole_0(X1,k3_tarski(k1_enumset1(k1_enumset1(X2,X2,X2),k1_enumset1(X2,X2,X2),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))))!=k3_tarski(k1_enumset1(k1_enumset1(X2,X2,X2),k1_enumset1(X2,X2,X2),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_96, c_0_78]), c_0_78]), c_0_79]), c_0_79]), c_0_80]), c_0_80])).
% 0.20/0.44  fof(c_0_107, plain, ![X95, X96]:((~r1_tarski(X95,k1_tarski(X96))|(X95=k1_xboole_0|X95=k1_tarski(X96)))&((X95!=k1_xboole_0|r1_tarski(X95,k1_tarski(X96)))&(X95!=k1_tarski(X96)|r1_tarski(X95,k1_tarski(X96))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_zfmisc_1])])])).
% 0.20/0.44  fof(c_0_108, plain, ![X30]:k2_xboole_0(X30,k1_xboole_0)=X30, inference(variable_rename,[status(thm)],[t1_boole])).
% 0.20/0.44  cnf(c_0_109, plain, (k4_xboole_0(X1,k3_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_97])).
% 0.20/0.44  cnf(c_0_110, plain, (~r2_hidden(X1,k4_xboole_0(k3_xboole_0(X2,X3),k3_tarski(k1_enumset1(X3,X3,X4))))), inference(spm,[status(thm)],[c_0_98, c_0_99])).
% 0.20/0.44  cnf(c_0_111, plain, (k3_xboole_0(X1,X1)=X1), inference(spm,[status(thm)],[c_0_100, c_0_49])).
% 0.20/0.44  cnf(c_0_112, plain, (~r2_hidden(X1,k1_xboole_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_74]), c_0_72])).
% 0.20/0.44  cnf(c_0_113, plain, (r2_hidden(esk1_3(X1,X2,X3),X1)|r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_101])).
% 0.20/0.44  cnf(c_0_114, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_73, c_0_102])).
% 0.20/0.44  cnf(c_0_115, plain, (k4_xboole_0(k1_tarski(X1),X2)!=k1_tarski(X1)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_95])).
% 0.20/0.44  cnf(c_0_116, negated_conjecture, (r1_tarski(k1_enumset1(esk3_0,esk3_0,esk3_0),esk4_0)|r2_hidden(esk3_0,esk4_0)), inference(rw,[status(thm)],[c_0_103, c_0_104])).
% 0.20/0.44  cnf(c_0_117, plain, (k4_xboole_0(k3_tarski(k1_enumset1(k1_enumset1(X1,X1,X1),k1_enumset1(X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))),X2)=k3_tarski(k1_enumset1(k1_enumset1(X1,X1,X1),k1_enumset1(X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))|r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_105, c_0_78]), c_0_78]), c_0_79]), c_0_79]), c_0_80]), c_0_80])).
% 0.20/0.44  cnf(c_0_118, plain, (r2_hidden(X1,X2)|k3_xboole_0(X2,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))!=k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_106, c_0_92]), c_0_92])).
% 0.20/0.44  cnf(c_0_119, plain, (X1=k1_xboole_0|X1=k1_tarski(X2)|~r1_tarski(X1,k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_107])).
% 0.20/0.44  cnf(c_0_120, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_108])).
% 0.20/0.44  cnf(c_0_121, plain, (k4_xboole_0(X1,k3_xboole_0(X2,X3))=k3_tarski(k1_enumset1(k4_xboole_0(X1,X2),k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)))), inference(rw,[status(thm)],[c_0_109, c_0_38])).
% 0.20/0.44  cnf(c_0_122, plain, (~r2_hidden(X1,k4_xboole_0(X2,k3_tarski(k1_enumset1(X2,X2,X3))))), inference(spm,[status(thm)],[c_0_110, c_0_111])).
% 0.20/0.44  cnf(c_0_123, plain, (X1=k1_xboole_0|r2_hidden(esk1_3(k1_xboole_0,X2,X1),X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112, c_0_113]), c_0_114])).
% 0.20/0.44  cnf(c_0_124, plain, (k4_xboole_0(k3_tarski(k1_enumset1(k1_enumset1(X1,X1,X1),k1_enumset1(X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))),X2)!=k3_tarski(k1_enumset1(k1_enumset1(X1,X1,X1),k1_enumset1(X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_115, c_0_78]), c_0_78]), c_0_79]), c_0_79]), c_0_80]), c_0_80])).
% 0.20/0.44  cnf(c_0_125, negated_conjecture, (k3_xboole_0(k1_enumset1(esk3_0,esk3_0,esk3_0),esk4_0)=k1_enumset1(esk3_0,esk3_0,esk3_0)|r2_hidden(esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_100, c_0_116])).
% 0.20/0.44  cnf(c_0_126, plain, (k4_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2)=k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)|r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_117, c_0_92]), c_0_92])).
% 0.20/0.44  cnf(c_0_127, plain, (r2_hidden(X1,X2)|k3_xboole_0(X2,k1_enumset1(X1,X1,X1))!=k1_enumset1(X1,X1,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_118, c_0_104]), c_0_104])).
% 0.20/0.44  cnf(c_0_128, plain, (k3_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_100, c_0_90])).
% 0.20/0.44  cnf(c_0_129, plain, (X1=k1_xboole_0|X1=k3_tarski(k1_enumset1(k1_enumset1(X2,X2,X2),k1_enumset1(X2,X2,X2),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)))|~r1_tarski(X1,k3_tarski(k1_enumset1(k1_enumset1(X2,X2,X2),k1_enumset1(X2,X2,X2),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_119, c_0_78]), c_0_78]), c_0_79]), c_0_79]), c_0_80]), c_0_80])).
% 0.20/0.44  fof(c_0_130, plain, ![X35, X36, X37]:r1_tarski(k3_xboole_0(X35,X36),k2_xboole_0(X35,X37)), inference(variable_rename,[status(thm)],[t29_xboole_1])).
% 0.20/0.44  fof(c_0_131, plain, ![X39, X40]:(k4_xboole_0(X39,X40)!=k4_xboole_0(X40,X39)|X39=X40), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t32_xboole_1])])).
% 0.20/0.44  cnf(c_0_132, plain, (k3_tarski(k1_enumset1(X1,X1,k1_xboole_0))=X1), inference(rw,[status(thm)],[c_0_120, c_0_38])).
% 0.20/0.44  cnf(c_0_133, plain, (k3_tarski(k1_enumset1(k4_xboole_0(X1,X2),k4_xboole_0(X1,X2),X1))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_121, c_0_87]), c_0_72]), c_0_87])).
% 0.20/0.44  cnf(c_0_134, plain, (k4_xboole_0(X1,k3_tarski(k1_enumset1(X1,X1,X2)))=k1_xboole_0), inference(spm,[status(thm)],[c_0_122, c_0_123])).
% 0.20/0.44  cnf(c_0_135, plain, (k4_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2)!=k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_124, c_0_92]), c_0_92])).
% 0.20/0.44  cnf(c_0_136, negated_conjecture, (k4_xboole_0(k1_enumset1(esk3_0,esk3_0,esk3_0),esk4_0)=k1_xboole_0|r2_hidden(esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_86, c_0_125])).
% 0.20/0.44  cnf(c_0_137, plain, (k4_xboole_0(k1_enumset1(X1,X1,X1),X2)=k1_enumset1(X1,X1,X1)|r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_126, c_0_104]), c_0_104])).
% 0.20/0.44  cnf(c_0_138, plain, (k1_enumset1(X1,X1,X1)!=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_127, c_0_128]), c_0_112])).
% 0.20/0.44  cnf(c_0_139, plain, (X1=k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)|X1=k1_xboole_0|~r1_tarski(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_129, c_0_92]), c_0_92])).
% 0.20/0.44  cnf(c_0_140, negated_conjecture, (~r1_tarski(k1_tarski(esk3_0),esk4_0)|~r2_hidden(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.20/0.44  cnf(c_0_141, plain, (r1_tarski(k3_xboole_0(X1,X2),k2_xboole_0(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_130])).
% 0.20/0.44  cnf(c_0_142, plain, (X1=X2|k4_xboole_0(X1,X2)!=k4_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_131])).
% 0.20/0.44  cnf(c_0_143, plain, (k4_xboole_0(X1,k3_xboole_0(X2,X1))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_121, c_0_61]), c_0_132])).
% 0.20/0.44  cnf(c_0_144, plain, (k4_xboole_0(k3_xboole_0(k4_xboole_0(X1,X2),X1),k3_xboole_0(X2,X3))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_121]), c_0_71])).
% 0.20/0.44  cnf(c_0_145, plain, (k3_tarski(k1_enumset1(k1_xboole_0,k1_xboole_0,X1))=X1), inference(spm,[status(thm)],[c_0_133, c_0_134])).
% 0.20/0.44  cnf(c_0_146, plain, (k4_xboole_0(k1_enumset1(X1,X1,X1),X2)!=k1_enumset1(X1,X1,X1)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_135, c_0_104]), c_0_104])).
% 0.20/0.44  cnf(c_0_147, negated_conjecture, (r2_hidden(esk3_0,esk4_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_136, c_0_137]), c_0_138])).
% 0.20/0.44  cnf(c_0_148, plain, (X1=k1_enumset1(X2,X2,X2)|X1=k1_xboole_0|~r1_tarski(X1,k1_enumset1(X2,X2,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_139, c_0_104]), c_0_104])).
% 0.20/0.44  cnf(c_0_149, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(spm,[status(thm)],[c_0_60, c_0_49])).
% 0.20/0.44  cnf(c_0_150, negated_conjecture, (~r2_hidden(esk3_0,esk4_0)|~r1_tarski(k3_tarski(k1_enumset1(k1_enumset1(esk3_0,esk3_0,esk3_0),k1_enumset1(esk3_0,esk3_0,esk3_0),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))),esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_140, c_0_78]), c_0_79]), c_0_80])).
% 0.20/0.44  cnf(c_0_151, plain, (r1_tarski(k3_xboole_0(X1,X2),k3_tarski(k1_enumset1(X1,X1,X3)))), inference(rw,[status(thm)],[c_0_141, c_0_38])).
% 0.20/0.44  cnf(c_0_152, plain, (k3_xboole_0(X1,X2)=X2|k4_xboole_0(X2,X1)!=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_142, c_0_86]), c_0_143])).
% 0.20/0.44  cnf(c_0_153, plain, (k4_xboole_0(k3_xboole_0(X1,X2),X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_86, c_0_144])).
% 0.20/0.44  cnf(c_0_154, plain, (k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_121, c_0_61]), c_0_145])).
% 0.20/0.44  cnf(c_0_155, negated_conjecture, (k4_xboole_0(k1_enumset1(esk3_0,esk3_0,esk3_0),esk4_0)!=k1_enumset1(esk3_0,esk3_0,esk3_0)), inference(spm,[status(thm)],[c_0_146, c_0_147])).
% 0.20/0.44  cnf(c_0_156, plain, (k4_xboole_0(k1_enumset1(X1,X1,X1),X2)=k1_enumset1(X1,X1,X1)|k4_xboole_0(k1_enumset1(X1,X1,X1),X2)=k1_xboole_0), inference(spm,[status(thm)],[c_0_148, c_0_149])).
% 0.20/0.44  cnf(c_0_157, negated_conjecture, (~r1_tarski(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),esk4_0)|~r2_hidden(esk3_0,esk4_0)), inference(rw,[status(thm)],[c_0_150, c_0_92])).
% 0.20/0.44  cnf(c_0_158, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(spm,[status(thm)],[c_0_151, c_0_44])).
% 0.20/0.44  cnf(c_0_159, plain, (k3_xboole_0(X1,k3_xboole_0(X2,X1))=k3_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_152, c_0_86])).
% 0.20/0.44  cnf(c_0_160, plain, (k3_xboole_0(X1,X2)=X1|k4_xboole_0(X1,X2)!=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_142, c_0_153]), c_0_154])).
% 0.20/0.44  cnf(c_0_161, negated_conjecture, (k4_xboole_0(k1_enumset1(esk3_0,esk3_0,esk3_0),esk4_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_155, c_0_156])).
% 0.20/0.44  cnf(c_0_162, negated_conjecture, (~r1_tarski(k1_enumset1(esk3_0,esk3_0,esk3_0),esk4_0)|~r2_hidden(esk3_0,esk4_0)), inference(rw,[status(thm)],[c_0_157, c_0_104])).
% 0.20/0.44  cnf(c_0_163, plain, (r1_tarski(k3_xboole_0(X1,X2),X2)), inference(spm,[status(thm)],[c_0_158, c_0_159])).
% 0.20/0.44  cnf(c_0_164, negated_conjecture, (k3_xboole_0(k1_enumset1(esk3_0,esk3_0,esk3_0),esk4_0)=k1_enumset1(esk3_0,esk3_0,esk3_0)), inference(spm,[status(thm)],[c_0_160, c_0_161])).
% 0.20/0.44  cnf(c_0_165, negated_conjecture, (~r1_tarski(k1_enumset1(esk3_0,esk3_0,esk3_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_162, c_0_147])])).
% 0.20/0.44  cnf(c_0_166, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_163, c_0_164]), c_0_165]), ['proof']).
% 0.20/0.44  # SZS output end CNFRefutation
% 0.20/0.44  # Proof object total steps             : 167
% 0.20/0.44  # Proof object clause steps            : 106
% 0.20/0.44  # Proof object formula steps           : 61
% 0.20/0.44  # Proof object conjectures             : 19
% 0.20/0.44  # Proof object clause conjectures      : 16
% 0.20/0.44  # Proof object formula conjectures     : 3
% 0.20/0.44  # Proof object initial clauses used    : 33
% 0.20/0.44  # Proof object initial formulas used   : 30
% 0.20/0.44  # Proof object generating inferences   : 39
% 0.20/0.44  # Proof object simplifying inferences  : 94
% 0.20/0.44  # Training examples: 0 positive, 0 negative
% 0.20/0.44  # Parsed axioms                        : 30
% 0.20/0.44  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.44  # Initial clauses                      : 42
% 0.20/0.44  # Removed in clause preprocessing      : 7
% 0.20/0.44  # Initial clauses in saturation        : 35
% 0.20/0.44  # Processed clauses                    : 1204
% 0.20/0.44  # ...of these trivial                  : 44
% 0.20/0.44  # ...subsumed                          : 869
% 0.20/0.44  # ...remaining for further processing  : 291
% 0.20/0.44  # Other redundant clauses eliminated   : 14
% 0.20/0.44  # Clauses deleted for lack of memory   : 0
% 0.20/0.44  # Backward-subsumed                    : 7
% 0.20/0.44  # Backward-rewritten                   : 69
% 0.20/0.44  # Generated clauses                    : 4564
% 0.20/0.44  # ...of the previous two non-trivial   : 3464
% 0.20/0.44  # Contextual simplify-reflections      : 0
% 0.20/0.44  # Paramodulations                      : 4537
% 0.20/0.44  # Factorizations                       : 12
% 0.20/0.44  # Equation resolutions                 : 15
% 0.20/0.44  # Propositional unsat checks           : 0
% 0.20/0.44  #    Propositional check models        : 0
% 0.20/0.44  #    Propositional check unsatisfiable : 0
% 0.20/0.44  #    Propositional clauses             : 0
% 0.20/0.44  #    Propositional clauses after purity: 0
% 0.20/0.44  #    Propositional unsat core size     : 0
% 0.20/0.44  #    Propositional preprocessing time  : 0.000
% 0.20/0.44  #    Propositional encoding time       : 0.000
% 0.20/0.44  #    Propositional solver time         : 0.000
% 0.20/0.44  #    Success case prop preproc time    : 0.000
% 0.20/0.44  #    Success case prop encoding time   : 0.000
% 0.20/0.44  #    Success case prop solver time     : 0.000
% 0.20/0.44  # Current number of processed clauses  : 175
% 0.20/0.44  #    Positive orientable unit clauses  : 74
% 0.20/0.44  #    Positive unorientable unit clauses: 1
% 0.20/0.44  #    Negative unit clauses             : 27
% 0.20/0.44  #    Non-unit-clauses                  : 73
% 0.20/0.44  # Current number of unprocessed clauses: 2263
% 0.20/0.44  # ...number of literals in the above   : 4125
% 0.20/0.44  # Current number of archived formulas  : 0
% 0.20/0.44  # Current number of archived clauses   : 118
% 0.20/0.44  # Clause-clause subsumption calls (NU) : 1625
% 0.20/0.44  # Rec. Clause-clause subsumption calls : 1437
% 0.20/0.44  # Non-unit clause-clause subsumptions  : 84
% 0.20/0.44  # Unit Clause-clause subsumption calls : 466
% 0.20/0.44  # Rewrite failures with RHS unbound    : 0
% 0.20/0.44  # BW rewrite match attempts            : 166
% 0.20/0.44  # BW rewrite match successes           : 34
% 0.20/0.44  # Condensation attempts                : 0
% 0.20/0.45  # Condensation successes               : 0
% 0.20/0.45  # Termbank termtop insertions          : 45532
% 0.20/0.45  
% 0.20/0.45  # -------------------------------------------------
% 0.20/0.45  # User time                : 0.090 s
% 0.20/0.45  # System time              : 0.007 s
% 0.20/0.45  # Total time               : 0.097 s
% 0.20/0.45  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------
