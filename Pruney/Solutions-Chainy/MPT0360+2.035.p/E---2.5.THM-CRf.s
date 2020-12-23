%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:46:13 EST 2020

% Result     : Theorem 0.39s
% Output     : CNFRefutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 792 expanded)
%              Number of clauses        :   76 ( 320 expanded)
%              Number of leaves         :   31 ( 228 expanded)
%              Depth                    :   18
%              Number of atoms          :  323 (1553 expanded)
%              Number of equality atoms :  113 ( 709 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    7 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t40_subset_1,conjecture,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => ( ( r1_tarski(X2,X3)
          & r1_tarski(X2,k3_subset_1(X1,X3)) )
       => X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_subset_1)).

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t95_xboole_1,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(t6_boole,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

fof(t64_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))
    <=> ( r2_hidden(X1,X2)
        & X1 != X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(t75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(t92_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => r1_tarski(X1,k3_tarski(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_zfmisc_1)).

fof(t99_zfmisc_1,axiom,(
    ! [X1] : k3_tarski(k1_zfmisc_1(X1)) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).

fof(t91_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(idempotence_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(t92_xboole_1,axiom,(
    ! [X1] : k5_xboole_0(X1,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(t5_boole,axiom,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(d4_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k3_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] :
              ( r2_hidden(X3,X4)
              & r2_hidden(X4,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tarski)).

fof(s1_xboole_0__e1_138_1__zfmisc_1,axiom,(
    ! [X1] :
    ? [X2] :
    ! [X3] :
      ( r2_hidden(X3,X2)
    <=> ( r2_hidden(X3,k3_tarski(X1))
        & ? [X4] :
            ( X3 = X4
            & ? [X5] :
                ( r2_hidden(X5,X4)
                & r2_hidden(X5,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s1_xboole_0__e1_138_1__zfmisc_1)).

fof(t2_zfmisc_1,axiom,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_zfmisc_1)).

fof(t31_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => ( r1_tarski(X2,X3)
          <=> r1_tarski(k3_subset_1(X1,X3),k3_subset_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_subset_1)).

fof(dt_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(involutiveness_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,k3_subset_1(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(t38_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ( r1_tarski(X2,k3_subset_1(X1,X2))
      <=> X2 = k1_subset_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_subset_1)).

fof(d3_subset_1,axiom,(
    ! [X1] : k1_subset_1(X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(c_0_31,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(X1))
       => ( ( r1_tarski(X2,X3)
            & r1_tarski(X2,k3_subset_1(X1,X3)) )
         => X2 = k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t40_subset_1])).

fof(c_0_32,plain,(
    ! [X98,X99] :
      ( ( ~ m1_subset_1(X99,X98)
        | r2_hidden(X99,X98)
        | v1_xboole_0(X98) )
      & ( ~ r2_hidden(X99,X98)
        | m1_subset_1(X99,X98)
        | v1_xboole_0(X98) )
      & ( ~ m1_subset_1(X99,X98)
        | v1_xboole_0(X99)
        | ~ v1_xboole_0(X98) )
      & ( ~ v1_xboole_0(X99)
        | m1_subset_1(X99,X98)
        | ~ v1_xboole_0(X98) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

fof(c_0_33,negated_conjecture,
    ( m1_subset_1(esk12_0,k1_zfmisc_1(esk10_0))
    & r1_tarski(esk11_0,esk12_0)
    & r1_tarski(esk11_0,k3_subset_1(esk10_0,esk12_0))
    & esk11_0 != k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_31])])])).

fof(c_0_34,plain,(
    ! [X82,X83] : k3_tarski(k2_tarski(X82,X83)) = k2_xboole_0(X82,X83) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_35,plain,(
    ! [X37,X38] : k1_enumset1(X37,X37,X38) = k2_tarski(X37,X38) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

cnf(c_0_36,plain,
    ( v1_xboole_0(X1)
    | ~ m1_subset_1(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_37,negated_conjecture,
    ( m1_subset_1(esk12_0,k1_zfmisc_1(esk10_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_38,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_39,plain,(
    ! [X34,X35] : k3_xboole_0(X34,X35) = k5_xboole_0(k5_xboole_0(X34,X35),k2_xboole_0(X34,X35)) ),
    inference(variable_rename,[status(thm)],[t95_xboole_1])).

cnf(c_0_40,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_41,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

fof(c_0_42,plain,(
    ! [X39,X40,X41] : k2_enumset1(X39,X39,X40,X41) = k1_enumset1(X39,X40,X41) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_43,plain,(
    ! [X42,X43,X44,X45] : k3_enumset1(X42,X42,X43,X44,X45) = k2_enumset1(X42,X43,X44,X45) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_44,plain,(
    ! [X27] :
      ( ~ v1_xboole_0(X27)
      | X27 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_boole])])).

cnf(c_0_45,negated_conjecture,
    ( v1_xboole_0(esk12_0)
    | ~ v1_xboole_0(k1_zfmisc_1(esk10_0)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_46,negated_conjecture,
    ( v1_xboole_0(k1_zfmisc_1(esk10_0))
    | r2_hidden(esk12_0,k1_zfmisc_1(esk10_0)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_37])).

fof(c_0_47,plain,(
    ! [X92,X93,X94] :
      ( ( r2_hidden(X92,X93)
        | ~ r2_hidden(X92,k4_xboole_0(X93,k1_tarski(X94))) )
      & ( X92 != X94
        | ~ r2_hidden(X92,k4_xboole_0(X93,k1_tarski(X94))) )
      & ( ~ r2_hidden(X92,X93)
        | X92 = X94
        | r2_hidden(X92,k4_xboole_0(X93,k1_tarski(X94))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_zfmisc_1])])])).

fof(c_0_48,plain,(
    ! [X36] : k2_tarski(X36,X36) = k1_tarski(X36) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_49,plain,(
    ! [X17,X18] : k4_xboole_0(X17,X18) = k5_xboole_0(X17,k3_xboole_0(X17,X18)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_50,plain,
    ( k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_51,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_52,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_53,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

fof(c_0_54,plain,(
    ! [X46,X47,X48,X49,X50] : k4_enumset1(X46,X46,X47,X48,X49,X50) = k3_enumset1(X46,X47,X48,X49,X50) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_55,plain,(
    ! [X51,X52,X53,X54,X55,X56] : k5_enumset1(X51,X51,X52,X53,X54,X55,X56) = k4_enumset1(X51,X52,X53,X54,X55,X56) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_56,plain,(
    ! [X57,X58,X59,X60,X61,X62,X63] : k6_enumset1(X57,X57,X58,X59,X60,X61,X62,X63) = k5_enumset1(X57,X58,X59,X60,X61,X62,X63) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_57,plain,(
    ! [X95,X96] :
      ( ~ r2_hidden(X95,X96)
      | r1_tarski(X95,k3_tarski(X96)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t92_zfmisc_1])])).

cnf(c_0_58,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_59,negated_conjecture,
    ( v1_xboole_0(esk12_0)
    | r2_hidden(esk12_0,k1_zfmisc_1(esk10_0)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

fof(c_0_60,plain,(
    ! [X97] : k3_tarski(k1_zfmisc_1(X97)) = X97 ),
    inference(variable_rename,[status(thm)],[t99_zfmisc_1])).

cnf(c_0_61,plain,
    ( X1 != X2
    | ~ r2_hidden(X1,k4_xboole_0(X3,k1_tarski(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_62,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_63,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_64,plain,
    ( k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50,c_0_51]),c_0_52]),c_0_53])).

cnf(c_0_65,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_66,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_67,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

fof(c_0_68,plain,(
    ! [X30,X31,X32] : k5_xboole_0(k5_xboole_0(X30,X31),X32) = k5_xboole_0(X30,k5_xboole_0(X31,X32)) ),
    inference(variable_rename,[status(thm)],[t91_xboole_1])).

fof(c_0_69,plain,(
    ! [X14] : k2_xboole_0(X14,X14) = X14 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).

fof(c_0_70,plain,(
    ! [X19,X20,X21] :
      ( ~ r1_tarski(X19,X20)
      | ~ r1_tarski(X20,X21)
      | r1_tarski(X19,X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

cnf(c_0_71,plain,
    ( r1_tarski(X1,k3_tarski(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_72,negated_conjecture,
    ( esk12_0 = k1_xboole_0
    | r2_hidden(esk12_0,k1_zfmisc_1(esk10_0)) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_73,plain,
    ( k3_tarski(k1_zfmisc_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_74,plain,
    ( X1 != X2
    | ~ r2_hidden(X1,k5_xboole_0(X3,k5_xboole_0(k5_xboole_0(X3,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)),k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_62]),c_0_41]),c_0_63]),c_0_52]),c_0_53]),c_0_64]),c_0_65]),c_0_65]),c_0_65]),c_0_66]),c_0_66]),c_0_66]),c_0_67]),c_0_67]),c_0_67])).

cnf(c_0_75,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_76,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

fof(c_0_77,plain,(
    ! [X33] : k5_xboole_0(X33,X33) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t92_xboole_1])).

fof(c_0_78,plain,(
    ! [X23] : k5_xboole_0(X23,k1_xboole_0) = X23 ),
    inference(variable_rename,[status(thm)],[t5_boole])).

fof(c_0_79,plain,(
    ! [X64,X65,X66,X67,X68,X69] :
      ( ( ~ r2_hidden(X66,X65)
        | r1_tarski(X66,X64)
        | X65 != k1_zfmisc_1(X64) )
      & ( ~ r1_tarski(X67,X64)
        | r2_hidden(X67,X65)
        | X65 != k1_zfmisc_1(X64) )
      & ( ~ r2_hidden(esk3_2(X68,X69),X69)
        | ~ r1_tarski(esk3_2(X68,X69),X68)
        | X69 = k1_zfmisc_1(X68) )
      & ( r2_hidden(esk3_2(X68,X69),X69)
        | r1_tarski(esk3_2(X68,X69),X68)
        | X69 = k1_zfmisc_1(X68) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

cnf(c_0_80,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_81,negated_conjecture,
    ( esk12_0 = k1_xboole_0
    | r1_tarski(esk12_0,esk10_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_73])).

cnf(c_0_82,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,k5_xboole_0(X2,k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))))))) ),
    inference(er,[status(thm)],[inference(rw,[status(thm)],[c_0_74,c_0_75])])).

cnf(c_0_83,plain,
    ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_76,c_0_51]),c_0_52]),c_0_53]),c_0_65]),c_0_66]),c_0_67])).

cnf(c_0_84,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_77])).

cnf(c_0_85,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_78])).

fof(c_0_86,plain,(
    ! [X71,X72,X73,X75,X76,X77,X78,X80] :
      ( ( r2_hidden(X73,esk4_3(X71,X72,X73))
        | ~ r2_hidden(X73,X72)
        | X72 != k3_tarski(X71) )
      & ( r2_hidden(esk4_3(X71,X72,X73),X71)
        | ~ r2_hidden(X73,X72)
        | X72 != k3_tarski(X71) )
      & ( ~ r2_hidden(X75,X76)
        | ~ r2_hidden(X76,X71)
        | r2_hidden(X75,X72)
        | X72 != k3_tarski(X71) )
      & ( ~ r2_hidden(esk5_2(X77,X78),X78)
        | ~ r2_hidden(esk5_2(X77,X78),X80)
        | ~ r2_hidden(X80,X77)
        | X78 = k3_tarski(X77) )
      & ( r2_hidden(esk5_2(X77,X78),esk6_2(X77,X78))
        | r2_hidden(esk5_2(X77,X78),X78)
        | X78 = k3_tarski(X77) )
      & ( r2_hidden(esk6_2(X77,X78),X77)
        | r2_hidden(esk5_2(X77,X78),X78)
        | X78 = k3_tarski(X77) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tarski])])])])])])).

cnf(c_0_87,plain,
    ( r2_hidden(X1,X3)
    | ~ r1_tarski(X1,X2)
    | X3 != k1_zfmisc_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_79])).

cnf(c_0_88,negated_conjecture,
    ( esk12_0 = k1_xboole_0
    | r1_tarski(X1,esk10_0)
    | ~ r1_tarski(X1,esk12_0) ),
    inference(spm,[status(thm)],[c_0_80,c_0_81])).

cnf(c_0_89,negated_conjecture,
    ( r1_tarski(esk11_0,esk12_0) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

fof(c_0_90,plain,(
    ! [X84,X86,X89,X90,X91] :
      ( ( r2_hidden(X86,k3_tarski(X84))
        | ~ r2_hidden(X86,esk7_1(X84)) )
      & ( X86 = esk8_2(X84,X86)
        | ~ r2_hidden(X86,esk7_1(X84)) )
      & ( r2_hidden(esk9_2(X84,X86),esk8_2(X84,X86))
        | ~ r2_hidden(X86,esk7_1(X84)) )
      & ( r2_hidden(esk9_2(X84,X86),X84)
        | ~ r2_hidden(X86,esk7_1(X84)) )
      & ( ~ r2_hidden(X89,k3_tarski(X84))
        | X89 != X90
        | ~ r2_hidden(X91,X90)
        | ~ r2_hidden(X91,X84)
        | r2_hidden(X89,esk7_1(X84)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[s1_xboole_0__e1_138_1__zfmisc_1])])])])])])).

cnf(c_0_91,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_84]),c_0_85]),c_0_84])).

cnf(c_0_92,plain,
    ( r2_hidden(esk6_2(X1,X2),X1)
    | r2_hidden(esk5_2(X1,X2),X2)
    | X2 = k3_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_86])).

cnf(c_0_93,plain,
    ( k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t2_zfmisc_1])).

cnf(c_0_94,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(er,[status(thm)],[c_0_87])).

cnf(c_0_95,negated_conjecture,
    ( esk12_0 = k1_xboole_0
    | r1_tarski(esk11_0,esk10_0) ),
    inference(spm,[status(thm)],[c_0_88,c_0_89])).

cnf(c_0_96,plain,
    ( r2_hidden(X1,k3_tarski(X2))
    | ~ r2_hidden(X1,esk7_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_90])).

cnf(c_0_97,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk5_2(k1_xboole_0,X1),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_92]),c_0_93])).

cnf(c_0_98,plain,
    ( m1_subset_1(X1,X2)
    | v1_xboole_0(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_99,negated_conjecture,
    ( esk12_0 = k1_xboole_0
    | r2_hidden(esk11_0,k1_zfmisc_1(esk10_0)) ),
    inference(spm,[status(thm)],[c_0_94,c_0_95])).

cnf(c_0_100,plain,
    ( esk7_1(X1) = k1_xboole_0
    | r2_hidden(esk5_2(k1_xboole_0,esk7_1(X1)),k3_tarski(X1)) ),
    inference(spm,[status(thm)],[c_0_96,c_0_97])).

fof(c_0_101,plain,(
    ! [X105,X106,X107] :
      ( ( ~ r1_tarski(X106,X107)
        | r1_tarski(k3_subset_1(X105,X107),k3_subset_1(X105,X106))
        | ~ m1_subset_1(X107,k1_zfmisc_1(X105))
        | ~ m1_subset_1(X106,k1_zfmisc_1(X105)) )
      & ( ~ r1_tarski(k3_subset_1(X105,X107),k3_subset_1(X105,X106))
        | r1_tarski(X106,X107)
        | ~ m1_subset_1(X107,k1_zfmisc_1(X105))
        | ~ m1_subset_1(X106,k1_zfmisc_1(X105)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_subset_1])])])])).

fof(c_0_102,plain,(
    ! [X101,X102] :
      ( ~ m1_subset_1(X102,k1_zfmisc_1(X101))
      | m1_subset_1(k3_subset_1(X101,X102),k1_zfmisc_1(X101)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).

cnf(c_0_103,negated_conjecture,
    ( esk12_0 = k1_xboole_0
    | m1_subset_1(esk11_0,k1_zfmisc_1(esk10_0))
    | v1_xboole_0(k1_zfmisc_1(esk10_0)) ),
    inference(spm,[status(thm)],[c_0_98,c_0_99])).

cnf(c_0_104,plain,
    ( r1_tarski(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_79])).

cnf(c_0_105,plain,
    ( esk7_1(X1) = k3_tarski(X2)
    | r2_hidden(esk5_2(X2,esk7_1(X1)),k3_tarski(X1))
    | r2_hidden(esk6_2(X2,esk7_1(X1)),X2) ),
    inference(spm,[status(thm)],[c_0_96,c_0_92])).

cnf(c_0_106,plain,
    ( esk7_1(k1_xboole_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_93]),c_0_91])).

cnf(c_0_107,plain,
    ( r1_tarski(X3,X2)
    | ~ r1_tarski(k3_subset_1(X1,X2),k3_subset_1(X1,X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_101])).

cnf(c_0_108,plain,
    ( m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_102])).

cnf(c_0_109,negated_conjecture,
    ( esk12_0 = k1_xboole_0
    | m1_subset_1(esk11_0,k1_zfmisc_1(esk10_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_103]),c_0_58])).

fof(c_0_110,plain,(
    ! [X103,X104] :
      ( ~ m1_subset_1(X104,k1_zfmisc_1(X103))
      | k3_subset_1(X103,k3_subset_1(X103,X104)) = X104 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).

cnf(c_0_111,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(er,[status(thm)],[c_0_104])).

cnf(c_0_112,plain,
    ( k3_tarski(X1) = k1_xboole_0
    | r2_hidden(esk6_2(X1,k1_xboole_0),X1) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_106]),c_0_93]),c_0_91])).

cnf(c_0_113,negated_conjecture,
    ( r1_tarski(esk12_0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk10_0))
    | ~ r1_tarski(k3_subset_1(esk10_0,X1),k3_subset_1(esk10_0,esk12_0)) ),
    inference(spm,[status(thm)],[c_0_107,c_0_37])).

cnf(c_0_114,negated_conjecture,
    ( esk12_0 = k1_xboole_0
    | m1_subset_1(k3_subset_1(esk10_0,esk11_0),k1_zfmisc_1(esk10_0)) ),
    inference(spm,[status(thm)],[c_0_108,c_0_109])).

cnf(c_0_115,plain,
    ( k3_subset_1(X2,k3_subset_1(X2,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_110])).

fof(c_0_116,plain,(
    ! [X108,X109] :
      ( ( ~ r1_tarski(X109,k3_subset_1(X108,X109))
        | X109 = k1_subset_1(X108)
        | ~ m1_subset_1(X109,k1_zfmisc_1(X108)) )
      & ( X109 != k1_subset_1(X108)
        | r1_tarski(X109,k3_subset_1(X108,X109))
        | ~ m1_subset_1(X109,k1_zfmisc_1(X108)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_subset_1])])])).

fof(c_0_117,plain,(
    ! [X100] : k1_subset_1(X100) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[d3_subset_1])).

fof(c_0_118,plain,(
    ! [X8,X9,X10,X11,X12] :
      ( ( ~ r1_tarski(X8,X9)
        | ~ r2_hidden(X10,X8)
        | r2_hidden(X10,X9) )
      & ( r2_hidden(esk1_2(X11,X12),X11)
        | r1_tarski(X11,X12) )
      & ( ~ r2_hidden(esk1_2(X11,X12),X12)
        | r1_tarski(X11,X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_119,negated_conjecture,
    ( r1_tarski(X1,esk12_0)
    | ~ r1_tarski(X1,esk11_0) ),
    inference(spm,[status(thm)],[c_0_80,c_0_89])).

cnf(c_0_120,plain,
    ( X1 = k1_xboole_0
    | r1_tarski(esk6_2(k1_zfmisc_1(X1),k1_xboole_0),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111,c_0_112]),c_0_73])).

cnf(c_0_121,negated_conjecture,
    ( esk11_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_122,negated_conjecture,
    ( esk12_0 = k1_xboole_0
    | r1_tarski(esk12_0,k3_subset_1(esk10_0,esk11_0))
    | ~ r1_tarski(k3_subset_1(esk10_0,k3_subset_1(esk10_0,esk11_0)),k3_subset_1(esk10_0,esk12_0)) ),
    inference(spm,[status(thm)],[c_0_113,c_0_114])).

cnf(c_0_123,negated_conjecture,
    ( k3_subset_1(esk10_0,k3_subset_1(esk10_0,esk11_0)) = esk11_0
    | esk12_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_115,c_0_109])).

cnf(c_0_124,negated_conjecture,
    ( r1_tarski(esk11_0,k3_subset_1(esk10_0,esk12_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_125,plain,
    ( X1 = k1_subset_1(X2)
    | ~ r1_tarski(X1,k3_subset_1(X2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_116])).

cnf(c_0_126,plain,
    ( k1_subset_1(X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_117])).

cnf(c_0_127,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_118])).

cnf(c_0_128,negated_conjecture,
    ( r1_tarski(esk6_2(k1_zfmisc_1(esk11_0),k1_xboole_0),esk12_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_119,c_0_120]),c_0_121])).

cnf(c_0_129,negated_conjecture,
    ( esk12_0 = k1_xboole_0
    | r1_tarski(esk12_0,k3_subset_1(esk10_0,esk11_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_122,c_0_123]),c_0_124])])).

cnf(c_0_130,plain,
    ( X1 = k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,k3_subset_1(X2,X1)) ),
    inference(rw,[status(thm)],[c_0_125,c_0_126])).

cnf(c_0_131,negated_conjecture,
    ( r2_hidden(X1,esk12_0)
    | ~ r2_hidden(X1,esk6_2(k1_zfmisc_1(esk11_0),k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_127,c_0_128])).

cnf(c_0_132,plain,
    ( r2_hidden(esk5_2(X1,X2),esk6_2(X1,X2))
    | r2_hidden(esk5_2(X1,X2),X2)
    | X2 = k3_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_86])).

cnf(c_0_133,negated_conjecture,
    ( esk12_0 = k1_xboole_0
    | r1_tarski(X1,k3_subset_1(esk10_0,esk11_0))
    | ~ r1_tarski(X1,esk12_0) ),
    inference(spm,[status(thm)],[c_0_80,c_0_129])).

cnf(c_0_134,negated_conjecture,
    ( esk12_0 = k1_xboole_0
    | ~ r1_tarski(esk11_0,k3_subset_1(esk10_0,esk11_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_130,c_0_109]),c_0_121])).

cnf(c_0_135,negated_conjecture,
    ( r2_hidden(esk5_2(k1_zfmisc_1(esk11_0),k1_xboole_0),esk12_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_131,c_0_132]),c_0_73]),c_0_121]),c_0_91])).

cnf(c_0_136,negated_conjecture,
    ( esk12_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_133,c_0_89]),c_0_134])).

cnf(c_0_137,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_135,c_0_136]),c_0_91]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:56:20 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.39/0.58  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_S2mI
% 0.39/0.58  # and selection function SelectCQArNTNpEqFirst.
% 0.39/0.58  #
% 0.39/0.58  # Preprocessing time       : 0.029 s
% 0.39/0.58  # Presaturation interreduction done
% 0.39/0.58  
% 0.39/0.58  # Proof found!
% 0.39/0.58  # SZS status Theorem
% 0.39/0.58  # SZS output start CNFRefutation
% 0.39/0.58  fof(t40_subset_1, conjecture, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>((r1_tarski(X2,X3)&r1_tarski(X2,k3_subset_1(X1,X3)))=>X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_subset_1)).
% 0.39/0.58  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 0.39/0.58  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.39/0.58  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.39/0.58  fof(t95_xboole_1, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_xboole_1)).
% 0.39/0.58  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.39/0.58  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.39/0.58  fof(t6_boole, axiom, ![X1]:(v1_xboole_0(X1)=>X1=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_boole)).
% 0.39/0.58  fof(t64_zfmisc_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))<=>(r2_hidden(X1,X2)&X1!=X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 0.39/0.58  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.39/0.58  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.39/0.58  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 0.39/0.58  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 0.39/0.58  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 0.39/0.58  fof(t92_zfmisc_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>r1_tarski(X1,k3_tarski(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_zfmisc_1)).
% 0.39/0.58  fof(t99_zfmisc_1, axiom, ![X1]:k3_tarski(k1_zfmisc_1(X1))=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 0.39/0.58  fof(t91_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 0.39/0.58  fof(idempotence_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 0.39/0.58  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 0.39/0.58  fof(t92_xboole_1, axiom, ![X1]:k5_xboole_0(X1,X1)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 0.39/0.58  fof(t5_boole, axiom, ![X1]:k5_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 0.39/0.58  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 0.39/0.58  fof(d4_tarski, axiom, ![X1, X2]:(X2=k3_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:(r2_hidden(X3,X4)&r2_hidden(X4,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tarski)).
% 0.39/0.58  fof(s1_xboole_0__e1_138_1__zfmisc_1, axiom, ![X1]:?[X2]:![X3]:(r2_hidden(X3,X2)<=>(r2_hidden(X3,k3_tarski(X1))&?[X4]:(X3=X4&?[X5]:(r2_hidden(X5,X4)&r2_hidden(X5,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', s1_xboole_0__e1_138_1__zfmisc_1)).
% 0.39/0.58  fof(t2_zfmisc_1, axiom, k3_tarski(k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_zfmisc_1)).
% 0.39/0.58  fof(t31_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(r1_tarski(X2,X3)<=>r1_tarski(k3_subset_1(X1,X3),k3_subset_1(X1,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_subset_1)).
% 0.39/0.58  fof(dt_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 0.39/0.58  fof(involutiveness_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,k3_subset_1(X1,X2))=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 0.39/0.58  fof(t38_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>(r1_tarski(X2,k3_subset_1(X1,X2))<=>X2=k1_subset_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_subset_1)).
% 0.39/0.58  fof(d3_subset_1, axiom, ![X1]:k1_subset_1(X1)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_subset_1)).
% 0.39/0.58  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.39/0.58  fof(c_0_31, negated_conjecture, ~(![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>((r1_tarski(X2,X3)&r1_tarski(X2,k3_subset_1(X1,X3)))=>X2=k1_xboole_0))), inference(assume_negation,[status(cth)],[t40_subset_1])).
% 0.39/0.58  fof(c_0_32, plain, ![X98, X99]:(((~m1_subset_1(X99,X98)|r2_hidden(X99,X98)|v1_xboole_0(X98))&(~r2_hidden(X99,X98)|m1_subset_1(X99,X98)|v1_xboole_0(X98)))&((~m1_subset_1(X99,X98)|v1_xboole_0(X99)|~v1_xboole_0(X98))&(~v1_xboole_0(X99)|m1_subset_1(X99,X98)|~v1_xboole_0(X98)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 0.39/0.58  fof(c_0_33, negated_conjecture, (m1_subset_1(esk12_0,k1_zfmisc_1(esk10_0))&((r1_tarski(esk11_0,esk12_0)&r1_tarski(esk11_0,k3_subset_1(esk10_0,esk12_0)))&esk11_0!=k1_xboole_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_31])])])).
% 0.39/0.58  fof(c_0_34, plain, ![X82, X83]:k3_tarski(k2_tarski(X82,X83))=k2_xboole_0(X82,X83), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.39/0.58  fof(c_0_35, plain, ![X37, X38]:k1_enumset1(X37,X37,X38)=k2_tarski(X37,X38), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.39/0.58  cnf(c_0_36, plain, (v1_xboole_0(X1)|~m1_subset_1(X1,X2)|~v1_xboole_0(X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.39/0.58  cnf(c_0_37, negated_conjecture, (m1_subset_1(esk12_0,k1_zfmisc_1(esk10_0))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.39/0.58  cnf(c_0_38, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.39/0.58  fof(c_0_39, plain, ![X34, X35]:k3_xboole_0(X34,X35)=k5_xboole_0(k5_xboole_0(X34,X35),k2_xboole_0(X34,X35)), inference(variable_rename,[status(thm)],[t95_xboole_1])).
% 0.39/0.58  cnf(c_0_40, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.39/0.58  cnf(c_0_41, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.39/0.58  fof(c_0_42, plain, ![X39, X40, X41]:k2_enumset1(X39,X39,X40,X41)=k1_enumset1(X39,X40,X41), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.39/0.58  fof(c_0_43, plain, ![X42, X43, X44, X45]:k3_enumset1(X42,X42,X43,X44,X45)=k2_enumset1(X42,X43,X44,X45), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.39/0.58  fof(c_0_44, plain, ![X27]:(~v1_xboole_0(X27)|X27=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_boole])])).
% 0.39/0.58  cnf(c_0_45, negated_conjecture, (v1_xboole_0(esk12_0)|~v1_xboole_0(k1_zfmisc_1(esk10_0))), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.39/0.58  cnf(c_0_46, negated_conjecture, (v1_xboole_0(k1_zfmisc_1(esk10_0))|r2_hidden(esk12_0,k1_zfmisc_1(esk10_0))), inference(spm,[status(thm)],[c_0_38, c_0_37])).
% 0.39/0.58  fof(c_0_47, plain, ![X92, X93, X94]:(((r2_hidden(X92,X93)|~r2_hidden(X92,k4_xboole_0(X93,k1_tarski(X94))))&(X92!=X94|~r2_hidden(X92,k4_xboole_0(X93,k1_tarski(X94)))))&(~r2_hidden(X92,X93)|X92=X94|r2_hidden(X92,k4_xboole_0(X93,k1_tarski(X94))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_zfmisc_1])])])).
% 0.39/0.58  fof(c_0_48, plain, ![X36]:k2_tarski(X36,X36)=k1_tarski(X36), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.39/0.58  fof(c_0_49, plain, ![X17, X18]:k4_xboole_0(X17,X18)=k5_xboole_0(X17,k3_xboole_0(X17,X18)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.39/0.58  cnf(c_0_50, plain, (k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.39/0.58  cnf(c_0_51, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_40, c_0_41])).
% 0.39/0.58  cnf(c_0_52, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.39/0.58  cnf(c_0_53, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.39/0.58  fof(c_0_54, plain, ![X46, X47, X48, X49, X50]:k4_enumset1(X46,X46,X47,X48,X49,X50)=k3_enumset1(X46,X47,X48,X49,X50), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.39/0.58  fof(c_0_55, plain, ![X51, X52, X53, X54, X55, X56]:k5_enumset1(X51,X51,X52,X53,X54,X55,X56)=k4_enumset1(X51,X52,X53,X54,X55,X56), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.39/0.58  fof(c_0_56, plain, ![X57, X58, X59, X60, X61, X62, X63]:k6_enumset1(X57,X57,X58,X59,X60,X61,X62,X63)=k5_enumset1(X57,X58,X59,X60,X61,X62,X63), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.39/0.58  fof(c_0_57, plain, ![X95, X96]:(~r2_hidden(X95,X96)|r1_tarski(X95,k3_tarski(X96))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t92_zfmisc_1])])).
% 0.39/0.58  cnf(c_0_58, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.39/0.58  cnf(c_0_59, negated_conjecture, (v1_xboole_0(esk12_0)|r2_hidden(esk12_0,k1_zfmisc_1(esk10_0))), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.39/0.58  fof(c_0_60, plain, ![X97]:k3_tarski(k1_zfmisc_1(X97))=X97, inference(variable_rename,[status(thm)],[t99_zfmisc_1])).
% 0.39/0.58  cnf(c_0_61, plain, (X1!=X2|~r2_hidden(X1,k4_xboole_0(X3,k1_tarski(X2)))), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.39/0.58  cnf(c_0_62, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.39/0.58  cnf(c_0_63, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.39/0.58  cnf(c_0_64, plain, (k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50, c_0_51]), c_0_52]), c_0_53])).
% 0.39/0.58  cnf(c_0_65, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.39/0.58  cnf(c_0_66, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.39/0.58  cnf(c_0_67, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.39/0.58  fof(c_0_68, plain, ![X30, X31, X32]:k5_xboole_0(k5_xboole_0(X30,X31),X32)=k5_xboole_0(X30,k5_xboole_0(X31,X32)), inference(variable_rename,[status(thm)],[t91_xboole_1])).
% 0.39/0.58  fof(c_0_69, plain, ![X14]:k2_xboole_0(X14,X14)=X14, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).
% 0.39/0.58  fof(c_0_70, plain, ![X19, X20, X21]:(~r1_tarski(X19,X20)|~r1_tarski(X20,X21)|r1_tarski(X19,X21)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 0.39/0.58  cnf(c_0_71, plain, (r1_tarski(X1,k3_tarski(X2))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.39/0.58  cnf(c_0_72, negated_conjecture, (esk12_0=k1_xboole_0|r2_hidden(esk12_0,k1_zfmisc_1(esk10_0))), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.39/0.58  cnf(c_0_73, plain, (k3_tarski(k1_zfmisc_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.39/0.58  cnf(c_0_74, plain, (X1!=X2|~r2_hidden(X1,k5_xboole_0(X3,k5_xboole_0(k5_xboole_0(X3,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)),k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61, c_0_62]), c_0_41]), c_0_63]), c_0_52]), c_0_53]), c_0_64]), c_0_65]), c_0_65]), c_0_65]), c_0_66]), c_0_66]), c_0_66]), c_0_67]), c_0_67]), c_0_67])).
% 0.39/0.58  cnf(c_0_75, plain, (k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.39/0.58  cnf(c_0_76, plain, (k2_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_69])).
% 0.39/0.58  fof(c_0_77, plain, ![X33]:k5_xboole_0(X33,X33)=k1_xboole_0, inference(variable_rename,[status(thm)],[t92_xboole_1])).
% 0.39/0.58  fof(c_0_78, plain, ![X23]:k5_xboole_0(X23,k1_xboole_0)=X23, inference(variable_rename,[status(thm)],[t5_boole])).
% 0.39/0.58  fof(c_0_79, plain, ![X64, X65, X66, X67, X68, X69]:(((~r2_hidden(X66,X65)|r1_tarski(X66,X64)|X65!=k1_zfmisc_1(X64))&(~r1_tarski(X67,X64)|r2_hidden(X67,X65)|X65!=k1_zfmisc_1(X64)))&((~r2_hidden(esk3_2(X68,X69),X69)|~r1_tarski(esk3_2(X68,X69),X68)|X69=k1_zfmisc_1(X68))&(r2_hidden(esk3_2(X68,X69),X69)|r1_tarski(esk3_2(X68,X69),X68)|X69=k1_zfmisc_1(X68)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 0.39/0.58  cnf(c_0_80, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_70])).
% 0.39/0.58  cnf(c_0_81, negated_conjecture, (esk12_0=k1_xboole_0|r1_tarski(esk12_0,esk10_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_73])).
% 0.39/0.58  cnf(c_0_82, plain, (~r2_hidden(X1,k5_xboole_0(X2,k5_xboole_0(X2,k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))))))), inference(er,[status(thm)],[inference(rw,[status(thm)],[c_0_74, c_0_75])])).
% 0.39/0.58  cnf(c_0_83, plain, (k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_76, c_0_51]), c_0_52]), c_0_53]), c_0_65]), c_0_66]), c_0_67])).
% 0.39/0.58  cnf(c_0_84, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_77])).
% 0.39/0.58  cnf(c_0_85, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_78])).
% 0.39/0.58  fof(c_0_86, plain, ![X71, X72, X73, X75, X76, X77, X78, X80]:((((r2_hidden(X73,esk4_3(X71,X72,X73))|~r2_hidden(X73,X72)|X72!=k3_tarski(X71))&(r2_hidden(esk4_3(X71,X72,X73),X71)|~r2_hidden(X73,X72)|X72!=k3_tarski(X71)))&(~r2_hidden(X75,X76)|~r2_hidden(X76,X71)|r2_hidden(X75,X72)|X72!=k3_tarski(X71)))&((~r2_hidden(esk5_2(X77,X78),X78)|(~r2_hidden(esk5_2(X77,X78),X80)|~r2_hidden(X80,X77))|X78=k3_tarski(X77))&((r2_hidden(esk5_2(X77,X78),esk6_2(X77,X78))|r2_hidden(esk5_2(X77,X78),X78)|X78=k3_tarski(X77))&(r2_hidden(esk6_2(X77,X78),X77)|r2_hidden(esk5_2(X77,X78),X78)|X78=k3_tarski(X77))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tarski])])])])])])).
% 0.39/0.58  cnf(c_0_87, plain, (r2_hidden(X1,X3)|~r1_tarski(X1,X2)|X3!=k1_zfmisc_1(X2)), inference(split_conjunct,[status(thm)],[c_0_79])).
% 0.39/0.58  cnf(c_0_88, negated_conjecture, (esk12_0=k1_xboole_0|r1_tarski(X1,esk10_0)|~r1_tarski(X1,esk12_0)), inference(spm,[status(thm)],[c_0_80, c_0_81])).
% 0.39/0.58  cnf(c_0_89, negated_conjecture, (r1_tarski(esk11_0,esk12_0)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.39/0.58  fof(c_0_90, plain, ![X84, X86, X89, X90, X91]:(((r2_hidden(X86,k3_tarski(X84))|~r2_hidden(X86,esk7_1(X84)))&((X86=esk8_2(X84,X86)|~r2_hidden(X86,esk7_1(X84)))&((r2_hidden(esk9_2(X84,X86),esk8_2(X84,X86))|~r2_hidden(X86,esk7_1(X84)))&(r2_hidden(esk9_2(X84,X86),X84)|~r2_hidden(X86,esk7_1(X84))))))&(~r2_hidden(X89,k3_tarski(X84))|(X89!=X90|(~r2_hidden(X91,X90)|~r2_hidden(X91,X84)))|r2_hidden(X89,esk7_1(X84)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[s1_xboole_0__e1_138_1__zfmisc_1])])])])])])).
% 0.39/0.58  cnf(c_0_91, plain, (~r2_hidden(X1,k1_xboole_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_83]), c_0_84]), c_0_85]), c_0_84])).
% 0.39/0.58  cnf(c_0_92, plain, (r2_hidden(esk6_2(X1,X2),X1)|r2_hidden(esk5_2(X1,X2),X2)|X2=k3_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_86])).
% 0.39/0.58  cnf(c_0_93, plain, (k3_tarski(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t2_zfmisc_1])).
% 0.39/0.58  cnf(c_0_94, plain, (r2_hidden(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(er,[status(thm)],[c_0_87])).
% 0.39/0.58  cnf(c_0_95, negated_conjecture, (esk12_0=k1_xboole_0|r1_tarski(esk11_0,esk10_0)), inference(spm,[status(thm)],[c_0_88, c_0_89])).
% 0.39/0.58  cnf(c_0_96, plain, (r2_hidden(X1,k3_tarski(X2))|~r2_hidden(X1,esk7_1(X2))), inference(split_conjunct,[status(thm)],[c_0_90])).
% 0.39/0.58  cnf(c_0_97, plain, (X1=k1_xboole_0|r2_hidden(esk5_2(k1_xboole_0,X1),X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_92]), c_0_93])).
% 0.39/0.58  cnf(c_0_98, plain, (m1_subset_1(X1,X2)|v1_xboole_0(X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.39/0.58  cnf(c_0_99, negated_conjecture, (esk12_0=k1_xboole_0|r2_hidden(esk11_0,k1_zfmisc_1(esk10_0))), inference(spm,[status(thm)],[c_0_94, c_0_95])).
% 0.39/0.58  cnf(c_0_100, plain, (esk7_1(X1)=k1_xboole_0|r2_hidden(esk5_2(k1_xboole_0,esk7_1(X1)),k3_tarski(X1))), inference(spm,[status(thm)],[c_0_96, c_0_97])).
% 0.39/0.58  fof(c_0_101, plain, ![X105, X106, X107]:((~r1_tarski(X106,X107)|r1_tarski(k3_subset_1(X105,X107),k3_subset_1(X105,X106))|~m1_subset_1(X107,k1_zfmisc_1(X105))|~m1_subset_1(X106,k1_zfmisc_1(X105)))&(~r1_tarski(k3_subset_1(X105,X107),k3_subset_1(X105,X106))|r1_tarski(X106,X107)|~m1_subset_1(X107,k1_zfmisc_1(X105))|~m1_subset_1(X106,k1_zfmisc_1(X105)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_subset_1])])])])).
% 0.39/0.58  fof(c_0_102, plain, ![X101, X102]:(~m1_subset_1(X102,k1_zfmisc_1(X101))|m1_subset_1(k3_subset_1(X101,X102),k1_zfmisc_1(X101))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).
% 0.39/0.58  cnf(c_0_103, negated_conjecture, (esk12_0=k1_xboole_0|m1_subset_1(esk11_0,k1_zfmisc_1(esk10_0))|v1_xboole_0(k1_zfmisc_1(esk10_0))), inference(spm,[status(thm)],[c_0_98, c_0_99])).
% 0.39/0.58  cnf(c_0_104, plain, (r1_tarski(X1,X3)|~r2_hidden(X1,X2)|X2!=k1_zfmisc_1(X3)), inference(split_conjunct,[status(thm)],[c_0_79])).
% 0.39/0.58  cnf(c_0_105, plain, (esk7_1(X1)=k3_tarski(X2)|r2_hidden(esk5_2(X2,esk7_1(X1)),k3_tarski(X1))|r2_hidden(esk6_2(X2,esk7_1(X1)),X2)), inference(spm,[status(thm)],[c_0_96, c_0_92])).
% 0.39/0.58  cnf(c_0_106, plain, (esk7_1(k1_xboole_0)=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_93]), c_0_91])).
% 0.39/0.58  cnf(c_0_107, plain, (r1_tarski(X3,X2)|~r1_tarski(k3_subset_1(X1,X2),k3_subset_1(X1,X3))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~m1_subset_1(X3,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_101])).
% 0.39/0.58  cnf(c_0_108, plain, (m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_102])).
% 0.39/0.58  cnf(c_0_109, negated_conjecture, (esk12_0=k1_xboole_0|m1_subset_1(esk11_0,k1_zfmisc_1(esk10_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_103]), c_0_58])).
% 0.39/0.58  fof(c_0_110, plain, ![X103, X104]:(~m1_subset_1(X104,k1_zfmisc_1(X103))|k3_subset_1(X103,k3_subset_1(X103,X104))=X104), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).
% 0.39/0.58  cnf(c_0_111, plain, (r1_tarski(X1,X2)|~r2_hidden(X1,k1_zfmisc_1(X2))), inference(er,[status(thm)],[c_0_104])).
% 0.39/0.58  cnf(c_0_112, plain, (k3_tarski(X1)=k1_xboole_0|r2_hidden(esk6_2(X1,k1_xboole_0),X1)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105, c_0_106]), c_0_93]), c_0_91])).
% 0.39/0.58  cnf(c_0_113, negated_conjecture, (r1_tarski(esk12_0,X1)|~m1_subset_1(X1,k1_zfmisc_1(esk10_0))|~r1_tarski(k3_subset_1(esk10_0,X1),k3_subset_1(esk10_0,esk12_0))), inference(spm,[status(thm)],[c_0_107, c_0_37])).
% 0.39/0.58  cnf(c_0_114, negated_conjecture, (esk12_0=k1_xboole_0|m1_subset_1(k3_subset_1(esk10_0,esk11_0),k1_zfmisc_1(esk10_0))), inference(spm,[status(thm)],[c_0_108, c_0_109])).
% 0.39/0.58  cnf(c_0_115, plain, (k3_subset_1(X2,k3_subset_1(X2,X1))=X1|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_110])).
% 0.39/0.58  fof(c_0_116, plain, ![X108, X109]:((~r1_tarski(X109,k3_subset_1(X108,X109))|X109=k1_subset_1(X108)|~m1_subset_1(X109,k1_zfmisc_1(X108)))&(X109!=k1_subset_1(X108)|r1_tarski(X109,k3_subset_1(X108,X109))|~m1_subset_1(X109,k1_zfmisc_1(X108)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_subset_1])])])).
% 0.39/0.58  fof(c_0_117, plain, ![X100]:k1_subset_1(X100)=k1_xboole_0, inference(variable_rename,[status(thm)],[d3_subset_1])).
% 0.39/0.58  fof(c_0_118, plain, ![X8, X9, X10, X11, X12]:((~r1_tarski(X8,X9)|(~r2_hidden(X10,X8)|r2_hidden(X10,X9)))&((r2_hidden(esk1_2(X11,X12),X11)|r1_tarski(X11,X12))&(~r2_hidden(esk1_2(X11,X12),X12)|r1_tarski(X11,X12)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.39/0.58  cnf(c_0_119, negated_conjecture, (r1_tarski(X1,esk12_0)|~r1_tarski(X1,esk11_0)), inference(spm,[status(thm)],[c_0_80, c_0_89])).
% 0.39/0.58  cnf(c_0_120, plain, (X1=k1_xboole_0|r1_tarski(esk6_2(k1_zfmisc_1(X1),k1_xboole_0),X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111, c_0_112]), c_0_73])).
% 0.39/0.58  cnf(c_0_121, negated_conjecture, (esk11_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.39/0.58  cnf(c_0_122, negated_conjecture, (esk12_0=k1_xboole_0|r1_tarski(esk12_0,k3_subset_1(esk10_0,esk11_0))|~r1_tarski(k3_subset_1(esk10_0,k3_subset_1(esk10_0,esk11_0)),k3_subset_1(esk10_0,esk12_0))), inference(spm,[status(thm)],[c_0_113, c_0_114])).
% 0.39/0.58  cnf(c_0_123, negated_conjecture, (k3_subset_1(esk10_0,k3_subset_1(esk10_0,esk11_0))=esk11_0|esk12_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_115, c_0_109])).
% 0.39/0.58  cnf(c_0_124, negated_conjecture, (r1_tarski(esk11_0,k3_subset_1(esk10_0,esk12_0))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.39/0.58  cnf(c_0_125, plain, (X1=k1_subset_1(X2)|~r1_tarski(X1,k3_subset_1(X2,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_116])).
% 0.39/0.58  cnf(c_0_126, plain, (k1_subset_1(X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_117])).
% 0.39/0.58  cnf(c_0_127, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_118])).
% 0.39/0.58  cnf(c_0_128, negated_conjecture, (r1_tarski(esk6_2(k1_zfmisc_1(esk11_0),k1_xboole_0),esk12_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_119, c_0_120]), c_0_121])).
% 0.39/0.58  cnf(c_0_129, negated_conjecture, (esk12_0=k1_xboole_0|r1_tarski(esk12_0,k3_subset_1(esk10_0,esk11_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_122, c_0_123]), c_0_124])])).
% 0.39/0.58  cnf(c_0_130, plain, (X1=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,k3_subset_1(X2,X1))), inference(rw,[status(thm)],[c_0_125, c_0_126])).
% 0.39/0.58  cnf(c_0_131, negated_conjecture, (r2_hidden(X1,esk12_0)|~r2_hidden(X1,esk6_2(k1_zfmisc_1(esk11_0),k1_xboole_0))), inference(spm,[status(thm)],[c_0_127, c_0_128])).
% 0.39/0.58  cnf(c_0_132, plain, (r2_hidden(esk5_2(X1,X2),esk6_2(X1,X2))|r2_hidden(esk5_2(X1,X2),X2)|X2=k3_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_86])).
% 0.39/0.58  cnf(c_0_133, negated_conjecture, (esk12_0=k1_xboole_0|r1_tarski(X1,k3_subset_1(esk10_0,esk11_0))|~r1_tarski(X1,esk12_0)), inference(spm,[status(thm)],[c_0_80, c_0_129])).
% 0.39/0.58  cnf(c_0_134, negated_conjecture, (esk12_0=k1_xboole_0|~r1_tarski(esk11_0,k3_subset_1(esk10_0,esk11_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_130, c_0_109]), c_0_121])).
% 0.39/0.58  cnf(c_0_135, negated_conjecture, (r2_hidden(esk5_2(k1_zfmisc_1(esk11_0),k1_xboole_0),esk12_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_131, c_0_132]), c_0_73]), c_0_121]), c_0_91])).
% 0.39/0.58  cnf(c_0_136, negated_conjecture, (esk12_0=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_133, c_0_89]), c_0_134])).
% 0.39/0.58  cnf(c_0_137, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_135, c_0_136]), c_0_91]), ['proof']).
% 0.39/0.58  # SZS output end CNFRefutation
% 0.39/0.58  # Proof object total steps             : 138
% 0.39/0.58  # Proof object clause steps            : 76
% 0.39/0.58  # Proof object formula steps           : 62
% 0.39/0.58  # Proof object conjectures             : 30
% 0.39/0.58  # Proof object clause conjectures      : 27
% 0.39/0.58  # Proof object formula conjectures     : 3
% 0.39/0.58  # Proof object initial clauses used    : 38
% 0.39/0.58  # Proof object initial formulas used   : 31
% 0.39/0.58  # Proof object generating inferences   : 29
% 0.39/0.58  # Proof object simplifying inferences  : 50
% 0.39/0.58  # Training examples: 0 positive, 0 negative
% 0.39/0.58  # Parsed axioms                        : 36
% 0.39/0.58  # Removed by relevancy pruning/SinE    : 0
% 0.39/0.58  # Initial clauses                      : 61
% 0.39/0.58  # Removed in clause preprocessing      : 11
% 0.39/0.58  # Initial clauses in saturation        : 50
% 0.39/0.58  # Processed clauses                    : 1553
% 0.39/0.58  # ...of these trivial                  : 2
% 0.39/0.58  # ...subsumed                          : 580
% 0.39/0.58  # ...remaining for further processing  : 971
% 0.39/0.58  # Other redundant clauses eliminated   : 9
% 0.39/0.58  # Clauses deleted for lack of memory   : 0
% 0.39/0.58  # Backward-subsumed                    : 12
% 0.39/0.58  # Backward-rewritten                   : 680
% 0.39/0.58  # Generated clauses                    : 10865
% 0.39/0.58  # ...of the previous two non-trivial   : 10447
% 0.39/0.58  # Contextual simplify-reflections      : 18
% 0.39/0.58  # Paramodulations                      : 10854
% 0.39/0.58  # Factorizations                       : 2
% 0.39/0.58  # Equation resolutions                 : 9
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
% 0.39/0.58  # Current number of processed clauses  : 221
% 0.39/0.58  #    Positive orientable unit clauses  : 22
% 0.39/0.58  #    Positive unorientable unit clauses: 0
% 0.39/0.58  #    Negative unit clauses             : 3
% 0.39/0.58  #    Non-unit-clauses                  : 196
% 0.39/0.58  # Current number of unprocessed clauses: 8901
% 0.39/0.58  # ...number of literals in the above   : 32605
% 0.39/0.58  # Current number of archived formulas  : 0
% 0.39/0.58  # Current number of archived clauses   : 752
% 0.39/0.58  # Clause-clause subsumption calls (NU) : 35637
% 0.39/0.58  # Rec. Clause-clause subsumption calls : 18938
% 0.39/0.58  # Non-unit clause-clause subsumptions  : 597
% 0.39/0.58  # Unit Clause-clause subsumption calls : 518
% 0.39/0.58  # Rewrite failures with RHS unbound    : 0
% 0.39/0.58  # BW rewrite match attempts            : 29
% 0.39/0.58  # BW rewrite match successes           : 12
% 0.39/0.58  # Condensation attempts                : 0
% 0.39/0.58  # Condensation successes               : 0
% 0.39/0.58  # Termbank termtop insertions          : 201673
% 0.39/0.58  
% 0.39/0.58  # -------------------------------------------------
% 0.39/0.58  # User time                : 0.229 s
% 0.39/0.58  # System time              : 0.009 s
% 0.39/0.58  # Total time               : 0.238 s
% 0.39/0.58  # Maximum resident set size: 1612 pages
%------------------------------------------------------------------------------
