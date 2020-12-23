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
% DateTime   : Thu Dec  3 10:46:14 EST 2020

% Result     : Theorem 1.22s
% Output     : CNFRefutation 1.22s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 449 expanded)
%              Number of clauses        :   67 ( 187 expanded)
%              Number of leaves         :   29 ( 122 expanded)
%              Depth                    :   18
%              Number of atoms          :  267 (1063 expanded)
%              Number of equality atoms :   97 ( 350 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    7 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t40_subset_1,conjecture,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => ( ( r1_tarski(X2,X3)
          & r1_tarski(X2,k3_subset_1(X1,X3)) )
       => X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_subset_1)).

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(l13_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(l49_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => r1_tarski(X1,k3_tarski(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).

fof(t99_zfmisc_1,axiom,(
    ! [X1] : k3_tarski(k1_zfmisc_1(X1)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t95_xboole_1,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(t64_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))
    <=> ( r2_hidden(X1,X2)
        & X1 != X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(t75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(t31_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => ( r1_tarski(X2,X3)
          <=> r1_tarski(k3_subset_1(X1,X3),k3_subset_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_subset_1)).

fof(dt_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(t91_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(idempotence_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(involutiveness_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,k3_subset_1(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(t92_xboole_1,axiom,(
    ! [X1] : k5_xboole_0(X1,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(t5_boole,axiom,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(t38_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ( r1_tarski(X2,k3_subset_1(X1,X2))
      <=> X2 = k1_subset_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_subset_1)).

fof(d3_subset_1,axiom,(
    ! [X1] : k1_subset_1(X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

fof(c_0_29,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(X1))
       => ( ( r1_tarski(X2,X3)
            & r1_tarski(X2,k3_subset_1(X1,X3)) )
         => X2 = k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t40_subset_1])).

fof(c_0_30,plain,(
    ! [X87,X88] :
      ( ( ~ m1_subset_1(X88,X87)
        | r2_hidden(X88,X87)
        | v1_xboole_0(X87) )
      & ( ~ r2_hidden(X88,X87)
        | m1_subset_1(X88,X87)
        | v1_xboole_0(X87) )
      & ( ~ m1_subset_1(X88,X87)
        | v1_xboole_0(X88)
        | ~ v1_xboole_0(X87) )
      & ( ~ v1_xboole_0(X88)
        | m1_subset_1(X88,X87)
        | ~ v1_xboole_0(X87) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

fof(c_0_31,negated_conjecture,
    ( m1_subset_1(esk9_0,k1_zfmisc_1(esk7_0))
    & r1_tarski(esk8_0,esk9_0)
    & r1_tarski(esk8_0,k3_subset_1(esk7_0,esk9_0))
    & esk8_0 != k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_29])])])).

cnf(c_0_32,plain,
    ( v1_xboole_0(X1)
    | ~ m1_subset_1(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_33,negated_conjecture,
    ( m1_subset_1(esk9_0,k1_zfmisc_1(esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_34,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_35,plain,(
    ! [X15] :
      ( ~ v1_xboole_0(X15)
      | X15 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).

cnf(c_0_36,negated_conjecture,
    ( v1_xboole_0(esk9_0)
    | ~ v1_xboole_0(k1_zfmisc_1(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_37,negated_conjecture,
    ( v1_xboole_0(k1_zfmisc_1(esk7_0))
    | r2_hidden(esk9_0,k1_zfmisc_1(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_33])).

fof(c_0_38,plain,(
    ! [X71,X72] :
      ( ~ r2_hidden(X71,X72)
      | r1_tarski(X71,k3_tarski(X72)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l49_zfmisc_1])])).

cnf(c_0_39,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_40,negated_conjecture,
    ( v1_xboole_0(esk9_0)
    | r2_hidden(esk9_0,k1_zfmisc_1(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

fof(c_0_41,plain,(
    ! [X86] : k3_tarski(k1_zfmisc_1(X86)) = X86 ),
    inference(variable_rename,[status(thm)],[t99_zfmisc_1])).

fof(c_0_42,plain,(
    ! [X20,X21,X22] :
      ( ~ r1_tarski(X20,X21)
      | ~ r1_tarski(X21,X22)
      | r1_tarski(X20,X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

cnf(c_0_43,plain,
    ( r1_tarski(X1,k3_tarski(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_44,negated_conjecture,
    ( esk9_0 = k1_xboole_0
    | r2_hidden(esk9_0,k1_zfmisc_1(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_45,plain,
    ( k3_tarski(k1_zfmisc_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

fof(c_0_46,plain,(
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

cnf(c_0_47,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_48,negated_conjecture,
    ( esk9_0 = k1_xboole_0
    | r1_tarski(esk9_0,esk7_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45])).

cnf(c_0_49,plain,
    ( r2_hidden(X1,X3)
    | ~ r1_tarski(X1,X2)
    | X3 != k1_zfmisc_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_50,negated_conjecture,
    ( esk9_0 = k1_xboole_0
    | r1_tarski(X1,esk7_0)
    | ~ r1_tarski(X1,esk9_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_51,negated_conjecture,
    ( r1_tarski(esk8_0,esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_52,plain,(
    ! [X73,X74] : k3_tarski(k2_tarski(X73,X74)) = k2_xboole_0(X73,X74) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_53,plain,(
    ! [X37,X38] : k1_enumset1(X37,X37,X38) = k2_tarski(X37,X38) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

cnf(c_0_54,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(er,[status(thm)],[c_0_49])).

cnf(c_0_55,negated_conjecture,
    ( esk9_0 = k1_xboole_0
    | r1_tarski(esk8_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

fof(c_0_56,plain,(
    ! [X34,X35] : k3_xboole_0(X34,X35) = k5_xboole_0(k5_xboole_0(X34,X35),k2_xboole_0(X34,X35)) ),
    inference(variable_rename,[status(thm)],[t95_xboole_1])).

cnf(c_0_57,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_58,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

fof(c_0_59,plain,(
    ! [X39,X40,X41] : k2_enumset1(X39,X39,X40,X41) = k1_enumset1(X39,X40,X41) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_60,plain,(
    ! [X42,X43,X44,X45] : k3_enumset1(X42,X42,X43,X44,X45) = k2_enumset1(X42,X43,X44,X45) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

cnf(c_0_61,plain,
    ( m1_subset_1(X1,X2)
    | v1_xboole_0(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_62,negated_conjecture,
    ( esk9_0 = k1_xboole_0
    | r2_hidden(esk8_0,k1_zfmisc_1(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

fof(c_0_63,plain,(
    ! [X83,X84,X85] :
      ( ( r2_hidden(X83,X84)
        | ~ r2_hidden(X83,k4_xboole_0(X84,k1_tarski(X85))) )
      & ( X83 != X85
        | ~ r2_hidden(X83,k4_xboole_0(X84,k1_tarski(X85))) )
      & ( ~ r2_hidden(X83,X84)
        | X83 = X85
        | r2_hidden(X83,k4_xboole_0(X84,k1_tarski(X85))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_zfmisc_1])])])).

fof(c_0_64,plain,(
    ! [X36] : k2_tarski(X36,X36) = k1_tarski(X36) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_65,plain,(
    ! [X18,X19] : k4_xboole_0(X18,X19) = k5_xboole_0(X18,k3_xboole_0(X18,X19)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_66,plain,
    ( k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_67,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_68,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_69,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

fof(c_0_70,plain,(
    ! [X46,X47,X48,X49,X50] : k4_enumset1(X46,X46,X47,X48,X49,X50) = k3_enumset1(X46,X47,X48,X49,X50) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_71,plain,(
    ! [X51,X52,X53,X54,X55,X56] : k5_enumset1(X51,X51,X52,X53,X54,X55,X56) = k4_enumset1(X51,X52,X53,X54,X55,X56) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_72,plain,(
    ! [X57,X58,X59,X60,X61,X62,X63] : k6_enumset1(X57,X57,X58,X59,X60,X61,X62,X63) = k5_enumset1(X57,X58,X59,X60,X61,X62,X63) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_73,plain,(
    ! [X94,X95,X96] :
      ( ( ~ r1_tarski(X95,X96)
        | r1_tarski(k3_subset_1(X94,X96),k3_subset_1(X94,X95))
        | ~ m1_subset_1(X96,k1_zfmisc_1(X94))
        | ~ m1_subset_1(X95,k1_zfmisc_1(X94)) )
      & ( ~ r1_tarski(k3_subset_1(X94,X96),k3_subset_1(X94,X95))
        | r1_tarski(X95,X96)
        | ~ m1_subset_1(X96,k1_zfmisc_1(X94))
        | ~ m1_subset_1(X95,k1_zfmisc_1(X94)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_subset_1])])])])).

fof(c_0_74,plain,(
    ! [X90,X91] :
      ( ~ m1_subset_1(X91,k1_zfmisc_1(X90))
      | m1_subset_1(k3_subset_1(X90,X91),k1_zfmisc_1(X90)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).

cnf(c_0_75,negated_conjecture,
    ( esk9_0 = k1_xboole_0
    | m1_subset_1(esk8_0,k1_zfmisc_1(esk7_0))
    | v1_xboole_0(k1_zfmisc_1(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_76,plain,
    ( X1 != X2
    | ~ r2_hidden(X1,k4_xboole_0(X3,k1_tarski(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_77,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_78,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_79,plain,
    ( k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66,c_0_67]),c_0_68]),c_0_69])).

cnf(c_0_80,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_81,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_82,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

fof(c_0_83,plain,(
    ! [X30,X31,X32] : k5_xboole_0(k5_xboole_0(X30,X31),X32) = k5_xboole_0(X30,k5_xboole_0(X31,X32)) ),
    inference(variable_rename,[status(thm)],[t91_xboole_1])).

fof(c_0_84,plain,(
    ! [X14] : k2_xboole_0(X14,X14) = X14 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).

fof(c_0_85,plain,(
    ! [X8,X9,X10,X11,X12] :
      ( ( ~ r1_tarski(X8,X9)
        | ~ r2_hidden(X10,X8)
        | r2_hidden(X10,X9) )
      & ( r2_hidden(esk1_2(X11,X12),X11)
        | r1_tarski(X11,X12) )
      & ( ~ r2_hidden(esk1_2(X11,X12),X12)
        | r1_tarski(X11,X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_86,plain,
    ( r1_tarski(X3,X2)
    | ~ r1_tarski(k3_subset_1(X1,X2),k3_subset_1(X1,X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_87,plain,
    ( m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

cnf(c_0_88,negated_conjecture,
    ( esk9_0 = k1_xboole_0
    | m1_subset_1(esk8_0,k1_zfmisc_1(esk7_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_75]),c_0_39])).

fof(c_0_89,plain,(
    ! [X92,X93] :
      ( ~ m1_subset_1(X93,k1_zfmisc_1(X92))
      | k3_subset_1(X92,k3_subset_1(X92,X93)) = X93 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).

cnf(c_0_90,plain,
    ( X1 != X2
    | ~ r2_hidden(X1,k5_xboole_0(X3,k5_xboole_0(k5_xboole_0(X3,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)),k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_76,c_0_77]),c_0_58]),c_0_78]),c_0_68]),c_0_69]),c_0_79]),c_0_80]),c_0_80]),c_0_80]),c_0_81]),c_0_81]),c_0_81]),c_0_82]),c_0_82]),c_0_82])).

cnf(c_0_91,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_83])).

cnf(c_0_92,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_84])).

fof(c_0_93,plain,(
    ! [X33] : k5_xboole_0(X33,X33) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t92_xboole_1])).

fof(c_0_94,plain,(
    ! [X24] : k5_xboole_0(X24,k1_xboole_0) = X24 ),
    inference(variable_rename,[status(thm)],[t5_boole])).

cnf(c_0_95,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_85])).

cnf(c_0_96,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_85])).

fof(c_0_97,plain,(
    ! [X16] :
      ( X16 = k1_xboole_0
      | r2_hidden(esk2_1(X16),X16) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

cnf(c_0_98,negated_conjecture,
    ( r1_tarski(esk9_0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk7_0))
    | ~ r1_tarski(k3_subset_1(esk7_0,X1),k3_subset_1(esk7_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_86,c_0_33])).

cnf(c_0_99,negated_conjecture,
    ( esk9_0 = k1_xboole_0
    | m1_subset_1(k3_subset_1(esk7_0,esk8_0),k1_zfmisc_1(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_87,c_0_88])).

cnf(c_0_100,plain,
    ( k3_subset_1(X2,k3_subset_1(X2,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_89])).

fof(c_0_101,plain,(
    ! [X97,X98] :
      ( ( ~ r1_tarski(X98,k3_subset_1(X97,X98))
        | X98 = k1_subset_1(X97)
        | ~ m1_subset_1(X98,k1_zfmisc_1(X97)) )
      & ( X98 != k1_subset_1(X97)
        | r1_tarski(X98,k3_subset_1(X97,X98))
        | ~ m1_subset_1(X98,k1_zfmisc_1(X97)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_subset_1])])])).

fof(c_0_102,plain,(
    ! [X89] : k1_subset_1(X89) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[d3_subset_1])).

cnf(c_0_103,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,k5_xboole_0(X2,k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))))))) ),
    inference(er,[status(thm)],[inference(rw,[status(thm)],[c_0_90,c_0_91])])).

cnf(c_0_104,plain,
    ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_92,c_0_67]),c_0_68]),c_0_69]),c_0_80]),c_0_81]),c_0_82])).

cnf(c_0_105,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_93])).

cnf(c_0_106,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_94])).

cnf(c_0_107,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r2_hidden(X3,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(spm,[status(thm)],[c_0_95,c_0_96])).

cnf(c_0_108,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk2_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_97])).

cnf(c_0_109,negated_conjecture,
    ( esk9_0 = k1_xboole_0
    | r1_tarski(esk9_0,k3_subset_1(esk7_0,esk8_0))
    | ~ r1_tarski(k3_subset_1(esk7_0,k3_subset_1(esk7_0,esk8_0)),k3_subset_1(esk7_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_98,c_0_99])).

cnf(c_0_110,negated_conjecture,
    ( k3_subset_1(esk7_0,k3_subset_1(esk7_0,esk8_0)) = esk8_0
    | esk9_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_100,c_0_88])).

cnf(c_0_111,negated_conjecture,
    ( r1_tarski(esk8_0,k3_subset_1(esk7_0,esk9_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_112,plain,
    ( X1 = k1_subset_1(X2)
    | ~ r1_tarski(X1,k3_subset_1(X2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_101])).

cnf(c_0_113,plain,
    ( k1_subset_1(X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_102])).

cnf(c_0_114,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_104]),c_0_105]),c_0_106]),c_0_105])).

cnf(c_0_115,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk1_2(X1,X2),X1)
    | r2_hidden(esk2_1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_107,c_0_108])).

cnf(c_0_116,negated_conjecture,
    ( esk9_0 = k1_xboole_0
    | r1_tarski(esk9_0,k3_subset_1(esk7_0,esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_110]),c_0_111])])).

cnf(c_0_117,plain,
    ( X1 = k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,k3_subset_1(X2,X1)) ),
    inference(rw,[status(thm)],[c_0_112,c_0_113])).

cnf(c_0_118,negated_conjecture,
    ( esk8_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_119,negated_conjecture,
    ( r2_hidden(X1,esk9_0)
    | ~ r2_hidden(X1,esk8_0) ),
    inference(spm,[status(thm)],[c_0_95,c_0_51])).

cnf(c_0_120,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk1_2(X1,k1_xboole_0),X1) ),
    inference(spm,[status(thm)],[c_0_114,c_0_115])).

cnf(c_0_121,negated_conjecture,
    ( esk9_0 = k1_xboole_0
    | r1_tarski(X1,k3_subset_1(esk7_0,esk8_0))
    | ~ r1_tarski(X1,esk9_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_116])).

cnf(c_0_122,negated_conjecture,
    ( esk9_0 = k1_xboole_0
    | ~ r1_tarski(esk8_0,k3_subset_1(esk7_0,esk8_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_117,c_0_88]),c_0_118])).

cnf(c_0_123,negated_conjecture,
    ( r2_hidden(esk1_2(esk8_0,k1_xboole_0),esk9_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_119,c_0_120]),c_0_118])).

cnf(c_0_124,negated_conjecture,
    ( esk9_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_121,c_0_51]),c_0_122])).

cnf(c_0_125,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_123,c_0_124]),c_0_114]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:40:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 1.22/1.45  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_S2mI
% 1.22/1.45  # and selection function SelectCQArNTNpEqFirst.
% 1.22/1.45  #
% 1.22/1.45  # Preprocessing time       : 0.029 s
% 1.22/1.45  # Presaturation interreduction done
% 1.22/1.45  
% 1.22/1.45  # Proof found!
% 1.22/1.45  # SZS status Theorem
% 1.22/1.45  # SZS output start CNFRefutation
% 1.22/1.45  fof(t40_subset_1, conjecture, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>((r1_tarski(X2,X3)&r1_tarski(X2,k3_subset_1(X1,X3)))=>X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_subset_1)).
% 1.22/1.45  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 1.22/1.45  fof(l13_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 1.22/1.45  fof(l49_zfmisc_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>r1_tarski(X1,k3_tarski(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 1.22/1.45  fof(t99_zfmisc_1, axiom, ![X1]:k3_tarski(k1_zfmisc_1(X1))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 1.22/1.45  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 1.22/1.45  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 1.22/1.45  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 1.22/1.45  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 1.22/1.45  fof(t95_xboole_1, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_xboole_1)).
% 1.22/1.45  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 1.22/1.45  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 1.22/1.45  fof(t64_zfmisc_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))<=>(r2_hidden(X1,X2)&X1!=X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 1.22/1.45  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 1.22/1.45  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 1.22/1.45  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 1.22/1.45  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 1.22/1.45  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 1.22/1.45  fof(t31_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(r1_tarski(X2,X3)<=>r1_tarski(k3_subset_1(X1,X3),k3_subset_1(X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_subset_1)).
% 1.22/1.45  fof(dt_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 1.22/1.45  fof(t91_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 1.22/1.45  fof(idempotence_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 1.22/1.45  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 1.22/1.45  fof(involutiveness_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,k3_subset_1(X1,X2))=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 1.22/1.45  fof(t92_xboole_1, axiom, ![X1]:k5_xboole_0(X1,X1)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 1.22/1.45  fof(t5_boole, axiom, ![X1]:k5_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 1.22/1.45  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 1.22/1.45  fof(t38_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>(r1_tarski(X2,k3_subset_1(X1,X2))<=>X2=k1_subset_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_subset_1)).
% 1.22/1.45  fof(d3_subset_1, axiom, ![X1]:k1_subset_1(X1)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 1.22/1.45  fof(c_0_29, negated_conjecture, ~(![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>((r1_tarski(X2,X3)&r1_tarski(X2,k3_subset_1(X1,X3)))=>X2=k1_xboole_0))), inference(assume_negation,[status(cth)],[t40_subset_1])).
% 1.22/1.45  fof(c_0_30, plain, ![X87, X88]:(((~m1_subset_1(X88,X87)|r2_hidden(X88,X87)|v1_xboole_0(X87))&(~r2_hidden(X88,X87)|m1_subset_1(X88,X87)|v1_xboole_0(X87)))&((~m1_subset_1(X88,X87)|v1_xboole_0(X88)|~v1_xboole_0(X87))&(~v1_xboole_0(X88)|m1_subset_1(X88,X87)|~v1_xboole_0(X87)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 1.22/1.45  fof(c_0_31, negated_conjecture, (m1_subset_1(esk9_0,k1_zfmisc_1(esk7_0))&((r1_tarski(esk8_0,esk9_0)&r1_tarski(esk8_0,k3_subset_1(esk7_0,esk9_0)))&esk8_0!=k1_xboole_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_29])])])).
% 1.22/1.45  cnf(c_0_32, plain, (v1_xboole_0(X1)|~m1_subset_1(X1,X2)|~v1_xboole_0(X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 1.22/1.45  cnf(c_0_33, negated_conjecture, (m1_subset_1(esk9_0,k1_zfmisc_1(esk7_0))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 1.22/1.45  cnf(c_0_34, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 1.22/1.45  fof(c_0_35, plain, ![X15]:(~v1_xboole_0(X15)|X15=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).
% 1.22/1.45  cnf(c_0_36, negated_conjecture, (v1_xboole_0(esk9_0)|~v1_xboole_0(k1_zfmisc_1(esk7_0))), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 1.22/1.45  cnf(c_0_37, negated_conjecture, (v1_xboole_0(k1_zfmisc_1(esk7_0))|r2_hidden(esk9_0,k1_zfmisc_1(esk7_0))), inference(spm,[status(thm)],[c_0_34, c_0_33])).
% 1.22/1.45  fof(c_0_38, plain, ![X71, X72]:(~r2_hidden(X71,X72)|r1_tarski(X71,k3_tarski(X72))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l49_zfmisc_1])])).
% 1.22/1.45  cnf(c_0_39, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 1.22/1.45  cnf(c_0_40, negated_conjecture, (v1_xboole_0(esk9_0)|r2_hidden(esk9_0,k1_zfmisc_1(esk7_0))), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 1.22/1.45  fof(c_0_41, plain, ![X86]:k3_tarski(k1_zfmisc_1(X86))=X86, inference(variable_rename,[status(thm)],[t99_zfmisc_1])).
% 1.22/1.45  fof(c_0_42, plain, ![X20, X21, X22]:(~r1_tarski(X20,X21)|~r1_tarski(X21,X22)|r1_tarski(X20,X22)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 1.22/1.45  cnf(c_0_43, plain, (r1_tarski(X1,k3_tarski(X2))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 1.22/1.45  cnf(c_0_44, negated_conjecture, (esk9_0=k1_xboole_0|r2_hidden(esk9_0,k1_zfmisc_1(esk7_0))), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 1.22/1.45  cnf(c_0_45, plain, (k3_tarski(k1_zfmisc_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_41])).
% 1.22/1.45  fof(c_0_46, plain, ![X64, X65, X66, X67, X68, X69]:(((~r2_hidden(X66,X65)|r1_tarski(X66,X64)|X65!=k1_zfmisc_1(X64))&(~r1_tarski(X67,X64)|r2_hidden(X67,X65)|X65!=k1_zfmisc_1(X64)))&((~r2_hidden(esk3_2(X68,X69),X69)|~r1_tarski(esk3_2(X68,X69),X68)|X69=k1_zfmisc_1(X68))&(r2_hidden(esk3_2(X68,X69),X69)|r1_tarski(esk3_2(X68,X69),X68)|X69=k1_zfmisc_1(X68)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 1.22/1.45  cnf(c_0_47, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 1.22/1.45  cnf(c_0_48, negated_conjecture, (esk9_0=k1_xboole_0|r1_tarski(esk9_0,esk7_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_45])).
% 1.22/1.45  cnf(c_0_49, plain, (r2_hidden(X1,X3)|~r1_tarski(X1,X2)|X3!=k1_zfmisc_1(X2)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 1.22/1.45  cnf(c_0_50, negated_conjecture, (esk9_0=k1_xboole_0|r1_tarski(X1,esk7_0)|~r1_tarski(X1,esk9_0)), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 1.22/1.45  cnf(c_0_51, negated_conjecture, (r1_tarski(esk8_0,esk9_0)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 1.22/1.45  fof(c_0_52, plain, ![X73, X74]:k3_tarski(k2_tarski(X73,X74))=k2_xboole_0(X73,X74), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 1.22/1.45  fof(c_0_53, plain, ![X37, X38]:k1_enumset1(X37,X37,X38)=k2_tarski(X37,X38), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 1.22/1.45  cnf(c_0_54, plain, (r2_hidden(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(er,[status(thm)],[c_0_49])).
% 1.22/1.45  cnf(c_0_55, negated_conjecture, (esk9_0=k1_xboole_0|r1_tarski(esk8_0,esk7_0)), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 1.22/1.45  fof(c_0_56, plain, ![X34, X35]:k3_xboole_0(X34,X35)=k5_xboole_0(k5_xboole_0(X34,X35),k2_xboole_0(X34,X35)), inference(variable_rename,[status(thm)],[t95_xboole_1])).
% 1.22/1.45  cnf(c_0_57, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 1.22/1.45  cnf(c_0_58, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 1.22/1.45  fof(c_0_59, plain, ![X39, X40, X41]:k2_enumset1(X39,X39,X40,X41)=k1_enumset1(X39,X40,X41), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 1.22/1.45  fof(c_0_60, plain, ![X42, X43, X44, X45]:k3_enumset1(X42,X42,X43,X44,X45)=k2_enumset1(X42,X43,X44,X45), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 1.22/1.45  cnf(c_0_61, plain, (m1_subset_1(X1,X2)|v1_xboole_0(X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 1.22/1.45  cnf(c_0_62, negated_conjecture, (esk9_0=k1_xboole_0|r2_hidden(esk8_0,k1_zfmisc_1(esk7_0))), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 1.22/1.45  fof(c_0_63, plain, ![X83, X84, X85]:(((r2_hidden(X83,X84)|~r2_hidden(X83,k4_xboole_0(X84,k1_tarski(X85))))&(X83!=X85|~r2_hidden(X83,k4_xboole_0(X84,k1_tarski(X85)))))&(~r2_hidden(X83,X84)|X83=X85|r2_hidden(X83,k4_xboole_0(X84,k1_tarski(X85))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_zfmisc_1])])])).
% 1.22/1.45  fof(c_0_64, plain, ![X36]:k2_tarski(X36,X36)=k1_tarski(X36), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 1.22/1.45  fof(c_0_65, plain, ![X18, X19]:k4_xboole_0(X18,X19)=k5_xboole_0(X18,k3_xboole_0(X18,X19)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 1.22/1.45  cnf(c_0_66, plain, (k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_56])).
% 1.22/1.45  cnf(c_0_67, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_57, c_0_58])).
% 1.22/1.45  cnf(c_0_68, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 1.22/1.45  cnf(c_0_69, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 1.22/1.45  fof(c_0_70, plain, ![X46, X47, X48, X49, X50]:k4_enumset1(X46,X46,X47,X48,X49,X50)=k3_enumset1(X46,X47,X48,X49,X50), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 1.22/1.45  fof(c_0_71, plain, ![X51, X52, X53, X54, X55, X56]:k5_enumset1(X51,X51,X52,X53,X54,X55,X56)=k4_enumset1(X51,X52,X53,X54,X55,X56), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 1.22/1.45  fof(c_0_72, plain, ![X57, X58, X59, X60, X61, X62, X63]:k6_enumset1(X57,X57,X58,X59,X60,X61,X62,X63)=k5_enumset1(X57,X58,X59,X60,X61,X62,X63), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 1.22/1.45  fof(c_0_73, plain, ![X94, X95, X96]:((~r1_tarski(X95,X96)|r1_tarski(k3_subset_1(X94,X96),k3_subset_1(X94,X95))|~m1_subset_1(X96,k1_zfmisc_1(X94))|~m1_subset_1(X95,k1_zfmisc_1(X94)))&(~r1_tarski(k3_subset_1(X94,X96),k3_subset_1(X94,X95))|r1_tarski(X95,X96)|~m1_subset_1(X96,k1_zfmisc_1(X94))|~m1_subset_1(X95,k1_zfmisc_1(X94)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_subset_1])])])])).
% 1.22/1.45  fof(c_0_74, plain, ![X90, X91]:(~m1_subset_1(X91,k1_zfmisc_1(X90))|m1_subset_1(k3_subset_1(X90,X91),k1_zfmisc_1(X90))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).
% 1.22/1.45  cnf(c_0_75, negated_conjecture, (esk9_0=k1_xboole_0|m1_subset_1(esk8_0,k1_zfmisc_1(esk7_0))|v1_xboole_0(k1_zfmisc_1(esk7_0))), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 1.22/1.45  cnf(c_0_76, plain, (X1!=X2|~r2_hidden(X1,k4_xboole_0(X3,k1_tarski(X2)))), inference(split_conjunct,[status(thm)],[c_0_63])).
% 1.22/1.45  cnf(c_0_77, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_64])).
% 1.22/1.45  cnf(c_0_78, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_65])).
% 1.22/1.45  cnf(c_0_79, plain, (k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66, c_0_67]), c_0_68]), c_0_69])).
% 1.22/1.45  cnf(c_0_80, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_70])).
% 1.22/1.45  cnf(c_0_81, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_71])).
% 1.22/1.45  cnf(c_0_82, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_72])).
% 1.22/1.45  fof(c_0_83, plain, ![X30, X31, X32]:k5_xboole_0(k5_xboole_0(X30,X31),X32)=k5_xboole_0(X30,k5_xboole_0(X31,X32)), inference(variable_rename,[status(thm)],[t91_xboole_1])).
% 1.22/1.45  fof(c_0_84, plain, ![X14]:k2_xboole_0(X14,X14)=X14, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).
% 1.22/1.45  fof(c_0_85, plain, ![X8, X9, X10, X11, X12]:((~r1_tarski(X8,X9)|(~r2_hidden(X10,X8)|r2_hidden(X10,X9)))&((r2_hidden(esk1_2(X11,X12),X11)|r1_tarski(X11,X12))&(~r2_hidden(esk1_2(X11,X12),X12)|r1_tarski(X11,X12)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 1.22/1.45  cnf(c_0_86, plain, (r1_tarski(X3,X2)|~r1_tarski(k3_subset_1(X1,X2),k3_subset_1(X1,X3))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~m1_subset_1(X3,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_73])).
% 1.22/1.45  cnf(c_0_87, plain, (m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_74])).
% 1.22/1.45  cnf(c_0_88, negated_conjecture, (esk9_0=k1_xboole_0|m1_subset_1(esk8_0,k1_zfmisc_1(esk7_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_75]), c_0_39])).
% 1.22/1.45  fof(c_0_89, plain, ![X92, X93]:(~m1_subset_1(X93,k1_zfmisc_1(X92))|k3_subset_1(X92,k3_subset_1(X92,X93))=X93), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).
% 1.22/1.45  cnf(c_0_90, plain, (X1!=X2|~r2_hidden(X1,k5_xboole_0(X3,k5_xboole_0(k5_xboole_0(X3,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)),k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_76, c_0_77]), c_0_58]), c_0_78]), c_0_68]), c_0_69]), c_0_79]), c_0_80]), c_0_80]), c_0_80]), c_0_81]), c_0_81]), c_0_81]), c_0_82]), c_0_82]), c_0_82])).
% 1.22/1.45  cnf(c_0_91, plain, (k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_83])).
% 1.22/1.45  cnf(c_0_92, plain, (k2_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_84])).
% 1.22/1.45  fof(c_0_93, plain, ![X33]:k5_xboole_0(X33,X33)=k1_xboole_0, inference(variable_rename,[status(thm)],[t92_xboole_1])).
% 1.22/1.45  fof(c_0_94, plain, ![X24]:k5_xboole_0(X24,k1_xboole_0)=X24, inference(variable_rename,[status(thm)],[t5_boole])).
% 1.22/1.45  cnf(c_0_95, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_85])).
% 1.22/1.45  cnf(c_0_96, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_85])).
% 1.22/1.45  fof(c_0_97, plain, ![X16]:(X16=k1_xboole_0|r2_hidden(esk2_1(X16),X16)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 1.22/1.45  cnf(c_0_98, negated_conjecture, (r1_tarski(esk9_0,X1)|~m1_subset_1(X1,k1_zfmisc_1(esk7_0))|~r1_tarski(k3_subset_1(esk7_0,X1),k3_subset_1(esk7_0,esk9_0))), inference(spm,[status(thm)],[c_0_86, c_0_33])).
% 1.22/1.45  cnf(c_0_99, negated_conjecture, (esk9_0=k1_xboole_0|m1_subset_1(k3_subset_1(esk7_0,esk8_0),k1_zfmisc_1(esk7_0))), inference(spm,[status(thm)],[c_0_87, c_0_88])).
% 1.22/1.45  cnf(c_0_100, plain, (k3_subset_1(X2,k3_subset_1(X2,X1))=X1|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_89])).
% 1.22/1.45  fof(c_0_101, plain, ![X97, X98]:((~r1_tarski(X98,k3_subset_1(X97,X98))|X98=k1_subset_1(X97)|~m1_subset_1(X98,k1_zfmisc_1(X97)))&(X98!=k1_subset_1(X97)|r1_tarski(X98,k3_subset_1(X97,X98))|~m1_subset_1(X98,k1_zfmisc_1(X97)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_subset_1])])])).
% 1.22/1.45  fof(c_0_102, plain, ![X89]:k1_subset_1(X89)=k1_xboole_0, inference(variable_rename,[status(thm)],[d3_subset_1])).
% 1.22/1.45  cnf(c_0_103, plain, (~r2_hidden(X1,k5_xboole_0(X2,k5_xboole_0(X2,k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))))))), inference(er,[status(thm)],[inference(rw,[status(thm)],[c_0_90, c_0_91])])).
% 1.22/1.45  cnf(c_0_104, plain, (k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_92, c_0_67]), c_0_68]), c_0_69]), c_0_80]), c_0_81]), c_0_82])).
% 1.22/1.45  cnf(c_0_105, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_93])).
% 1.22/1.45  cnf(c_0_106, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_94])).
% 1.22/1.45  cnf(c_0_107, plain, (r2_hidden(esk1_2(X1,X2),X1)|r2_hidden(X3,X2)|~r2_hidden(X3,X1)), inference(spm,[status(thm)],[c_0_95, c_0_96])).
% 1.22/1.45  cnf(c_0_108, plain, (X1=k1_xboole_0|r2_hidden(esk2_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_97])).
% 1.22/1.45  cnf(c_0_109, negated_conjecture, (esk9_0=k1_xboole_0|r1_tarski(esk9_0,k3_subset_1(esk7_0,esk8_0))|~r1_tarski(k3_subset_1(esk7_0,k3_subset_1(esk7_0,esk8_0)),k3_subset_1(esk7_0,esk9_0))), inference(spm,[status(thm)],[c_0_98, c_0_99])).
% 1.22/1.45  cnf(c_0_110, negated_conjecture, (k3_subset_1(esk7_0,k3_subset_1(esk7_0,esk8_0))=esk8_0|esk9_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_100, c_0_88])).
% 1.22/1.45  cnf(c_0_111, negated_conjecture, (r1_tarski(esk8_0,k3_subset_1(esk7_0,esk9_0))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 1.22/1.45  cnf(c_0_112, plain, (X1=k1_subset_1(X2)|~r1_tarski(X1,k3_subset_1(X2,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_101])).
% 1.22/1.45  cnf(c_0_113, plain, (k1_subset_1(X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_102])).
% 1.22/1.45  cnf(c_0_114, plain, (~r2_hidden(X1,k1_xboole_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103, c_0_104]), c_0_105]), c_0_106]), c_0_105])).
% 1.22/1.45  cnf(c_0_115, plain, (X1=k1_xboole_0|r2_hidden(esk1_2(X1,X2),X1)|r2_hidden(esk2_1(X1),X2)), inference(spm,[status(thm)],[c_0_107, c_0_108])).
% 1.22/1.45  cnf(c_0_116, negated_conjecture, (esk9_0=k1_xboole_0|r1_tarski(esk9_0,k3_subset_1(esk7_0,esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109, c_0_110]), c_0_111])])).
% 1.22/1.45  cnf(c_0_117, plain, (X1=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,k3_subset_1(X2,X1))), inference(rw,[status(thm)],[c_0_112, c_0_113])).
% 1.22/1.45  cnf(c_0_118, negated_conjecture, (esk8_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_31])).
% 1.22/1.45  cnf(c_0_119, negated_conjecture, (r2_hidden(X1,esk9_0)|~r2_hidden(X1,esk8_0)), inference(spm,[status(thm)],[c_0_95, c_0_51])).
% 1.22/1.45  cnf(c_0_120, plain, (X1=k1_xboole_0|r2_hidden(esk1_2(X1,k1_xboole_0),X1)), inference(spm,[status(thm)],[c_0_114, c_0_115])).
% 1.22/1.45  cnf(c_0_121, negated_conjecture, (esk9_0=k1_xboole_0|r1_tarski(X1,k3_subset_1(esk7_0,esk8_0))|~r1_tarski(X1,esk9_0)), inference(spm,[status(thm)],[c_0_47, c_0_116])).
% 1.22/1.45  cnf(c_0_122, negated_conjecture, (esk9_0=k1_xboole_0|~r1_tarski(esk8_0,k3_subset_1(esk7_0,esk8_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_117, c_0_88]), c_0_118])).
% 1.22/1.45  cnf(c_0_123, negated_conjecture, (r2_hidden(esk1_2(esk8_0,k1_xboole_0),esk9_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_119, c_0_120]), c_0_118])).
% 1.22/1.45  cnf(c_0_124, negated_conjecture, (esk9_0=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_121, c_0_51]), c_0_122])).
% 1.22/1.45  cnf(c_0_125, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_123, c_0_124]), c_0_114]), ['proof']).
% 1.22/1.45  # SZS output end CNFRefutation
% 1.22/1.45  # Proof object total steps             : 126
% 1.22/1.45  # Proof object clause steps            : 67
% 1.22/1.45  # Proof object formula steps           : 59
% 1.22/1.45  # Proof object conjectures             : 28
% 1.22/1.45  # Proof object clause conjectures      : 25
% 1.22/1.45  # Proof object formula conjectures     : 3
% 1.22/1.45  # Proof object initial clauses used    : 35
% 1.22/1.45  # Proof object initial formulas used   : 29
% 1.22/1.45  # Proof object generating inferences   : 24
% 1.22/1.45  # Proof object simplifying inferences  : 41
% 1.22/1.45  # Training examples: 0 positive, 0 negative
% 1.22/1.45  # Parsed axioms                        : 35
% 1.22/1.45  # Removed by relevancy pruning/SinE    : 0
% 1.22/1.45  # Initial clauses                      : 55
% 1.22/1.45  # Removed in clause preprocessing      : 11
% 1.22/1.45  # Initial clauses in saturation        : 44
% 1.22/1.45  # Processed clauses                    : 7174
% 1.22/1.45  # ...of these trivial                  : 10
% 1.22/1.45  # ...subsumed                          : 3760
% 1.22/1.45  # ...remaining for further processing  : 3404
% 1.22/1.45  # Other redundant clauses eliminated   : 6
% 1.22/1.45  # Clauses deleted for lack of memory   : 0
% 1.22/1.45  # Backward-subsumed                    : 248
% 1.22/1.45  # Backward-rewritten                   : 2880
% 1.22/1.45  # Generated clauses                    : 67974
% 1.22/1.45  # ...of the previous two non-trivial   : 64926
% 1.22/1.45  # Contextual simplify-reflections      : 78
% 1.22/1.45  # Paramodulations                      : 67960
% 1.22/1.45  # Factorizations                       : 8
% 1.22/1.45  # Equation resolutions                 : 6
% 1.22/1.45  # Propositional unsat checks           : 0
% 1.22/1.45  #    Propositional check models        : 0
% 1.22/1.45  #    Propositional check unsatisfiable : 0
% 1.22/1.45  #    Propositional clauses             : 0
% 1.22/1.45  #    Propositional clauses after purity: 0
% 1.22/1.45  #    Propositional unsat core size     : 0
% 1.22/1.45  #    Propositional preprocessing time  : 0.000
% 1.22/1.45  #    Propositional encoding time       : 0.000
% 1.22/1.45  #    Propositional solver time         : 0.000
% 1.22/1.45  #    Success case prop preproc time    : 0.000
% 1.22/1.45  #    Success case prop encoding time   : 0.000
% 1.22/1.45  #    Success case prop solver time     : 0.000
% 1.22/1.45  # Current number of processed clauses  : 227
% 1.22/1.45  #    Positive orientable unit clauses  : 29
% 1.22/1.45  #    Positive unorientable unit clauses: 0
% 1.22/1.45  #    Negative unit clauses             : 3
% 1.22/1.45  #    Non-unit-clauses                  : 195
% 1.22/1.45  # Current number of unprocessed clauses: 57081
% 1.22/1.45  # ...number of literals in the above   : 223697
% 1.22/1.45  # Current number of archived formulas  : 0
% 1.22/1.45  # Current number of archived clauses   : 3182
% 1.22/1.45  # Clause-clause subsumption calls (NU) : 1551165
% 1.22/1.45  # Rec. Clause-clause subsumption calls : 573662
% 1.22/1.45  # Non-unit clause-clause subsumptions  : 4051
% 1.22/1.45  # Unit Clause-clause subsumption calls : 7446
% 1.22/1.45  # Rewrite failures with RHS unbound    : 0
% 1.22/1.45  # BW rewrite match attempts            : 387
% 1.22/1.45  # BW rewrite match successes           : 22
% 1.22/1.45  # Condensation attempts                : 0
% 1.22/1.45  # Condensation successes               : 0
% 1.22/1.45  # Termbank termtop insertions          : 1208234
% 1.22/1.46  
% 1.22/1.46  # -------------------------------------------------
% 1.22/1.46  # User time                : 1.068 s
% 1.22/1.46  # System time              : 0.038 s
% 1.22/1.46  # Total time               : 1.106 s
% 1.22/1.46  # Maximum resident set size: 1608 pages
%------------------------------------------------------------------------------
