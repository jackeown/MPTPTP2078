%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0255+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:41 EST 2020

% Result     : Theorem 6.47s
% Output     : CNFRefutation 6.47s
% Verified   : 
% Statistics : Number of formulae       :  172 (5206 expanded)
%              Number of clauses        :   95 (1940 expanded)
%              Number of leaves         :   39 (1633 expanded)
%              Depth                    :   12
%              Number of atoms          :  393 (5664 expanded)
%              Number of equality atoms :  186 (5093 expanded)
%              Maximal formula depth    :   52 (   4 average)
%              Maximal clause size      :   76 (   2 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT002+2.ax',t7_boole)).

fof(t3_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X2) ) )
      & ~ ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(X3,X2) )
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',t3_xboole_0)).

fof(t69_xboole_1,axiom,(
    ! [X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ~ ( r1_tarski(X2,X1)
          & r1_xboole_0(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT002+2.ax',t69_xboole_1)).

fof(t65_xboole_1,axiom,(
    ! [X1] : r1_xboole_0(X1,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT002+2.ax',t65_xboole_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',d3_tarski)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT003+2.ax',t70_enumset1)).

fof(t6_xboole_0,axiom,(
    ! [X1,X2] :
      ~ ( r2_xboole_0(X1,X2)
        & ! [X3] :
            ~ ( r2_hidden(X3,X2)
              & ~ r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',t6_xboole_0)).

fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(l49_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => r1_tarski(X1,k3_tarski(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

fof(t95_xboole_1,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT002+2.ax',t95_xboole_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT003+2.ax',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT003+2.ax',t72_enumset1)).

fof(t50_zfmisc_1,conjecture,(
    ! [X1,X2,X3] : k2_xboole_0(k2_tarski(X1,X2),X3) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_zfmisc_1)).

fof(d8_xboole_0,axiom,(
    ! [X1,X2] :
      ( r2_xboole_0(X1,X2)
    <=> ( r1_tarski(X1,X2)
        & X1 != X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',d8_xboole_0)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',d1_xboole_0)).

fof(t2_zfmisc_1,axiom,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_zfmisc_1)).

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',idempotence_k3_xboole_0)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT003+2.ax',t73_enumset1)).

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT003+2.ax',t74_enumset1)).

fof(t75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT003+2.ax',t75_enumset1)).

fof(idempotence_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',idempotence_k2_xboole_0)).

fof(t68_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] : k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8)) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT003+2.ax',t68_enumset1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT003+2.ax',t69_enumset1)).

fof(t134_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8,X9] : k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k1_tarski(X9)) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT003+2.ax',t134_enumset1)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT003+2.ax',commutativity_k2_tarski)).

fof(t4_boole,axiom,(
    ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT002+2.ax',t4_boole)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT002+2.ax',t100_xboole_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT002+2.ax',d10_xboole_0)).

fof(t92_xboole_1,axiom,(
    ! [X1] : k5_xboole_0(X1,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT002+2.ax',t92_xboole_1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT002+2.ax',t7_xboole_1)).

fof(t91_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT002+2.ax',t91_xboole_1)).

fof(t1_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k5_xboole_0(X2,X3))
    <=> ~ ( r2_hidden(X1,X2)
        <=> r2_hidden(X1,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',t1_xboole_0)).

fof(l13_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',l13_xboole_0)).

fof(t20_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(X1)
    <=> X1 != X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(t5_boole,axiom,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT002+2.ax',t5_boole)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT002+2.ax',t2_xboole_1)).

fof(d7_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8,X9,X10] :
      ( X10 = k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)
    <=> ! [X11] :
          ( r2_hidden(X11,X10)
        <=> ~ ( X11 != X1
              & X11 != X2
              & X11 != X3
              & X11 != X4
              & X11 != X5
              & X11 != X6
              & X11 != X7
              & X11 != X8
              & X11 != X9 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT003+2.ax',d7_enumset1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',fc1_xboole_0)).

fof(c_0_39,plain,(
    ! [X381,X382] :
      ( ~ r2_hidden(X381,X382)
      | ~ v1_xboole_0(X382) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

fof(c_0_40,plain,(
    ! [X84,X85,X87,X88,X89] :
      ( ( r2_hidden(esk10_2(X84,X85),X84)
        | r1_xboole_0(X84,X85) )
      & ( r2_hidden(esk10_2(X84,X85),X85)
        | r1_xboole_0(X84,X85) )
      & ( ~ r2_hidden(X89,X87)
        | ~ r2_hidden(X89,X88)
        | ~ r1_xboole_0(X87,X88) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

fof(c_0_41,plain,(
    ! [X347,X348] :
      ( v1_xboole_0(X348)
      | ~ r1_tarski(X348,X347)
      | ~ r1_xboole_0(X348,X347) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t69_xboole_1])])])).

fof(c_0_42,plain,(
    ! [X339] : r1_xboole_0(X339,k1_xboole_0) ),
    inference(variable_rename,[status(thm)],[t65_xboole_1])).

fof(c_0_43,plain,(
    ! [X27,X28,X29,X30,X31] :
      ( ( ~ r1_tarski(X27,X28)
        | ~ r2_hidden(X29,X27)
        | r2_hidden(X29,X28) )
      & ( r2_hidden(esk2_2(X30,X31),X30)
        | r1_tarski(X30,X31) )
      & ( ~ r2_hidden(esk2_2(X30,X31),X31)
        | r1_tarski(X30,X31) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_44,plain,(
    ! [X1055,X1056] : k3_tarski(k2_tarski(X1055,X1056)) = k2_xboole_0(X1055,X1056) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_45,plain,(
    ! [X892,X893] : k1_enumset1(X892,X892,X893) = k2_tarski(X892,X893) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_46,plain,(
    ! [X99,X100] :
      ( ( r2_hidden(esk12_2(X99,X100),X100)
        | ~ r2_xboole_0(X99,X100) )
      & ( ~ r2_hidden(esk12_2(X99,X100),X99)
        | ~ r2_xboole_0(X99,X100) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t6_xboole_0])])])])])).

fof(c_0_47,plain,(
    ! [X981,X982,X983,X984,X985,X986] :
      ( ( ~ r2_hidden(X983,X982)
        | r1_tarski(X983,X981)
        | X982 != k1_zfmisc_1(X981) )
      & ( ~ r1_tarski(X984,X981)
        | r2_hidden(X984,X982)
        | X982 != k1_zfmisc_1(X981) )
      & ( ~ r2_hidden(esk21_2(X985,X986),X986)
        | ~ r1_tarski(esk21_2(X985,X986),X985)
        | X986 = k1_zfmisc_1(X985) )
      & ( r2_hidden(esk21_2(X985,X986),X986)
        | r1_tarski(esk21_2(X985,X986),X985)
        | X986 = k1_zfmisc_1(X985) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

cnf(c_0_48,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_49,plain,
    ( r2_hidden(esk10_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_50,plain,
    ( v1_xboole_0(X1)
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_51,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_52,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

fof(c_0_53,plain,(
    ! [X1053,X1054] :
      ( ~ r2_hidden(X1053,X1054)
      | r1_tarski(X1053,k3_tarski(X1054)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l49_zfmisc_1])])).

fof(c_0_54,plain,(
    ! [X426,X427] : k3_xboole_0(X426,X427) = k5_xboole_0(k5_xboole_0(X426,X427),k2_xboole_0(X426,X427)) ),
    inference(variable_rename,[status(thm)],[t95_xboole_1])).

cnf(c_0_55,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_56,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

fof(c_0_57,plain,(
    ! [X894,X895,X896] : k2_enumset1(X894,X894,X895,X896) = k1_enumset1(X894,X895,X896) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_58,plain,(
    ! [X897,X898,X899,X900] : k3_enumset1(X897,X897,X898,X899,X900) = k2_enumset1(X897,X898,X899,X900) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_59,negated_conjecture,(
    ~ ! [X1,X2,X3] : k2_xboole_0(k2_tarski(X1,X2),X3) != k1_xboole_0 ),
    inference(assume_negation,[status(cth)],[t50_zfmisc_1])).

cnf(c_0_60,plain,
    ( r2_hidden(esk12_2(X1,X2),X2)
    | ~ r2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

fof(c_0_61,plain,(
    ! [X64,X65] :
      ( ( r1_tarski(X64,X65)
        | ~ r2_xboole_0(X64,X65) )
      & ( X64 != X65
        | ~ r2_xboole_0(X64,X65) )
      & ( ~ r1_tarski(X64,X65)
        | X64 = X65
        | r2_xboole_0(X64,X65) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_xboole_0])])])).

cnf(c_0_62,plain,
    ( r1_tarski(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

fof(c_0_63,plain,(
    ! [X23,X24,X25] :
      ( ( ~ v1_xboole_0(X23)
        | ~ r2_hidden(X24,X23) )
      & ( r2_hidden(esk1_1(X25),X25)
        | v1_xboole_0(X25) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_64,plain,
    ( r1_xboole_0(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_65,plain,
    ( v1_xboole_0(X1)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_66,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_48,c_0_52])).

cnf(c_0_67,plain,
    ( r1_tarski(X1,k3_tarski(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_68,plain,
    ( k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t2_zfmisc_1])).

fof(c_0_69,plain,(
    ! [X67] : k3_xboole_0(X67,X67) = X67 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

cnf(c_0_70,plain,
    ( k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_71,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_72,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_73,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

fof(c_0_74,plain,(
    ! [X901,X902,X903,X904,X905] : k4_enumset1(X901,X901,X902,X903,X904,X905) = k3_enumset1(X901,X902,X903,X904,X905) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_75,plain,(
    ! [X906,X907,X908,X909,X910,X911] : k5_enumset1(X906,X906,X907,X908,X909,X910,X911) = k4_enumset1(X906,X907,X908,X909,X910,X911) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_76,plain,(
    ! [X912,X913,X914,X915,X916,X917,X918] : k6_enumset1(X912,X912,X913,X914,X915,X916,X917,X918) = k5_enumset1(X912,X913,X914,X915,X916,X917,X918) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_77,plain,(
    ! [X66] : k2_xboole_0(X66,X66) = X66 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).

fof(c_0_78,plain,(
    ! [X883,X884,X885,X886,X887,X888,X889,X890] : k6_enumset1(X883,X884,X885,X886,X887,X888,X889,X890) = k2_xboole_0(k5_enumset1(X883,X884,X885,X886,X887,X888,X889),k1_tarski(X890)) ),
    inference(variable_rename,[status(thm)],[t68_enumset1])).

fof(c_0_79,plain,(
    ! [X891] : k2_tarski(X891,X891) = k1_tarski(X891) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_80,plain,(
    ! [X698,X699,X700,X701,X702,X703,X704,X705,X706] : k7_enumset1(X698,X699,X700,X701,X702,X703,X704,X705,X706) = k2_xboole_0(k6_enumset1(X698,X699,X700,X701,X702,X703,X704,X705),k1_tarski(X706)) ),
    inference(variable_rename,[status(thm)],[t134_enumset1])).

fof(c_0_81,negated_conjecture,(
    k2_xboole_0(k2_tarski(esk32_0,esk33_0),esk34_0) = k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_59])])])).

fof(c_0_82,plain,(
    ! [X441,X442] : k2_tarski(X441,X442) = k2_tarski(X442,X441) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

fof(c_0_83,plain,(
    ! [X293] : k4_xboole_0(k1_xboole_0,X293) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t4_boole])).

fof(c_0_84,plain,(
    ! [X127,X128] : k4_xboole_0(X127,X128) = k5_xboole_0(X127,k3_xboole_0(X127,X128)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_85,plain,
    ( r2_hidden(X1,X3)
    | ~ r1_tarski(X1,X2)
    | X3 != k1_zfmisc_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_86,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_48,c_0_60])).

cnf(c_0_87,plain,
    ( X1 = X2
    | r2_xboole_0(X1,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_88,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(er,[status(thm)],[c_0_62])).

cnf(c_0_89,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_90,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_tarski(X2,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_91,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_66,c_0_65])).

cnf(c_0_92,plain,
    ( r1_tarski(X1,k1_xboole_0)
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

fof(c_0_93,plain,(
    ! [X104,X105] :
      ( ( r1_tarski(X104,X105)
        | X104 != X105 )
      & ( r1_tarski(X105,X104)
        | X104 != X105 )
      & ( ~ r1_tarski(X104,X105)
        | ~ r1_tarski(X105,X104)
        | X104 = X105 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_94,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_95,plain,
    ( k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_70,c_0_71]),c_0_72]),c_0_73])).

cnf(c_0_96,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

cnf(c_0_97,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_98,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_76])).

fof(c_0_99,plain,(
    ! [X421] : k5_xboole_0(X421,X421) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t92_xboole_1])).

cnf(c_0_100,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_77])).

fof(c_0_101,plain,(
    ! [X383,X384] : r1_tarski(X383,k2_xboole_0(X383,X384)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

cnf(c_0_102,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8)) ),
    inference(split_conjunct,[status(thm)],[c_0_78])).

cnf(c_0_103,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_79])).

cnf(c_0_104,plain,
    ( k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k1_tarski(X9)) ),
    inference(split_conjunct,[status(thm)],[c_0_80])).

cnf(c_0_105,negated_conjecture,
    ( k2_xboole_0(k2_tarski(esk32_0,esk33_0),esk34_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_81])).

cnf(c_0_106,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_82])).

cnf(c_0_107,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_83])).

cnf(c_0_108,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_84])).

fof(c_0_109,plain,(
    ! [X418,X419,X420] : k5_xboole_0(k5_xboole_0(X418,X419),X420) = k5_xboole_0(X418,k5_xboole_0(X419,X420)) ),
    inference(variable_rename,[status(thm)],[t91_xboole_1])).

cnf(c_0_110,plain,
    ( ~ r2_hidden(esk12_2(X1,X2),X1)
    | ~ r2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_111,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(er,[status(thm)],[c_0_85])).

cnf(c_0_112,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_86,c_0_87])).

cnf(c_0_113,plain,
    ( r1_tarski(esk1_1(k1_zfmisc_1(X1)),X1)
    | v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_88,c_0_89])).

cnf(c_0_114,plain,
    ( v1_xboole_0(X1)
    | ~ r1_tarski(X2,k1_xboole_0)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_50,c_0_90])).

cnf(c_0_115,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_91,c_0_92])).

cnf(c_0_116,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_93])).

fof(c_0_117,plain,(
    ! [X74,X75,X76] :
      ( ( ~ r2_hidden(X74,X75)
        | ~ r2_hidden(X74,X76)
        | ~ r2_hidden(X74,k5_xboole_0(X75,X76)) )
      & ( r2_hidden(X74,X75)
        | r2_hidden(X74,X76)
        | ~ r2_hidden(X74,k5_xboole_0(X75,X76)) )
      & ( ~ r2_hidden(X74,X75)
        | r2_hidden(X74,X76)
        | r2_hidden(X74,k5_xboole_0(X75,X76)) )
      & ( ~ r2_hidden(X74,X76)
        | r2_hidden(X74,X75)
        | r2_hidden(X74,k5_xboole_0(X75,X76)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_0])])])).

cnf(c_0_118,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X1),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_94,c_0_95]),c_0_96]),c_0_97]),c_0_98])).

cnf(c_0_119,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_99])).

cnf(c_0_120,plain,
    ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_100,c_0_71]),c_0_72]),c_0_73]),c_0_96]),c_0_97]),c_0_98])).

cnf(c_0_121,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_101])).

cnf(c_0_122,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k3_tarski(k6_enumset1(k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_102,c_0_103]),c_0_56]),c_0_71]),c_0_72]),c_0_72]),c_0_73]),c_0_73]),c_0_96]),c_0_96]),c_0_97]),c_0_97]),c_0_98]),c_0_98]),c_0_98]),c_0_98]),c_0_98]),c_0_98]),c_0_98]),c_0_98])).

cnf(c_0_123,plain,
    ( k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k3_tarski(k6_enumset1(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k6_enumset1(X9,X9,X9,X9,X9,X9,X9,X9))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_104,c_0_103]),c_0_56]),c_0_71]),c_0_72]),c_0_72]),c_0_73]),c_0_73]),c_0_96]),c_0_96]),c_0_97]),c_0_97]),c_0_98]),c_0_98])).

cnf(c_0_124,negated_conjecture,
    ( k3_tarski(k6_enumset1(k6_enumset1(esk32_0,esk32_0,esk32_0,esk32_0,esk32_0,esk32_0,esk32_0,esk33_0),k6_enumset1(esk32_0,esk32_0,esk32_0,esk32_0,esk32_0,esk32_0,esk32_0,esk33_0),k6_enumset1(esk32_0,esk32_0,esk32_0,esk32_0,esk32_0,esk32_0,esk32_0,esk33_0),k6_enumset1(esk32_0,esk32_0,esk32_0,esk32_0,esk32_0,esk32_0,esk32_0,esk33_0),k6_enumset1(esk32_0,esk32_0,esk32_0,esk32_0,esk32_0,esk32_0,esk32_0,esk33_0),k6_enumset1(esk32_0,esk32_0,esk32_0,esk32_0,esk32_0,esk32_0,esk32_0,esk33_0),k6_enumset1(esk32_0,esk32_0,esk32_0,esk32_0,esk32_0,esk32_0,esk32_0,esk33_0),esk34_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_105,c_0_56]),c_0_71]),c_0_72]),c_0_72]),c_0_72]),c_0_73]),c_0_73]),c_0_73]),c_0_73]),c_0_96]),c_0_96]),c_0_96]),c_0_96]),c_0_96]),c_0_97]),c_0_97]),c_0_97]),c_0_97]),c_0_97]),c_0_97]),c_0_98]),c_0_98]),c_0_98]),c_0_98]),c_0_98]),c_0_98]),c_0_98])).

cnf(c_0_125,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2) = k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_106,c_0_56]),c_0_56]),c_0_72]),c_0_72]),c_0_73]),c_0_73]),c_0_96]),c_0_96]),c_0_97]),c_0_97]),c_0_98]),c_0_98])).

cnf(c_0_126,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,X1),k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X1)))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_107,c_0_108]),c_0_95]),c_0_96]),c_0_97]),c_0_98])).

cnf(c_0_127,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_109])).

cnf(c_0_128,plain,
    ( ~ r1_tarski(esk12_2(k1_zfmisc_1(X1),X2),X1)
    | ~ r2_xboole_0(k1_zfmisc_1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_110,c_0_111])).

cnf(c_0_129,plain,
    ( esk1_1(k1_zfmisc_1(X1)) = X1
    | v1_xboole_0(k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_112,c_0_113])).

cnf(c_0_130,plain,
    ( v1_xboole_0(X1)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X2,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_114,c_0_115])).

cnf(c_0_131,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_116])).

cnf(c_0_132,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_117])).

cnf(c_0_133,plain,
    ( k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_118,c_0_119]),c_0_120])).

cnf(c_0_134,plain,
    ( r1_tarski(X1,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_121,c_0_71]),c_0_72]),c_0_73]),c_0_96]),c_0_97]),c_0_98])).

cnf(c_0_135,plain,
    ( k7_enumset1(X1,X1,X2,X3,X4,X5,X6,X7,X8) = k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(rw,[status(thm)],[c_0_122,c_0_123])).

cnf(c_0_136,negated_conjecture,
    ( k3_tarski(k6_enumset1(esk34_0,esk34_0,esk34_0,esk34_0,esk34_0,esk34_0,esk34_0,k6_enumset1(esk32_0,esk32_0,esk32_0,esk32_0,esk32_0,esk32_0,esk32_0,esk33_0))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_124,c_0_125])).

cnf(c_0_137,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(X1,k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X1))))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_126,c_0_127])).

cnf(c_0_138,plain,
    ( ~ r2_xboole_0(k1_zfmisc_1(k3_tarski(X1)),X2)
    | ~ r2_hidden(esk12_2(k1_zfmisc_1(k3_tarski(X1)),X2),X1) ),
    inference(spm,[status(thm)],[c_0_128,c_0_67])).

fof(c_0_139,plain,(
    ! [X69] :
      ( ~ v1_xboole_0(X69)
      | X69 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).

cnf(c_0_140,plain,
    ( v1_xboole_0(k1_zfmisc_1(X1))
    | r2_hidden(X1,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_89,c_0_129])).

cnf(c_0_141,plain,
    ( v1_xboole_0(X1)
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_130,c_0_131])).

cnf(c_0_142,plain,
    ( ~ r2_hidden(X1,k1_xboole_0)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_132,c_0_133])).

fof(c_0_143,plain,(
    ! [X1079,X1080] :
      ( ( k4_xboole_0(k1_tarski(X1079),k1_tarski(X1080)) != k1_tarski(X1079)
        | X1079 != X1080 )
      & ( X1079 = X1080
        | k4_xboole_0(k1_tarski(X1079),k1_tarski(X1080)) = k1_tarski(X1079) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_zfmisc_1])])).

cnf(c_0_144,plain,
    ( r1_tarski(X1,k3_tarski(k7_enumset1(X1,X1,X1,X1,X1,X1,X1,X1,X2))) ),
    inference(spm,[status(thm)],[c_0_134,c_0_135])).

cnf(c_0_145,negated_conjecture,
    ( k3_tarski(k7_enumset1(esk34_0,esk34_0,esk34_0,esk34_0,esk34_0,esk34_0,esk34_0,esk34_0,k7_enumset1(esk32_0,esk32_0,esk32_0,esk32_0,esk32_0,esk32_0,esk32_0,esk32_0,esk33_0))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_136,c_0_135]),c_0_135])).

cnf(c_0_146,plain,
    ( k5_xboole_0(X1,k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X1))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_137,c_0_133]),c_0_133])).

fof(c_0_147,plain,(
    ! [X324] : k5_xboole_0(X324,k1_xboole_0) = X324 ),
    inference(variable_rename,[status(thm)],[t5_boole])).

cnf(c_0_148,plain,
    ( ~ r2_xboole_0(k1_zfmisc_1(k3_tarski(X1)),X1) ),
    inference(spm,[status(thm)],[c_0_138,c_0_60])).

cnf(c_0_149,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_139])).

cnf(c_0_150,plain,
    ( v1_xboole_0(k1_zfmisc_1(X1))
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_140,c_0_141]),c_0_142])).

fof(c_0_151,plain,(
    ! [X239] : r1_tarski(k1_xboole_0,X239) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_152,plain,
    ( k4_xboole_0(k1_tarski(X1),k1_tarski(X2)) != k1_tarski(X1)
    | X1 != X2 ),
    inference(split_conjunct,[status(thm)],[c_0_143])).

fof(c_0_153,plain,(
    ! [X470,X471,X472,X473,X474,X475,X476,X477,X478,X479,X480,X481,X482,X483,X484,X485,X486,X487,X488,X489,X490,X491] :
      ( ( ~ r2_hidden(X480,X479)
        | X480 = X470
        | X480 = X471
        | X480 = X472
        | X480 = X473
        | X480 = X474
        | X480 = X475
        | X480 = X476
        | X480 = X477
        | X480 = X478
        | X479 != k7_enumset1(X470,X471,X472,X473,X474,X475,X476,X477,X478) )
      & ( X481 != X470
        | r2_hidden(X481,X479)
        | X479 != k7_enumset1(X470,X471,X472,X473,X474,X475,X476,X477,X478) )
      & ( X481 != X471
        | r2_hidden(X481,X479)
        | X479 != k7_enumset1(X470,X471,X472,X473,X474,X475,X476,X477,X478) )
      & ( X481 != X472
        | r2_hidden(X481,X479)
        | X479 != k7_enumset1(X470,X471,X472,X473,X474,X475,X476,X477,X478) )
      & ( X481 != X473
        | r2_hidden(X481,X479)
        | X479 != k7_enumset1(X470,X471,X472,X473,X474,X475,X476,X477,X478) )
      & ( X481 != X474
        | r2_hidden(X481,X479)
        | X479 != k7_enumset1(X470,X471,X472,X473,X474,X475,X476,X477,X478) )
      & ( X481 != X475
        | r2_hidden(X481,X479)
        | X479 != k7_enumset1(X470,X471,X472,X473,X474,X475,X476,X477,X478) )
      & ( X481 != X476
        | r2_hidden(X481,X479)
        | X479 != k7_enumset1(X470,X471,X472,X473,X474,X475,X476,X477,X478) )
      & ( X481 != X477
        | r2_hidden(X481,X479)
        | X479 != k7_enumset1(X470,X471,X472,X473,X474,X475,X476,X477,X478) )
      & ( X481 != X478
        | r2_hidden(X481,X479)
        | X479 != k7_enumset1(X470,X471,X472,X473,X474,X475,X476,X477,X478) )
      & ( esk19_10(X482,X483,X484,X485,X486,X487,X488,X489,X490,X491) != X482
        | ~ r2_hidden(esk19_10(X482,X483,X484,X485,X486,X487,X488,X489,X490,X491),X491)
        | X491 = k7_enumset1(X482,X483,X484,X485,X486,X487,X488,X489,X490) )
      & ( esk19_10(X482,X483,X484,X485,X486,X487,X488,X489,X490,X491) != X483
        | ~ r2_hidden(esk19_10(X482,X483,X484,X485,X486,X487,X488,X489,X490,X491),X491)
        | X491 = k7_enumset1(X482,X483,X484,X485,X486,X487,X488,X489,X490) )
      & ( esk19_10(X482,X483,X484,X485,X486,X487,X488,X489,X490,X491) != X484
        | ~ r2_hidden(esk19_10(X482,X483,X484,X485,X486,X487,X488,X489,X490,X491),X491)
        | X491 = k7_enumset1(X482,X483,X484,X485,X486,X487,X488,X489,X490) )
      & ( esk19_10(X482,X483,X484,X485,X486,X487,X488,X489,X490,X491) != X485
        | ~ r2_hidden(esk19_10(X482,X483,X484,X485,X486,X487,X488,X489,X490,X491),X491)
        | X491 = k7_enumset1(X482,X483,X484,X485,X486,X487,X488,X489,X490) )
      & ( esk19_10(X482,X483,X484,X485,X486,X487,X488,X489,X490,X491) != X486
        | ~ r2_hidden(esk19_10(X482,X483,X484,X485,X486,X487,X488,X489,X490,X491),X491)
        | X491 = k7_enumset1(X482,X483,X484,X485,X486,X487,X488,X489,X490) )
      & ( esk19_10(X482,X483,X484,X485,X486,X487,X488,X489,X490,X491) != X487
        | ~ r2_hidden(esk19_10(X482,X483,X484,X485,X486,X487,X488,X489,X490,X491),X491)
        | X491 = k7_enumset1(X482,X483,X484,X485,X486,X487,X488,X489,X490) )
      & ( esk19_10(X482,X483,X484,X485,X486,X487,X488,X489,X490,X491) != X488
        | ~ r2_hidden(esk19_10(X482,X483,X484,X485,X486,X487,X488,X489,X490,X491),X491)
        | X491 = k7_enumset1(X482,X483,X484,X485,X486,X487,X488,X489,X490) )
      & ( esk19_10(X482,X483,X484,X485,X486,X487,X488,X489,X490,X491) != X489
        | ~ r2_hidden(esk19_10(X482,X483,X484,X485,X486,X487,X488,X489,X490,X491),X491)
        | X491 = k7_enumset1(X482,X483,X484,X485,X486,X487,X488,X489,X490) )
      & ( esk19_10(X482,X483,X484,X485,X486,X487,X488,X489,X490,X491) != X490
        | ~ r2_hidden(esk19_10(X482,X483,X484,X485,X486,X487,X488,X489,X490,X491),X491)
        | X491 = k7_enumset1(X482,X483,X484,X485,X486,X487,X488,X489,X490) )
      & ( r2_hidden(esk19_10(X482,X483,X484,X485,X486,X487,X488,X489,X490,X491),X491)
        | esk19_10(X482,X483,X484,X485,X486,X487,X488,X489,X490,X491) = X482
        | esk19_10(X482,X483,X484,X485,X486,X487,X488,X489,X490,X491) = X483
        | esk19_10(X482,X483,X484,X485,X486,X487,X488,X489,X490,X491) = X484
        | esk19_10(X482,X483,X484,X485,X486,X487,X488,X489,X490,X491) = X485
        | esk19_10(X482,X483,X484,X485,X486,X487,X488,X489,X490,X491) = X486
        | esk19_10(X482,X483,X484,X485,X486,X487,X488,X489,X490,X491) = X487
        | esk19_10(X482,X483,X484,X485,X486,X487,X488,X489,X490,X491) = X488
        | esk19_10(X482,X483,X484,X485,X486,X487,X488,X489,X490,X491) = X489
        | esk19_10(X482,X483,X484,X485,X486,X487,X488,X489,X490,X491) = X490
        | X491 = k7_enumset1(X482,X483,X484,X485,X486,X487,X488,X489,X490) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_enumset1])])])])])])).

cnf(c_0_154,negated_conjecture,
    ( r1_tarski(esk34_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_144,c_0_145])).

cnf(c_0_155,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_156,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,X2)) = X2 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_127,c_0_119]),c_0_133])).

cnf(c_0_157,plain,
    ( k5_xboole_0(X1,k3_tarski(k7_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X1))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_146,c_0_135])).

cnf(c_0_158,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_147])).

cnf(c_0_159,plain,
    ( k1_zfmisc_1(k3_tarski(X1)) = X1
    | ~ r1_tarski(k1_zfmisc_1(k3_tarski(X1)),X1) ),
    inference(spm,[status(thm)],[c_0_148,c_0_87])).

cnf(c_0_160,plain,
    ( k1_zfmisc_1(X1) = k1_xboole_0
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_149,c_0_150])).

cnf(c_0_161,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_151])).

cnf(c_0_162,plain,
    ( X1 != X2
    | k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k5_xboole_0(k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)),k3_tarski(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))))) != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_152,c_0_103]),c_0_103]),c_0_103]),c_0_56]),c_0_56]),c_0_56]),c_0_108]),c_0_72]),c_0_72]),c_0_72]),c_0_72]),c_0_73]),c_0_73]),c_0_73]),c_0_73]),c_0_95]),c_0_96]),c_0_96]),c_0_96]),c_0_96]),c_0_96]),c_0_96]),c_0_96]),c_0_96]),c_0_96]),c_0_96]),c_0_97]),c_0_97]),c_0_97]),c_0_97]),c_0_97]),c_0_97]),c_0_97]),c_0_97]),c_0_97]),c_0_97]),c_0_97]),c_0_98]),c_0_98]),c_0_98]),c_0_98]),c_0_98]),c_0_98]),c_0_98]),c_0_98]),c_0_98]),c_0_98]),c_0_98]),c_0_98])).

cnf(c_0_163,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k7_enumset1(X2,X4,X5,X6,X7,X8,X9,X10,X11) ),
    inference(split_conjunct,[status(thm)],[c_0_153])).

cnf(c_0_164,negated_conjecture,
    ( esk34_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112,c_0_154]),c_0_155])])).

cnf(c_0_165,plain,
    ( k3_tarski(k7_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_156,c_0_157]),c_0_158])).

cnf(c_0_166,plain,
    ( k1_xboole_0 = X1
    | ~ r2_hidden(k3_tarski(X1),k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_159,c_0_160]),c_0_161])])).

cnf(c_0_167,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(rw,[status(thm)],[c_0_162,c_0_127])]),c_0_120]),c_0_119]),c_0_158]),c_0_119])).

cnf(c_0_168,plain,
    ( r2_hidden(X1,k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_163])])).

cnf(c_0_169,negated_conjecture,
    ( k7_enumset1(esk32_0,esk32_0,esk32_0,esk32_0,esk32_0,esk32_0,esk32_0,esk32_0,esk33_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_145,c_0_164]),c_0_164]),c_0_164]),c_0_164]),c_0_164]),c_0_164]),c_0_164]),c_0_164]),c_0_165])).

cnf(c_0_170,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_166,c_0_120]),c_0_167])).

cnf(c_0_171,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_168,c_0_169]),c_0_170]),
    [proof]).
%------------------------------------------------------------------------------
