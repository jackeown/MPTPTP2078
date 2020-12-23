%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0300+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:42 EST 2020

% Result     : Theorem 1.97s
% Output     : CNFRefutation 1.97s
% Verified   : 
% Statistics : Number of formulae       :  188 (22270 expanded)
%              Number of clauses        :  122 (8606 expanded)
%              Number of leaves         :   33 (6817 expanded)
%              Depth                    :   22
%              Number of atoms          :  419 (29622 expanded)
%              Number of equality atoms :  142 (21462 expanded)
%              Maximal formula depth    :   23 (   4 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    7 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t108_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ! [X5,X6] :
          ( r2_hidden(k4_tarski(X5,X6),k2_zfmisc_1(X1,X2))
        <=> r2_hidden(k4_tarski(X5,X6),k2_zfmisc_1(X3,X4)) )
     => k2_zfmisc_1(X1,X2) = k2_zfmisc_1(X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_zfmisc_1)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT003+2.ax',t70_enumset1)).

fof(l54_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X4) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(t95_xboole_1,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT002+2.ax',t95_xboole_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT003+2.ax',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT003+2.ax',t72_enumset1)).

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',idempotence_k3_xboole_0)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT003+2.ax',t73_enumset1)).

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT003+2.ax',t74_enumset1)).

fof(t75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT003+2.ax',t75_enumset1)).

fof(idempotence_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',idempotence_k2_xboole_0)).

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
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',t3_xboole_0)).

fof(t64_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))
    <=> ( r2_hidden(X1,X2)
        & X1 != X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT003+2.ax',t69_enumset1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT002+2.ax',t100_xboole_1)).

fof(t92_xboole_1,axiom,(
    ! [X1] : k5_xboole_0(X1,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT002+2.ax',t92_xboole_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',d3_tarski)).

fof(t91_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT002+2.ax',t91_xboole_1)).

fof(t61_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_tarski(X7)) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT003+2.ax',t61_enumset1)).

fof(t67_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] : k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8)) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT003+2.ax',t67_enumset1)).

fof(t55_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( r1_xboole_0(k2_tarski(X1,X2),X3)
        & r2_hidden(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_zfmisc_1)).

fof(d2_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_zfmisc_1(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ? [X5,X6] :
              ( r2_hidden(X5,X1)
              & r2_hidden(X6,X2)
              & X4 = k4_tarski(X5,X6) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(d4_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k3_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] :
              ( r2_hidden(X3,X4)
              & r2_hidden(X4,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).

fof(t2_zfmisc_1,axiom,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_zfmisc_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',d1_xboole_0)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',t7_xboole_0)).

fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT002+2.ax',t7_boole)).

fof(t69_xboole_1,axiom,(
    ! [X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ~ ( r1_tarski(X2,X1)
          & r1_xboole_0(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT002+2.ax',t69_xboole_1)).

fof(t65_xboole_1,axiom,(
    ! [X1] : r1_xboole_0(X1,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT002+2.ax',t65_xboole_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT002+2.ax',d10_xboole_0)).

fof(l13_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',l13_xboole_0)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT002+2.ax',t2_xboole_1)).

fof(c_0_33,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ! [X5,X6] :
            ( r2_hidden(k4_tarski(X5,X6),k2_zfmisc_1(X1,X2))
          <=> r2_hidden(k4_tarski(X5,X6),k2_zfmisc_1(X3,X4)) )
       => k2_zfmisc_1(X1,X2) = k2_zfmisc_1(X3,X4) ) ),
    inference(assume_negation,[status(cth)],[t108_zfmisc_1])).

fof(c_0_34,plain,(
    ! [X1055,X1056] : k3_tarski(k2_tarski(X1055,X1056)) = k2_xboole_0(X1055,X1056) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_35,plain,(
    ! [X892,X893] : k1_enumset1(X892,X892,X893) = k2_tarski(X892,X893) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_36,negated_conjecture,(
    ! [X1093,X1094] :
      ( ( ~ r2_hidden(k4_tarski(X1093,X1094),k2_zfmisc_1(esk37_0,esk38_0))
        | r2_hidden(k4_tarski(X1093,X1094),k2_zfmisc_1(esk39_0,esk40_0)) )
      & ( ~ r2_hidden(k4_tarski(X1093,X1094),k2_zfmisc_1(esk39_0,esk40_0))
        | r2_hidden(k4_tarski(X1093,X1094),k2_zfmisc_1(esk37_0,esk38_0)) )
      & k2_zfmisc_1(esk37_0,esk38_0) != k2_zfmisc_1(esk39_0,esk40_0) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_33])])])])).

fof(c_0_37,plain,(
    ! [X1057,X1058,X1059,X1060] :
      ( ( r2_hidden(X1057,X1059)
        | ~ r2_hidden(k4_tarski(X1057,X1058),k2_zfmisc_1(X1059,X1060)) )
      & ( r2_hidden(X1058,X1060)
        | ~ r2_hidden(k4_tarski(X1057,X1058),k2_zfmisc_1(X1059,X1060)) )
      & ( ~ r2_hidden(X1057,X1059)
        | ~ r2_hidden(X1058,X1060)
        | r2_hidden(k4_tarski(X1057,X1058),k2_zfmisc_1(X1059,X1060)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).

fof(c_0_38,plain,(
    ! [X426,X427] : k3_xboole_0(X426,X427) = k5_xboole_0(k5_xboole_0(X426,X427),k2_xboole_0(X426,X427)) ),
    inference(variable_rename,[status(thm)],[t95_xboole_1])).

cnf(c_0_39,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_40,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

fof(c_0_41,plain,(
    ! [X894,X895,X896] : k2_enumset1(X894,X894,X895,X896) = k1_enumset1(X894,X895,X896) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_42,plain,(
    ! [X897,X898,X899,X900] : k3_enumset1(X897,X897,X898,X899,X900) = k2_enumset1(X897,X898,X899,X900) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(esk37_0,esk38_0))
    | ~ r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(esk39_0,esk40_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_44,plain,
    ( r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

fof(c_0_45,plain,(
    ! [X67] : k3_xboole_0(X67,X67) = X67 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

cnf(c_0_46,plain,
    ( k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_47,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_48,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_49,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

fof(c_0_50,plain,(
    ! [X901,X902,X903,X904,X905] : k4_enumset1(X901,X901,X902,X903,X904,X905) = k3_enumset1(X901,X902,X903,X904,X905) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_51,plain,(
    ! [X906,X907,X908,X909,X910,X911] : k5_enumset1(X906,X906,X907,X908,X909,X910,X911) = k4_enumset1(X906,X907,X908,X909,X910,X911) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_52,plain,(
    ! [X912,X913,X914,X915,X916,X917,X918] : k6_enumset1(X912,X912,X913,X914,X915,X916,X917,X918) = k5_enumset1(X912,X913,X914,X915,X916,X917,X918) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_53,plain,(
    ! [X66] : k2_xboole_0(X66,X66) = X66 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).

cnf(c_0_54,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_55,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(esk37_0,esk38_0))
    | ~ r2_hidden(X2,esk40_0)
    | ~ r2_hidden(X1,esk39_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

fof(c_0_56,plain,(
    ! [X84,X85,X87,X88,X89] :
      ( ( r2_hidden(esk10_2(X84,X85),X84)
        | r1_xboole_0(X84,X85) )
      & ( r2_hidden(esk10_2(X84,X85),X85)
        | r1_xboole_0(X84,X85) )
      & ( ~ r2_hidden(X89,X87)
        | ~ r2_hidden(X89,X88)
        | ~ r1_xboole_0(X87,X88) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

fof(c_0_57,plain,(
    ! [X1220,X1221,X1222] :
      ( ( r2_hidden(X1220,X1221)
        | ~ r2_hidden(X1220,k4_xboole_0(X1221,k1_tarski(X1222))) )
      & ( X1220 != X1222
        | ~ r2_hidden(X1220,k4_xboole_0(X1221,k1_tarski(X1222))) )
      & ( ~ r2_hidden(X1220,X1221)
        | X1220 = X1222
        | r2_hidden(X1220,k4_xboole_0(X1221,k1_tarski(X1222))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_zfmisc_1])])])).

fof(c_0_58,plain,(
    ! [X891] : k2_tarski(X891,X891) = k1_tarski(X891) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_59,plain,(
    ! [X127,X128] : k4_xboole_0(X127,X128) = k5_xboole_0(X127,k3_xboole_0(X127,X128)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_60,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_61,plain,
    ( k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_47]),c_0_48]),c_0_49])).

cnf(c_0_62,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_63,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_64,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

fof(c_0_65,plain,(
    ! [X421] : k5_xboole_0(X421,X421) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t92_xboole_1])).

cnf(c_0_66,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_67,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_68,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(esk39_0,esk40_0))
    | ~ r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(esk37_0,esk38_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

fof(c_0_69,plain,(
    ! [X27,X28,X29,X30,X31] :
      ( ( ~ r1_tarski(X27,X28)
        | ~ r2_hidden(X29,X27)
        | r2_hidden(X29,X28) )
      & ( r2_hidden(esk2_2(X30,X31),X30)
        | r1_tarski(X30,X31) )
      & ( ~ r2_hidden(esk2_2(X30,X31),X31)
        | r1_tarski(X30,X31) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_70,negated_conjecture,
    ( r2_hidden(X1,esk37_0)
    | ~ r2_hidden(X2,esk40_0)
    | ~ r2_hidden(X1,esk39_0) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_71,plain,
    ( r2_hidden(esk10_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_72,plain,
    ( X1 != X2
    | ~ r2_hidden(X1,k4_xboole_0(X3,k1_tarski(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_73,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_74,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

fof(c_0_75,plain,(
    ! [X418,X419,X420] : k5_xboole_0(k5_xboole_0(X418,X419),X420) = k5_xboole_0(X418,k5_xboole_0(X419,X420)) ),
    inference(variable_rename,[status(thm)],[t91_xboole_1])).

cnf(c_0_76,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X1),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_60,c_0_61]),c_0_62]),c_0_63]),c_0_64])).

cnf(c_0_77,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_78,plain,
    ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66,c_0_47]),c_0_48]),c_0_49]),c_0_62]),c_0_63]),c_0_64])).

fof(c_0_79,plain,(
    ! [X828,X829,X830,X831,X832,X833,X834] : k5_enumset1(X828,X829,X830,X831,X832,X833,X834) = k2_xboole_0(k4_enumset1(X828,X829,X830,X831,X832,X833),k1_tarski(X834)) ),
    inference(variable_rename,[status(thm)],[t61_enumset1])).

fof(c_0_80,plain,(
    ! [X875,X876,X877,X878,X879,X880,X881,X882] : k6_enumset1(X875,X876,X877,X878,X879,X880,X881,X882) = k2_xboole_0(k4_enumset1(X875,X876,X877,X878,X879,X880),k2_tarski(X881,X882)) ),
    inference(variable_rename,[status(thm)],[t67_enumset1])).

cnf(c_0_81,negated_conjecture,
    ( r2_hidden(X1,esk40_0)
    | ~ r2_hidden(k4_tarski(X2,X1),k2_zfmisc_1(esk37_0,esk38_0)) ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_82,negated_conjecture,
    ( r2_hidden(X1,esk38_0)
    | ~ r2_hidden(X1,esk40_0)
    | ~ r2_hidden(X2,esk39_0) ),
    inference(spm,[status(thm)],[c_0_67,c_0_55])).

cnf(c_0_83,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_84,negated_conjecture,
    ( r2_hidden(X1,esk39_0)
    | ~ r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(esk37_0,esk38_0)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_68])).

fof(c_0_85,plain,(
    ! [X1201,X1202,X1203] :
      ( ~ r1_xboole_0(k2_tarski(X1201,X1202),X1203)
      | ~ r2_hidden(X1201,X1203) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_zfmisc_1])])).

cnf(c_0_86,negated_conjecture,
    ( r1_xboole_0(X1,esk40_0)
    | r2_hidden(X2,esk37_0)
    | ~ r2_hidden(X2,esk39_0) ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_87,plain,
    ( X1 != X2
    | ~ r2_hidden(X1,k5_xboole_0(X3,k5_xboole_0(k5_xboole_0(X3,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)),k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_72,c_0_73]),c_0_40]),c_0_74]),c_0_48]),c_0_49]),c_0_61]),c_0_62]),c_0_62]),c_0_62]),c_0_63]),c_0_63]),c_0_63]),c_0_64]),c_0_64]),c_0_64])).

cnf(c_0_88,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_89,plain,
    ( k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_76,c_0_77]),c_0_78])).

cnf(c_0_90,plain,
    ( k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_tarski(X7)) ),
    inference(split_conjunct,[status(thm)],[c_0_79])).

cnf(c_0_91,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8)) ),
    inference(split_conjunct,[status(thm)],[c_0_80])).

cnf(c_0_92,negated_conjecture,
    ( r2_hidden(X1,esk40_0)
    | ~ r2_hidden(X1,esk38_0)
    | ~ r2_hidden(X2,esk37_0) ),
    inference(spm,[status(thm)],[c_0_81,c_0_44])).

cnf(c_0_93,negated_conjecture,
    ( r1_tarski(esk40_0,X1)
    | r2_hidden(esk2_2(esk40_0,X1),esk38_0)
    | ~ r2_hidden(X2,esk39_0) ),
    inference(spm,[status(thm)],[c_0_82,c_0_83])).

cnf(c_0_94,negated_conjecture,
    ( r2_hidden(X1,esk39_0)
    | ~ r2_hidden(X2,esk38_0)
    | ~ r2_hidden(X1,esk37_0) ),
    inference(spm,[status(thm)],[c_0_84,c_0_44])).

cnf(c_0_95,plain,
    ( ~ r1_xboole_0(k2_tarski(X1,X2),X3)
    | ~ r2_hidden(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_85])).

cnf(c_0_96,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk2_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_97,negated_conjecture,
    ( r1_xboole_0(X1,esk40_0)
    | r1_tarski(esk39_0,X2)
    | r2_hidden(esk2_2(esk39_0,X2),esk37_0) ),
    inference(spm,[status(thm)],[c_0_86,c_0_83])).

fof(c_0_98,plain,(
    ! [X988,X989,X990,X991,X994,X995,X996,X997,X998,X999,X1001,X1002] :
      ( ( r2_hidden(esk22_4(X988,X989,X990,X991),X988)
        | ~ r2_hidden(X991,X990)
        | X990 != k2_zfmisc_1(X988,X989) )
      & ( r2_hidden(esk23_4(X988,X989,X990,X991),X989)
        | ~ r2_hidden(X991,X990)
        | X990 != k2_zfmisc_1(X988,X989) )
      & ( X991 = k4_tarski(esk22_4(X988,X989,X990,X991),esk23_4(X988,X989,X990,X991))
        | ~ r2_hidden(X991,X990)
        | X990 != k2_zfmisc_1(X988,X989) )
      & ( ~ r2_hidden(X995,X988)
        | ~ r2_hidden(X996,X989)
        | X994 != k4_tarski(X995,X996)
        | r2_hidden(X994,X990)
        | X990 != k2_zfmisc_1(X988,X989) )
      & ( ~ r2_hidden(esk24_3(X997,X998,X999),X999)
        | ~ r2_hidden(X1001,X997)
        | ~ r2_hidden(X1002,X998)
        | esk24_3(X997,X998,X999) != k4_tarski(X1001,X1002)
        | X999 = k2_zfmisc_1(X997,X998) )
      & ( r2_hidden(esk25_3(X997,X998,X999),X997)
        | r2_hidden(esk24_3(X997,X998,X999),X999)
        | X999 = k2_zfmisc_1(X997,X998) )
      & ( r2_hidden(esk26_3(X997,X998,X999),X998)
        | r2_hidden(esk24_3(X997,X998,X999),X999)
        | X999 = k2_zfmisc_1(X997,X998) )
      & ( esk24_3(X997,X998,X999) = k4_tarski(esk25_3(X997,X998,X999),esk26_3(X997,X998,X999))
        | r2_hidden(esk24_3(X997,X998,X999),X999)
        | X999 = k2_zfmisc_1(X997,X998) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_zfmisc_1])])])])])])).

cnf(c_0_99,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,k5_xboole_0(X2,k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))))))) ),
    inference(er,[status(thm)],[inference(rw,[status(thm)],[c_0_87,c_0_88])])).

cnf(c_0_100,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,X2)) = X2 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_77]),c_0_89])).

cnf(c_0_101,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k3_tarski(k6_enumset1(k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_90,c_0_73]),c_0_40]),c_0_47]),c_0_48]),c_0_48]),c_0_49]),c_0_49]),c_0_62]),c_0_62]),c_0_63]),c_0_63]),c_0_63]),c_0_63]),c_0_63]),c_0_63]),c_0_63]),c_0_64]),c_0_64]),c_0_64]),c_0_64]),c_0_64]),c_0_64]),c_0_64]),c_0_64]),c_0_64])).

cnf(c_0_102,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k3_tarski(k6_enumset1(k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X8))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_91,c_0_40]),c_0_47]),c_0_48]),c_0_48]),c_0_49]),c_0_49]),c_0_62]),c_0_62]),c_0_63]),c_0_63]),c_0_63]),c_0_63]),c_0_63]),c_0_63]),c_0_63]),c_0_64]),c_0_64]),c_0_64]),c_0_64]),c_0_64]),c_0_64]),c_0_64]),c_0_64])).

cnf(c_0_103,negated_conjecture,
    ( r1_xboole_0(X1,esk37_0)
    | r2_hidden(X2,esk40_0)
    | ~ r2_hidden(X2,esk38_0) ),
    inference(spm,[status(thm)],[c_0_92,c_0_71])).

cnf(c_0_104,negated_conjecture,
    ( r1_xboole_0(X1,esk39_0)
    | r1_tarski(esk40_0,X2)
    | r2_hidden(esk2_2(esk40_0,X2),esk38_0) ),
    inference(spm,[status(thm)],[c_0_93,c_0_71])).

cnf(c_0_105,negated_conjecture,
    ( r1_xboole_0(X1,esk38_0)
    | r2_hidden(X2,esk39_0)
    | ~ r2_hidden(X2,esk37_0) ),
    inference(spm,[status(thm)],[c_0_94,c_0_71])).

cnf(c_0_106,plain,
    ( ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2),X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_95,c_0_40]),c_0_48]),c_0_49]),c_0_62]),c_0_63]),c_0_64])).

cnf(c_0_107,negated_conjecture,
    ( r1_xboole_0(X1,esk40_0)
    | r1_tarski(esk39_0,esk37_0) ),
    inference(spm,[status(thm)],[c_0_96,c_0_97])).

cnf(c_0_108,plain,
    ( r2_hidden(esk23_4(X1,X2,X3,X4),X2)
    | ~ r2_hidden(X4,X3)
    | X3 != k2_zfmisc_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_98])).

cnf(c_0_109,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))))) ),
    inference(rw,[status(thm)],[c_0_99,c_0_100])).

cnf(c_0_110,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X7) = k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) ),
    inference(rw,[status(thm)],[c_0_101,c_0_102])).

fof(c_0_111,plain,(
    ! [X1005,X1006,X1007,X1009,X1010,X1011,X1012,X1014] :
      ( ( r2_hidden(X1007,esk27_3(X1005,X1006,X1007))
        | ~ r2_hidden(X1007,X1006)
        | X1006 != k3_tarski(X1005) )
      & ( r2_hidden(esk27_3(X1005,X1006,X1007),X1005)
        | ~ r2_hidden(X1007,X1006)
        | X1006 != k3_tarski(X1005) )
      & ( ~ r2_hidden(X1009,X1010)
        | ~ r2_hidden(X1010,X1005)
        | r2_hidden(X1009,X1006)
        | X1006 != k3_tarski(X1005) )
      & ( ~ r2_hidden(esk28_2(X1011,X1012),X1012)
        | ~ r2_hidden(esk28_2(X1011,X1012),X1014)
        | ~ r2_hidden(X1014,X1011)
        | X1012 = k3_tarski(X1011) )
      & ( r2_hidden(esk28_2(X1011,X1012),esk29_2(X1011,X1012))
        | r2_hidden(esk28_2(X1011,X1012),X1012)
        | X1012 = k3_tarski(X1011) )
      & ( r2_hidden(esk29_2(X1011,X1012),X1011)
        | r2_hidden(esk28_2(X1011,X1012),X1012)
        | X1012 = k3_tarski(X1011) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tarski])])])])])])).

cnf(c_0_112,negated_conjecture,
    ( r1_xboole_0(X1,esk37_0)
    | r1_tarski(esk38_0,X2)
    | r2_hidden(esk2_2(esk38_0,X2),esk40_0) ),
    inference(spm,[status(thm)],[c_0_103,c_0_83])).

cnf(c_0_113,negated_conjecture,
    ( r1_xboole_0(X1,esk39_0)
    | r1_tarski(esk40_0,esk38_0) ),
    inference(spm,[status(thm)],[c_0_96,c_0_104])).

cnf(c_0_114,plain,
    ( r2_hidden(esk22_4(X1,X2,X3,X4),X1)
    | ~ r2_hidden(X4,X3)
    | X3 != k2_zfmisc_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_98])).

cnf(c_0_115,negated_conjecture,
    ( r1_xboole_0(X1,esk38_0)
    | r1_tarski(esk37_0,X2)
    | r2_hidden(esk2_2(esk37_0,X2),esk39_0) ),
    inference(spm,[status(thm)],[c_0_105,c_0_83])).

cnf(c_0_116,negated_conjecture,
    ( r1_tarski(esk39_0,esk37_0)
    | ~ r2_hidden(X1,esk40_0) ),
    inference(spm,[status(thm)],[c_0_106,c_0_107])).

cnf(c_0_117,plain,
    ( r2_hidden(esk23_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X2)
    | ~ r2_hidden(X3,k2_zfmisc_1(X1,X2)) ),
    inference(er,[status(thm)],[c_0_108])).

cnf(c_0_118,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_110]),c_0_78]),c_0_77])).

cnf(c_0_119,plain,
    ( r2_hidden(esk29_2(X1,X2),X1)
    | r2_hidden(esk28_2(X1,X2),X2)
    | X2 = k3_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_111])).

cnf(c_0_120,plain,
    ( k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t2_zfmisc_1])).

cnf(c_0_121,negated_conjecture,
    ( r1_xboole_0(X1,esk37_0)
    | r1_tarski(esk38_0,esk40_0) ),
    inference(spm,[status(thm)],[c_0_96,c_0_112])).

cnf(c_0_122,negated_conjecture,
    ( r1_tarski(esk40_0,esk38_0)
    | ~ r2_hidden(X1,esk39_0) ),
    inference(spm,[status(thm)],[c_0_106,c_0_113])).

cnf(c_0_123,plain,
    ( r2_hidden(esk22_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X1)
    | ~ r2_hidden(X3,k2_zfmisc_1(X1,X2)) ),
    inference(er,[status(thm)],[c_0_114])).

cnf(c_0_124,negated_conjecture,
    ( r1_xboole_0(X1,esk38_0)
    | r1_tarski(esk37_0,esk39_0) ),
    inference(spm,[status(thm)],[c_0_96,c_0_115])).

cnf(c_0_125,negated_conjecture,
    ( r1_tarski(esk39_0,esk37_0)
    | ~ r2_hidden(X1,k2_zfmisc_1(X2,esk40_0)) ),
    inference(spm,[status(thm)],[c_0_116,c_0_117])).

cnf(c_0_126,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk28_2(k1_xboole_0,X1),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_118,c_0_119]),c_0_120])).

cnf(c_0_127,negated_conjecture,
    ( r1_tarski(esk38_0,esk40_0)
    | ~ r2_hidden(X1,esk37_0) ),
    inference(spm,[status(thm)],[c_0_106,c_0_121])).

fof(c_0_128,plain,(
    ! [X23,X24,X25] :
      ( ( ~ v1_xboole_0(X23)
        | ~ r2_hidden(X24,X23) )
      & ( r2_hidden(esk1_1(X25),X25)
        | v1_xboole_0(X25) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_129,negated_conjecture,
    ( r1_tarski(esk40_0,esk38_0)
    | ~ r2_hidden(X1,k2_zfmisc_1(esk39_0,X2)) ),
    inference(spm,[status(thm)],[c_0_122,c_0_123])).

cnf(c_0_130,negated_conjecture,
    ( r1_tarski(esk37_0,esk39_0)
    | ~ r2_hidden(X1,esk38_0) ),
    inference(spm,[status(thm)],[c_0_106,c_0_124])).

cnf(c_0_131,negated_conjecture,
    ( k2_zfmisc_1(esk37_0,esk38_0) != k2_zfmisc_1(esk39_0,esk40_0) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_132,negated_conjecture,
    ( k2_zfmisc_1(X1,esk40_0) = k1_xboole_0
    | r1_tarski(esk39_0,esk37_0) ),
    inference(spm,[status(thm)],[c_0_125,c_0_126])).

cnf(c_0_133,negated_conjecture,
    ( r1_tarski(esk38_0,esk40_0)
    | ~ r2_hidden(X1,k2_zfmisc_1(esk37_0,X2)) ),
    inference(spm,[status(thm)],[c_0_127,c_0_123])).

cnf(c_0_134,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_128])).

fof(c_0_135,plain,(
    ! [X102] :
      ( X102 = k1_xboole_0
      | r2_hidden(esk13_1(X102),X102) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

cnf(c_0_136,negated_conjecture,
    ( k2_zfmisc_1(esk39_0,X1) = k1_xboole_0
    | r1_tarski(esk40_0,esk38_0) ),
    inference(spm,[status(thm)],[c_0_129,c_0_126])).

cnf(c_0_137,negated_conjecture,
    ( r1_tarski(esk37_0,esk39_0)
    | ~ r2_hidden(X1,k2_zfmisc_1(X2,esk38_0)) ),
    inference(spm,[status(thm)],[c_0_130,c_0_117])).

cnf(c_0_138,negated_conjecture,
    ( r1_tarski(esk39_0,esk37_0)
    | k2_zfmisc_1(esk37_0,esk38_0) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_131,c_0_132])).

cnf(c_0_139,negated_conjecture,
    ( k2_zfmisc_1(esk37_0,X1) = k1_xboole_0
    | r1_tarski(esk38_0,esk40_0) ),
    inference(spm,[status(thm)],[c_0_133,c_0_126])).

fof(c_0_140,plain,(
    ! [X381,X382] :
      ( ~ r2_hidden(X381,X382)
      | ~ v1_xboole_0(X382) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

cnf(c_0_141,negated_conjecture,
    ( v1_xboole_0(esk37_0)
    | r2_hidden(X1,esk40_0)
    | ~ r2_hidden(X1,esk38_0) ),
    inference(spm,[status(thm)],[c_0_92,c_0_134])).

cnf(c_0_142,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk13_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_135])).

fof(c_0_143,plain,(
    ! [X347,X348] :
      ( v1_xboole_0(X348)
      | ~ r1_tarski(X348,X347)
      | ~ r1_xboole_0(X348,X347) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t69_xboole_1])])])).

fof(c_0_144,plain,(
    ! [X339] : r1_xboole_0(X339,k1_xboole_0) ),
    inference(variable_rename,[status(thm)],[t65_xboole_1])).

cnf(c_0_145,negated_conjecture,
    ( r1_tarski(esk40_0,esk38_0)
    | k2_zfmisc_1(esk37_0,esk38_0) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_131,c_0_136])).

cnf(c_0_146,negated_conjecture,
    ( k2_zfmisc_1(X1,esk38_0) = k1_xboole_0
    | r1_tarski(esk37_0,esk39_0) ),
    inference(spm,[status(thm)],[c_0_137,c_0_126])).

cnf(c_0_147,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_148,negated_conjecture,
    ( r1_tarski(esk38_0,esk40_0)
    | r1_tarski(esk39_0,esk37_0) ),
    inference(spm,[status(thm)],[c_0_138,c_0_139])).

cnf(c_0_149,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_140])).

cnf(c_0_150,negated_conjecture,
    ( esk38_0 = k1_xboole_0
    | v1_xboole_0(esk37_0)
    | r2_hidden(esk13_1(esk38_0),esk40_0) ),
    inference(spm,[status(thm)],[c_0_141,c_0_142])).

cnf(c_0_151,plain,
    ( v1_xboole_0(X1)
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_143])).

cnf(c_0_152,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_144])).

cnf(c_0_153,negated_conjecture,
    ( r1_tarski(esk37_0,esk39_0)
    | r1_tarski(esk40_0,esk38_0) ),
    inference(spm,[status(thm)],[c_0_145,c_0_146])).

cnf(c_0_154,negated_conjecture,
    ( esk40_0 = k1_xboole_0
    | r2_hidden(X1,esk37_0)
    | ~ r2_hidden(X1,esk39_0) ),
    inference(spm,[status(thm)],[c_0_70,c_0_142])).

fof(c_0_155,plain,(
    ! [X104,X105] :
      ( ( r1_tarski(X104,X105)
        | X104 != X105 )
      & ( r1_tarski(X105,X104)
        | X104 != X105 )
      & ( ~ r1_tarski(X104,X105)
        | ~ r1_tarski(X105,X104)
        | X104 = X105 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_156,negated_conjecture,
    ( r1_tarski(esk38_0,esk40_0)
    | ~ r2_hidden(X1,esk39_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_147,c_0_148]),c_0_127])).

cnf(c_0_157,negated_conjecture,
    ( esk39_0 = k1_xboole_0
    | r1_tarski(esk40_0,X1)
    | r2_hidden(esk2_2(esk40_0,X1),esk38_0) ),
    inference(spm,[status(thm)],[c_0_93,c_0_142])).

fof(c_0_158,plain,(
    ! [X69] :
      ( ~ v1_xboole_0(X69)
      | X69 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).

cnf(c_0_159,negated_conjecture,
    ( esk38_0 = k1_xboole_0
    | v1_xboole_0(esk37_0)
    | ~ v1_xboole_0(esk40_0) ),
    inference(spm,[status(thm)],[c_0_149,c_0_150])).

cnf(c_0_160,plain,
    ( v1_xboole_0(X1)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_151,c_0_152])).

cnf(c_0_161,negated_conjecture,
    ( r1_tarski(esk37_0,esk39_0)
    | ~ r2_hidden(X1,esk40_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_147,c_0_153]),c_0_130])).

cnf(c_0_162,negated_conjecture,
    ( esk40_0 = k1_xboole_0
    | r1_tarski(esk39_0,X1)
    | r2_hidden(esk2_2(esk39_0,X1),esk37_0) ),
    inference(spm,[status(thm)],[c_0_154,c_0_83])).

cnf(c_0_163,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_155])).

cnf(c_0_164,negated_conjecture,
    ( esk39_0 = k1_xboole_0
    | r1_tarski(esk38_0,esk40_0) ),
    inference(spm,[status(thm)],[c_0_156,c_0_126])).

cnf(c_0_165,negated_conjecture,
    ( esk39_0 = k1_xboole_0
    | r1_tarski(esk40_0,esk38_0) ),
    inference(spm,[status(thm)],[c_0_96,c_0_157])).

cnf(c_0_166,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_158])).

cnf(c_0_167,negated_conjecture,
    ( esk38_0 = k1_xboole_0
    | v1_xboole_0(esk37_0)
    | ~ r1_tarski(esk40_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_159,c_0_160])).

cnf(c_0_168,negated_conjecture,
    ( esk40_0 = k1_xboole_0
    | r1_tarski(esk37_0,esk39_0) ),
    inference(spm,[status(thm)],[c_0_161,c_0_126])).

cnf(c_0_169,negated_conjecture,
    ( esk40_0 = k1_xboole_0
    | r1_tarski(esk39_0,esk37_0) ),
    inference(spm,[status(thm)],[c_0_96,c_0_162])).

fof(c_0_170,plain,(
    ! [X239] : r1_tarski(k1_xboole_0,X239) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_171,plain,
    ( ~ r2_hidden(X1,k2_zfmisc_1(X2,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_118,c_0_117])).

cnf(c_0_172,negated_conjecture,
    ( esk39_0 = k1_xboole_0
    | esk40_0 = esk38_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_163,c_0_164]),c_0_165])).

cnf(c_0_173,negated_conjecture,
    ( esk38_0 = k1_xboole_0
    | esk37_0 = k1_xboole_0
    | ~ r1_tarski(esk40_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_166,c_0_167])).

cnf(c_0_174,negated_conjecture,
    ( esk40_0 = k1_xboole_0
    | esk39_0 = esk37_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_163,c_0_168]),c_0_169])).

cnf(c_0_175,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_170])).

cnf(c_0_176,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_171,c_0_126])).

cnf(c_0_177,negated_conjecture,
    ( esk39_0 = k1_xboole_0
    | k2_zfmisc_1(esk39_0,esk38_0) != k2_zfmisc_1(esk37_0,esk38_0) ),
    inference(spm,[status(thm)],[c_0_131,c_0_172])).

cnf(c_0_178,negated_conjecture,
    ( esk39_0 = esk37_0
    | esk37_0 = k1_xboole_0
    | esk38_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_173,c_0_174]),c_0_175])])).

cnf(c_0_179,negated_conjecture,
    ( esk39_0 = esk37_0
    | k2_zfmisc_1(esk37_0,esk38_0) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_131,c_0_174]),c_0_176])).

cnf(c_0_180,negated_conjecture,
    ( esk38_0 = k1_xboole_0
    | esk37_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_177,c_0_178])).

cnf(c_0_181,negated_conjecture,
    ( esk37_0 = k1_xboole_0
    | esk39_0 = esk37_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_179,c_0_180]),c_0_176])])).

cnf(c_0_182,plain,
    ( ~ r2_hidden(X1,k2_zfmisc_1(k1_xboole_0,X2)) ),
    inference(spm,[status(thm)],[c_0_118,c_0_123])).

cnf(c_0_183,negated_conjecture,
    ( esk37_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_177,c_0_181])).

cnf(c_0_184,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_182,c_0_126])).

cnf(c_0_185,negated_conjecture,
    ( k2_zfmisc_1(esk39_0,esk40_0) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_131,c_0_183]),c_0_184])).

cnf(c_0_186,negated_conjecture,
    ( esk39_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_179,c_0_183]),c_0_183]),c_0_184])])).

cnf(c_0_187,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_185,c_0_186]),c_0_184])]),
    [proof]).
%------------------------------------------------------------------------------
