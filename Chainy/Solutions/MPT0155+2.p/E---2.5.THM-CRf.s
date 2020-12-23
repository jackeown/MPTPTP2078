%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0155+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:38 EST 2020

% Result     : Theorem 1.84s
% Output     : CNFRefutation 1.84s
% Verified   : 
% Statistics : Number of formulae       :  114 (1028 expanded)
%              Number of clauses        :   63 ( 441 expanded)
%              Number of leaves         :   25 ( 292 expanded)
%              Depth                    :   14
%              Number of atoms          :  214 (1202 expanded)
%              Number of equality atoms :  140 (1047 expanded)
%              Maximal formula depth    :   22 (   3 average)
%              Maximal clause size      :   28 (   1 average)
%              Maximal term depth       :    8 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t49_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT002+2.ax',t49_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT002+2.ax',t100_xboole_1)).

fof(t22_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k3_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT002+2.ax',t22_xboole_1)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT002+2.ax',t98_xboole_1)).

fof(t51_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT002+2.ax',t51_xboole_1)).

fof(t16_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT002+2.ax',t16_xboole_1)).

fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',t4_xboole_0)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',commutativity_k3_xboole_0)).

fof(t91_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT002+2.ax',t91_xboole_1)).

fof(t95_xboole_1,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT002+2.ax',t95_xboole_1)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',t7_xboole_0)).

fof(t79_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT002+2.ax',t79_xboole_1)).

fof(t21_xboole_1,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,k2_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT002+2.ax',t21_xboole_1)).

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',idempotence_k3_xboole_0)).

fof(t71_enumset1,conjecture,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t44_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t93_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT002+2.ax',t93_xboole_1)).

fof(t112_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2)) = k3_xboole_0(k5_xboole_0(X1,X3),X2) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT002+2.ax',t112_xboole_1)).

fof(commutativity_k5_xboole_0,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',commutativity_k5_xboole_0)).

fof(t5_boole,axiom,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT002+2.ax',t5_boole)).

fof(d3_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            | r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',d3_xboole_0)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(d1_enumset1,axiom,(
    ! [X1,X2,X3,X4] :
      ( X4 = k1_enumset1(X1,X2,X3)
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ~ ( X5 != X1
              & X5 != X2
              & X5 != X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(c_0_25,plain,(
    ! [X286,X287,X288] : k3_xboole_0(X286,k4_xboole_0(X287,X288)) = k4_xboole_0(k3_xboole_0(X286,X287),X288) ),
    inference(variable_rename,[status(thm)],[t49_xboole_1])).

fof(c_0_26,plain,(
    ! [X123,X124] : k4_xboole_0(X123,X124) = k5_xboole_0(X123,k3_xboole_0(X123,X124)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_27,plain,(
    ! [X211,X212] : k2_xboole_0(X211,k3_xboole_0(X211,X212)) = X211 ),
    inference(variable_rename,[status(thm)],[t22_xboole_1])).

fof(c_0_28,plain,(
    ! [X429,X430] : k2_xboole_0(X429,X430) = k5_xboole_0(X429,k4_xboole_0(X430,X429)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_29,plain,(
    ! [X296,X297] : k2_xboole_0(k3_xboole_0(X296,X297),k4_xboole_0(X296,X297)) = X296 ),
    inference(variable_rename,[status(thm)],[t51_xboole_1])).

cnf(c_0_30,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_31,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_32,plain,(
    ! [X190,X191,X192] : k3_xboole_0(k3_xboole_0(X190,X191),X192) = k3_xboole_0(X190,k3_xboole_0(X191,X192)) ),
    inference(variable_rename,[status(thm)],[t16_xboole_1])).

cnf(c_0_33,plain,
    ( k2_xboole_0(X1,k3_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_34,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_35,plain,(
    ! [X86,X87,X89,X90,X91] :
      ( ( r1_xboole_0(X86,X87)
        | r2_hidden(esk11_2(X86,X87),k3_xboole_0(X86,X87)) )
      & ( ~ r2_hidden(X91,k3_xboole_0(X89,X90))
        | ~ r1_xboole_0(X89,X90) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

fof(c_0_36,plain,(
    ! [X15,X16] : k3_xboole_0(X15,X16) = k3_xboole_0(X16,X15) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_37,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_38,plain,(
    ! [X414,X415,X416] : k5_xboole_0(k5_xboole_0(X414,X415),X416) = k5_xboole_0(X414,k5_xboole_0(X415,X416)) ),
    inference(variable_rename,[status(thm)],[t91_xboole_1])).

cnf(c_0_39,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))) = k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k3_xboole_0(X1,X2),X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_31]),c_0_31])).

cnf(c_0_40,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_41,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k3_xboole_0(X1,X2),X1))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_34]),c_0_31])).

fof(c_0_42,plain,(
    ! [X422,X423] : k3_xboole_0(X422,X423) = k5_xboole_0(k5_xboole_0(X422,X423),k2_xboole_0(X422,X423)) ),
    inference(variable_rename,[status(thm)],[t95_xboole_1])).

cnf(c_0_43,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_44,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

fof(c_0_45,plain,(
    ! [X98] :
      ( X98 = k1_xboole_0
      | r2_hidden(esk13_1(X98),X98) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

fof(c_0_46,plain,(
    ! [X375,X376] : r1_xboole_0(k4_xboole_0(X375,X376),X376) ),
    inference(variable_rename,[status(thm)],[t79_xboole_1])).

fof(c_0_47,plain,(
    ! [X209,X210] : k3_xboole_0(X209,k2_xboole_0(X209,X210)) = X209 ),
    inference(variable_rename,[status(thm)],[t21_xboole_1])).

fof(c_0_48,plain,(
    ! [X63] : k3_xboole_0(X63,X63) = X63 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

cnf(c_0_49,plain,
    ( k5_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k3_xboole_0(X1,X2)))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_34]),c_0_31]),c_0_31])).

cnf(c_0_50,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_51,plain,
    ( k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,k3_xboole_0(X2,X3))) = k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))) ),
    inference(rw,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_52,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,k3_xboole_0(X2,X1)))) = X1 ),
    inference(rw,[status(thm)],[c_0_41,c_0_40])).

fof(c_0_53,negated_conjecture,(
    ~ ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(assume_negation,[status(cth)],[t71_enumset1])).

fof(c_0_54,plain,(
    ! [X504,X505,X506,X507] : k2_enumset1(X504,X505,X506,X507) = k2_xboole_0(k1_tarski(X504),k1_enumset1(X505,X506,X507)) ),
    inference(variable_rename,[status(thm)],[t44_enumset1])).

fof(c_0_55,plain,(
    ! [X664] : k2_tarski(X664,X664) = k1_tarski(X664) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_56,plain,(
    ! [X665,X666] : k1_enumset1(X665,X665,X666) = k2_tarski(X665,X666) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_57,plain,(
    ! [X418,X419] : k2_xboole_0(X418,X419) = k2_xboole_0(k5_xboole_0(X418,X419),k3_xboole_0(X418,X419)) ),
    inference(variable_rename,[status(thm)],[t93_xboole_1])).

cnf(c_0_58,plain,
    ( k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_59,plain,
    ( ~ r1_xboole_0(X1,X2)
    | ~ r2_hidden(X3,k3_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_60,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk13_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_61,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

fof(c_0_62,plain,(
    ! [X157,X158,X159] : k5_xboole_0(k3_xboole_0(X157,X158),k3_xboole_0(X159,X158)) = k3_xboole_0(k5_xboole_0(X157,X159),X158) ),
    inference(variable_rename,[status(thm)],[t112_xboole_1])).

fof(c_0_63,plain,(
    ! [X17,X18] : k5_xboole_0(X17,X18) = k5_xboole_0(X18,X17) ),
    inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).

cnf(c_0_64,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_65,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_66,plain,
    ( k5_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X1,X2))))))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_44]),c_0_40]),c_0_50]),c_0_51])).

cnf(c_0_67,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) = X1 ),
    inference(rw,[status(thm)],[c_0_52,c_0_51])).

fof(c_0_68,negated_conjecture,(
    k2_enumset1(esk19_0,esk19_0,esk20_0,esk21_0) != k1_enumset1(esk19_0,esk20_0,esk21_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_53])])])).

cnf(c_0_69,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_70,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_71,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_72,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_73,plain,
    ( k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58,c_0_34]),c_0_31])).

cnf(c_0_74,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_75,plain,
    ( r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X2) ),
    inference(rw,[status(thm)],[c_0_61,c_0_31])).

fof(c_0_76,plain,(
    ! [X320] : k5_xboole_0(X320,k1_xboole_0) = X320 ),
    inference(variable_rename,[status(thm)],[t5_boole])).

cnf(c_0_77,plain,
    ( k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2)) = k3_xboole_0(k5_xboole_0(X1,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_78,plain,
    ( k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_79,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_64,c_0_34]),c_0_31])).

cnf(c_0_80,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_40,c_0_65])).

cnf(c_0_81,plain,
    ( k5_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,k3_xboole_0(X1,X2))) = X1 ),
    inference(rw,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_82,negated_conjecture,
    ( k2_enumset1(esk19_0,esk19_0,esk20_0,esk21_0) != k1_enumset1(esk19_0,esk20_0,esk21_0) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_83,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k5_xboole_0(k1_enumset1(X1,X1,X1),k5_xboole_0(k1_enumset1(X2,X3,X4),k3_xboole_0(k1_enumset1(X2,X3,X4),k1_enumset1(X1,X1,X1)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_69,c_0_70]),c_0_71]),c_0_34]),c_0_31])).

fof(c_0_84,plain,(
    ! [X29,X30,X31,X32,X33,X34,X35,X36] :
      ( ( ~ r2_hidden(X32,X31)
        | r2_hidden(X32,X29)
        | r2_hidden(X32,X30)
        | X31 != k2_xboole_0(X29,X30) )
      & ( ~ r2_hidden(X33,X29)
        | r2_hidden(X33,X31)
        | X31 != k2_xboole_0(X29,X30) )
      & ( ~ r2_hidden(X33,X30)
        | r2_hidden(X33,X31)
        | X31 != k2_xboole_0(X29,X30) )
      & ( ~ r2_hidden(esk3_3(X34,X35,X36),X34)
        | ~ r2_hidden(esk3_3(X34,X35,X36),X36)
        | X36 = k2_xboole_0(X34,X35) )
      & ( ~ r2_hidden(esk3_3(X34,X35,X36),X35)
        | ~ r2_hidden(esk3_3(X34,X35,X36),X36)
        | X36 = k2_xboole_0(X34,X35) )
      & ( r2_hidden(esk3_3(X34,X35,X36),X36)
        | r2_hidden(esk3_3(X34,X35,X36),X34)
        | r2_hidden(esk3_3(X34,X35,X36),X35)
        | X36 = k2_xboole_0(X34,X35) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).

cnf(c_0_85,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) = k5_xboole_0(k5_xboole_0(X1,X2),k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_72,c_0_34]),c_0_34]),c_0_31]),c_0_31])).

cnf(c_0_86,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_73,c_0_50])).

cnf(c_0_87,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_88,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_76])).

cnf(c_0_89,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X2,X1)) = k3_xboole_0(X1,k5_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_65]),c_0_78]),c_0_44])).

cnf(c_0_90,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,X1)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_40]),c_0_81])).

cnf(c_0_91,negated_conjecture,
    ( k5_xboole_0(k1_enumset1(esk19_0,esk19_0,esk19_0),k5_xboole_0(k1_enumset1(esk19_0,esk20_0,esk21_0),k3_xboole_0(k1_enumset1(esk19_0,esk20_0,esk21_0),k1_enumset1(esk19_0,esk19_0,esk19_0)))) != k1_enumset1(esk19_0,esk20_0,esk21_0) ),
    inference(rw,[status(thm)],[c_0_82,c_0_83])).

cnf(c_0_92,plain,
    ( X3 = k2_xboole_0(X1,X2)
    | ~ r2_hidden(esk3_3(X1,X2,X3),X2)
    | ~ r2_hidden(esk3_3(X1,X2,X3),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_84])).

cnf(c_0_93,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,k5_xboole_0(X1,X2)))))) = k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_85,c_0_40]),c_0_51]),c_0_50])).

cnf(c_0_94,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X2,X1))) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_77]),c_0_44]),c_0_87]),c_0_88]),c_0_78]),c_0_89]),c_0_90])).

fof(c_0_95,plain,(
    ! [X450,X451,X452,X453,X454,X455] :
      ( ( ~ r2_hidden(X452,X451)
        | X452 = X450
        | X451 != k1_tarski(X450) )
      & ( X453 != X450
        | r2_hidden(X453,X451)
        | X451 != k1_tarski(X450) )
      & ( ~ r2_hidden(esk17_2(X454,X455),X455)
        | esk17_2(X454,X455) != X454
        | X455 = k1_tarski(X454) )
      & ( r2_hidden(esk17_2(X454,X455),X455)
        | esk17_2(X454,X455) = X454
        | X455 = k1_tarski(X454) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

cnf(c_0_96,plain,
    ( r2_hidden(esk3_3(X1,X2,X3),X3)
    | r2_hidden(esk3_3(X1,X2,X3),X1)
    | r2_hidden(esk3_3(X1,X2,X3),X2)
    | X3 = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_84])).

cnf(c_0_97,negated_conjecture,
    ( k5_xboole_0(k1_enumset1(esk19_0,esk19_0,esk19_0),k5_xboole_0(k1_enumset1(esk19_0,esk20_0,esk21_0),k3_xboole_0(k1_enumset1(esk19_0,esk19_0,esk19_0),k1_enumset1(esk19_0,esk20_0,esk21_0)))) != k1_enumset1(esk19_0,esk20_0,esk21_0) ),
    inference(rw,[status(thm)],[c_0_91,c_0_44])).

cnf(c_0_98,plain,
    ( X3 = k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))
    | ~ r2_hidden(esk3_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk3_3(X1,X2,X3),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_92,c_0_34]),c_0_31])).

cnf(c_0_99,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) = k5_xboole_0(X1,k3_xboole_0(X2,k5_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_93,c_0_94]),c_0_90]),c_0_89])).

cnf(c_0_100,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_95])).

cnf(c_0_101,plain,
    ( X3 = k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))
    | r2_hidden(esk3_3(X1,X2,X3),X3)
    | r2_hidden(esk3_3(X1,X2,X3),X2)
    | r2_hidden(esk3_3(X1,X2,X3),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_96,c_0_34]),c_0_31])).

cnf(c_0_102,negated_conjecture,
    ( k5_xboole_0(k1_enumset1(esk19_0,esk19_0,esk19_0),k3_xboole_0(k1_enumset1(esk19_0,esk20_0,esk21_0),k5_xboole_0(k1_enumset1(esk19_0,esk19_0,esk19_0),k1_enumset1(esk19_0,esk20_0,esk21_0)))) != k1_enumset1(esk19_0,esk20_0,esk21_0) ),
    inference(rw,[status(thm)],[c_0_97,c_0_89])).

cnf(c_0_103,plain,
    ( X1 = k5_xboole_0(X2,k3_xboole_0(X3,k5_xboole_0(X2,X3)))
    | ~ r2_hidden(esk3_3(X2,X3,X1),X1)
    | ~ r2_hidden(esk3_3(X2,X3,X1),X3) ),
    inference(rw,[status(thm)],[c_0_98,c_0_99])).

cnf(c_0_104,plain,
    ( X1 = X3
    | X2 != k1_enumset1(X3,X3,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_100,c_0_70]),c_0_71])).

cnf(c_0_105,plain,
    ( X1 = k5_xboole_0(X2,k3_xboole_0(X3,k5_xboole_0(X2,X3)))
    | r2_hidden(esk3_3(X2,X3,X1),X1)
    | r2_hidden(esk3_3(X2,X3,X1),X3)
    | r2_hidden(esk3_3(X2,X3,X1),X2) ),
    inference(rw,[status(thm)],[c_0_101,c_0_99])).

cnf(c_0_106,negated_conjecture,
    ( ~ r2_hidden(esk3_3(k1_enumset1(esk19_0,esk19_0,esk19_0),k1_enumset1(esk19_0,esk20_0,esk21_0),k1_enumset1(esk19_0,esk20_0,esk21_0)),k1_enumset1(esk19_0,esk20_0,esk21_0)) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_103])])).

fof(c_0_107,plain,(
    ! [X439,X440,X441,X442,X443,X444,X445,X446,X447,X448] :
      ( ( ~ r2_hidden(X443,X442)
        | X443 = X439
        | X443 = X440
        | X443 = X441
        | X442 != k1_enumset1(X439,X440,X441) )
      & ( X444 != X439
        | r2_hidden(X444,X442)
        | X442 != k1_enumset1(X439,X440,X441) )
      & ( X444 != X440
        | r2_hidden(X444,X442)
        | X442 != k1_enumset1(X439,X440,X441) )
      & ( X444 != X441
        | r2_hidden(X444,X442)
        | X442 != k1_enumset1(X439,X440,X441) )
      & ( esk16_4(X445,X446,X447,X448) != X445
        | ~ r2_hidden(esk16_4(X445,X446,X447,X448),X448)
        | X448 = k1_enumset1(X445,X446,X447) )
      & ( esk16_4(X445,X446,X447,X448) != X446
        | ~ r2_hidden(esk16_4(X445,X446,X447,X448),X448)
        | X448 = k1_enumset1(X445,X446,X447) )
      & ( esk16_4(X445,X446,X447,X448) != X447
        | ~ r2_hidden(esk16_4(X445,X446,X447,X448),X448)
        | X448 = k1_enumset1(X445,X446,X447) )
      & ( r2_hidden(esk16_4(X445,X446,X447,X448),X448)
        | esk16_4(X445,X446,X447,X448) = X445
        | esk16_4(X445,X446,X447,X448) = X446
        | esk16_4(X445,X446,X447,X448) = X447
        | X448 = k1_enumset1(X445,X446,X447) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).

cnf(c_0_108,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k1_enumset1(X2,X2,X2)) ),
    inference(er,[status(thm)],[c_0_104])).

cnf(c_0_109,negated_conjecture,
    ( r2_hidden(esk3_3(k1_enumset1(esk19_0,esk19_0,esk19_0),k1_enumset1(esk19_0,esk20_0,esk21_0),k1_enumset1(esk19_0,esk20_0,esk21_0)),k1_enumset1(esk19_0,esk19_0,esk19_0)) ),
    inference(sr,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_105])]),c_0_106])).

cnf(c_0_110,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X2,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_107])).

cnf(c_0_111,negated_conjecture,
    ( esk3_3(k1_enumset1(esk19_0,esk19_0,esk19_0),k1_enumset1(esk19_0,esk20_0,esk21_0),k1_enumset1(esk19_0,esk20_0,esk21_0)) = esk19_0 ),
    inference(spm,[status(thm)],[c_0_108,c_0_109])).

cnf(c_0_112,plain,
    ( r2_hidden(X1,k1_enumset1(X1,X2,X3)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_110])])).

cnf(c_0_113,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_106,c_0_111]),c_0_112])]),
    [proof]).
%------------------------------------------------------------------------------
