%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:37:20 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 292 expanded)
%              Number of clauses        :   45 ( 122 expanded)
%              Number of leaves         :   22 (  84 expanded)
%              Depth                    :   13
%              Number of atoms          :  185 ( 416 expanded)
%              Number of equality atoms :  113 ( 290 expanded)
%              Maximal formula depth    :   22 (   3 average)
%              Maximal clause size      :   28 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t79_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(t13_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(X1)
     => X1 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_zfmisc_1)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t5_boole,axiom,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(commutativity_k5_xboole_0,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

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

fof(t91_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(d1_enumset1,axiom,(
    ! [X1,X2,X3,X4] :
      ( X4 = k1_enumset1(X1,X2,X3)
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ~ ( X5 != X1
              & X5 != X2
              & X5 != X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(c_0_22,plain,(
    ! [X36,X37] : r1_xboole_0(k4_xboole_0(X36,X37),X37) ),
    inference(variable_rename,[status(thm)],[t79_xboole_1])).

fof(c_0_23,plain,(
    ! [X29,X30] : k4_xboole_0(X29,X30) = k5_xboole_0(X29,k3_xboole_0(X29,X30)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_24,plain,(
    ! [X21,X22,X24,X25,X26] :
      ( ( r1_xboole_0(X21,X22)
        | r2_hidden(esk2_2(X21,X22),k3_xboole_0(X21,X22)) )
      & ( ~ r2_hidden(X26,k3_xboole_0(X24,X25))
        | ~ r1_xboole_0(X24,X25) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

cnf(c_0_25,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_26,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_27,plain,(
    ! [X7,X8] : k3_xboole_0(X7,X8) = k3_xboole_0(X8,X7) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_28,plain,(
    ! [X33,X34] : r1_tarski(k4_xboole_0(X33,X34),X33) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

cnf(c_0_29,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_30,plain,
    ( r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X2) ),
    inference(rw,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_31,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_32,plain,(
    ! [X20] : k3_xboole_0(X20,X20) = X20 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

cnf(c_0_33,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_34,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2)))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31])).

cnf(c_0_35,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_36,plain,(
    ! [X27] :
      ( X27 = k1_xboole_0
      | r2_hidden(esk3_1(X27),X27) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

fof(c_0_37,negated_conjecture,(
    ~ ! [X1,X2] :
        ( k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(X1)
       => X1 = X2 ) ),
    inference(assume_negation,[status(cth)],[t13_zfmisc_1])).

fof(c_0_38,plain,(
    ! [X41,X42] : k2_xboole_0(X41,X42) = k5_xboole_0(X41,k4_xboole_0(X42,X41)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_39,plain,(
    ! [X31,X32] :
      ( ~ r1_tarski(X31,X32)
      | k3_xboole_0(X31,X32) = X31 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_40,plain,
    ( r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X1) ),
    inference(rw,[status(thm)],[c_0_33,c_0_26])).

cnf(c_0_41,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,k5_xboole_0(X2,X2))) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_42,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk3_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

fof(c_0_43,plain,(
    ! [X35] : k5_xboole_0(X35,k1_xboole_0) = X35 ),
    inference(variable_rename,[status(thm)],[t5_boole])).

fof(c_0_44,plain,(
    ! [X9,X10] : k5_xboole_0(X9,X10) = k5_xboole_0(X10,X9) ),
    inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).

fof(c_0_45,negated_conjecture,
    ( k2_xboole_0(k1_tarski(esk6_0),k1_tarski(esk7_0)) = k1_tarski(esk6_0)
    & esk6_0 != esk7_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_37])])])).

fof(c_0_46,plain,(
    ! [X61] : k2_tarski(X61,X61) = k1_tarski(X61) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_47,plain,(
    ! [X62,X63] : k1_enumset1(X62,X62,X63) = k2_tarski(X62,X63) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

cnf(c_0_48,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

fof(c_0_49,plain,(
    ! [X64,X65,X66] : k2_enumset1(X64,X64,X65,X66) = k1_enumset1(X64,X65,X66) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_50,plain,(
    ! [X67,X68,X69,X70] : k3_enumset1(X67,X67,X68,X69,X70) = k2_enumset1(X67,X68,X69,X70) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_51,plain,(
    ! [X71,X72,X73,X74,X75] : k4_enumset1(X71,X71,X72,X73,X74,X75) = k3_enumset1(X71,X72,X73,X74,X75) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_52,plain,(
    ! [X76,X77,X78,X79,X80,X81] : k5_enumset1(X76,X76,X77,X78,X79,X80,X81) = k4_enumset1(X76,X77,X78,X79,X80,X81) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_53,plain,(
    ! [X38,X39,X40] : k5_xboole_0(k5_xboole_0(X38,X39),X40) = k5_xboole_0(X38,k5_xboole_0(X39,X40)) ),
    inference(variable_rename,[status(thm)],[t91_xboole_1])).

cnf(c_0_54,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_55,plain,
    ( r1_tarski(k5_xboole_0(X1,X1),X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_35])).

cnf(c_0_56,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X1,X1)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_57,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_58,plain,
    ( k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_59,negated_conjecture,
    ( k2_xboole_0(k1_tarski(esk6_0),k1_tarski(esk7_0)) = k1_tarski(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_60,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_61,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_62,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(rw,[status(thm)],[c_0_48,c_0_26])).

cnf(c_0_63,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_64,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_65,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_66,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_67,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_68,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_31]),c_0_56])).

cnf(c_0_69,plain,
    ( k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_70,negated_conjecture,
    ( k5_xboole_0(k5_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k5_xboole_0(k5_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0),k3_xboole_0(k5_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0),k5_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)))) = k5_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59,c_0_60]),c_0_60]),c_0_60]),c_0_61]),c_0_61]),c_0_61]),c_0_62]),c_0_63]),c_0_63]),c_0_63]),c_0_63]),c_0_63]),c_0_64]),c_0_64]),c_0_64]),c_0_64]),c_0_64]),c_0_65]),c_0_65]),c_0_65]),c_0_65]),c_0_65]),c_0_66]),c_0_66]),c_0_66]),c_0_66]),c_0_66])).

fof(c_0_71,plain,(
    ! [X11,X12,X13,X14,X15,X16,X17,X18] :
      ( ( r2_hidden(X14,X11)
        | ~ r2_hidden(X14,X13)
        | X13 != k3_xboole_0(X11,X12) )
      & ( r2_hidden(X14,X12)
        | ~ r2_hidden(X14,X13)
        | X13 != k3_xboole_0(X11,X12) )
      & ( ~ r2_hidden(X15,X11)
        | ~ r2_hidden(X15,X12)
        | r2_hidden(X15,X13)
        | X13 != k3_xboole_0(X11,X12) )
      & ( ~ r2_hidden(esk1_3(X16,X17,X18),X18)
        | ~ r2_hidden(esk1_3(X16,X17,X18),X16)
        | ~ r2_hidden(esk1_3(X16,X17,X18),X17)
        | X18 = k3_xboole_0(X16,X17) )
      & ( r2_hidden(esk1_3(X16,X17,X18),X16)
        | r2_hidden(esk1_3(X16,X17,X18),X18)
        | X18 = k3_xboole_0(X16,X17) )
      & ( r2_hidden(esk1_3(X16,X17,X18),X17)
        | r2_hidden(esk1_3(X16,X17,X18),X18)
        | X18 = k3_xboole_0(X16,X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

cnf(c_0_72,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,X2)) = X2 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_69])).

cnf(c_0_73,negated_conjecture,
    ( k5_xboole_0(k5_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k5_xboole_0(k5_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0),k3_xboole_0(k5_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k5_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0)))) = k5_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0) ),
    inference(rw,[status(thm)],[c_0_70,c_0_31])).

fof(c_0_74,plain,(
    ! [X43,X44,X45,X46,X47,X48,X49,X50,X51,X52] :
      ( ( ~ r2_hidden(X47,X46)
        | X47 = X43
        | X47 = X44
        | X47 = X45
        | X46 != k1_enumset1(X43,X44,X45) )
      & ( X48 != X43
        | r2_hidden(X48,X46)
        | X46 != k1_enumset1(X43,X44,X45) )
      & ( X48 != X44
        | r2_hidden(X48,X46)
        | X46 != k1_enumset1(X43,X44,X45) )
      & ( X48 != X45
        | r2_hidden(X48,X46)
        | X46 != k1_enumset1(X43,X44,X45) )
      & ( esk4_4(X49,X50,X51,X52) != X49
        | ~ r2_hidden(esk4_4(X49,X50,X51,X52),X52)
        | X52 = k1_enumset1(X49,X50,X51) )
      & ( esk4_4(X49,X50,X51,X52) != X50
        | ~ r2_hidden(esk4_4(X49,X50,X51,X52),X52)
        | X52 = k1_enumset1(X49,X50,X51) )
      & ( esk4_4(X49,X50,X51,X52) != X51
        | ~ r2_hidden(esk4_4(X49,X50,X51,X52),X52)
        | X52 = k1_enumset1(X49,X50,X51) )
      & ( r2_hidden(esk4_4(X49,X50,X51,X52),X52)
        | esk4_4(X49,X50,X51,X52) = X49
        | esk4_4(X49,X50,X51,X52) = X50
        | esk4_4(X49,X50,X51,X52) = X51
        | X52 = k1_enumset1(X49,X50,X51) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).

fof(c_0_75,plain,(
    ! [X54,X55,X56,X57,X58,X59] :
      ( ( ~ r2_hidden(X56,X55)
        | X56 = X54
        | X55 != k1_tarski(X54) )
      & ( X57 != X54
        | r2_hidden(X57,X55)
        | X55 != k1_tarski(X54) )
      & ( ~ r2_hidden(esk5_2(X58,X59),X59)
        | esk5_2(X58,X59) != X58
        | X59 = k1_tarski(X58) )
      & ( r2_hidden(esk5_2(X58,X59),X59)
        | esk5_2(X58,X59) = X58
        | X59 = k1_tarski(X58) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

cnf(c_0_76,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_77,negated_conjecture,
    ( k5_xboole_0(k5_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0),k3_xboole_0(k5_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k5_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_68])).

cnf(c_0_78,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X4,X5,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

cnf(c_0_79,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_80,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_76])).

cnf(c_0_81,negated_conjecture,
    ( k3_xboole_0(k5_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k5_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0)) = k5_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_77]),c_0_57])).

cnf(c_0_82,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k5_enumset1(X4,X4,X4,X4,X4,X5,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_78,c_0_63]),c_0_64]),c_0_65]),c_0_66])).

cnf(c_0_83,plain,
    ( X1 = X3
    | X2 != k5_enumset1(X3,X3,X3,X3,X3,X3,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_79,c_0_60]),c_0_61]),c_0_63]),c_0_64]),c_0_65]),c_0_66])).

cnf(c_0_84,negated_conjecture,
    ( r2_hidden(X1,k5_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))
    | ~ r2_hidden(X1,k5_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_80,c_0_81])).

cnf(c_0_85,plain,
    ( r2_hidden(X1,k5_enumset1(X2,X2,X2,X2,X2,X3,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_82])])).

cnf(c_0_86,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k5_enumset1(X2,X2,X2,X2,X2,X2,X2)) ),
    inference(er,[status(thm)],[c_0_83])).

cnf(c_0_87,negated_conjecture,
    ( r2_hidden(esk7_0,k5_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_84,c_0_85])).

cnf(c_0_88,negated_conjecture,
    ( esk6_0 != esk7_0 ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_89,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_87]),c_0_88]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:33:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.19/0.41  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S054N
% 0.19/0.41  # and selection function GSelectMinInfpos.
% 0.19/0.41  #
% 0.19/0.41  # Preprocessing time       : 0.052 s
% 0.19/0.41  # Presaturation interreduction done
% 0.19/0.41  
% 0.19/0.41  # Proof found!
% 0.19/0.41  # SZS status Theorem
% 0.19/0.41  # SZS output start CNFRefutation
% 0.19/0.41  fof(t79_xboole_1, axiom, ![X1, X2]:r1_xboole_0(k4_xboole_0(X1,X2),X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 0.19/0.41  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.19/0.41  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 0.19/0.41  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.19/0.41  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.19/0.41  fof(idempotence_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 0.19/0.41  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 0.19/0.41  fof(t13_zfmisc_1, conjecture, ![X1, X2]:(k2_xboole_0(k1_tarski(X1),k1_tarski(X2))=k1_tarski(X1)=>X1=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_zfmisc_1)).
% 0.19/0.41  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.19/0.41  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.19/0.41  fof(t5_boole, axiom, ![X1]:k5_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 0.19/0.41  fof(commutativity_k5_xboole_0, axiom, ![X1, X2]:k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 0.19/0.41  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.19/0.41  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.19/0.41  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.19/0.41  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.19/0.41  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 0.19/0.41  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 0.19/0.41  fof(t91_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 0.19/0.41  fof(d4_xboole_0, axiom, ![X1, X2, X3]:(X3=k3_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 0.19/0.41  fof(d1_enumset1, axiom, ![X1, X2, X3, X4]:(X4=k1_enumset1(X1,X2,X3)<=>![X5]:(r2_hidden(X5,X4)<=>~(((X5!=X1&X5!=X2)&X5!=X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 0.19/0.41  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 0.19/0.41  fof(c_0_22, plain, ![X36, X37]:r1_xboole_0(k4_xboole_0(X36,X37),X37), inference(variable_rename,[status(thm)],[t79_xboole_1])).
% 0.19/0.41  fof(c_0_23, plain, ![X29, X30]:k4_xboole_0(X29,X30)=k5_xboole_0(X29,k3_xboole_0(X29,X30)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.19/0.41  fof(c_0_24, plain, ![X21, X22, X24, X25, X26]:((r1_xboole_0(X21,X22)|r2_hidden(esk2_2(X21,X22),k3_xboole_0(X21,X22)))&(~r2_hidden(X26,k3_xboole_0(X24,X25))|~r1_xboole_0(X24,X25))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 0.19/0.41  cnf(c_0_25, plain, (r1_xboole_0(k4_xboole_0(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.41  cnf(c_0_26, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.41  fof(c_0_27, plain, ![X7, X8]:k3_xboole_0(X7,X8)=k3_xboole_0(X8,X7), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.19/0.41  fof(c_0_28, plain, ![X33, X34]:r1_tarski(k4_xboole_0(X33,X34),X33), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.19/0.41  cnf(c_0_29, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.41  cnf(c_0_30, plain, (r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X2)), inference(rw,[status(thm)],[c_0_25, c_0_26])).
% 0.19/0.41  cnf(c_0_31, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.41  fof(c_0_32, plain, ![X20]:k3_xboole_0(X20,X20)=X20, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).
% 0.19/0.41  cnf(c_0_33, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.41  cnf(c_0_34, plain, (~r2_hidden(X1,k3_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2))))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_31])).
% 0.19/0.41  cnf(c_0_35, plain, (k3_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.41  fof(c_0_36, plain, ![X27]:(X27=k1_xboole_0|r2_hidden(esk3_1(X27),X27)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 0.19/0.41  fof(c_0_37, negated_conjecture, ~(![X1, X2]:(k2_xboole_0(k1_tarski(X1),k1_tarski(X2))=k1_tarski(X1)=>X1=X2)), inference(assume_negation,[status(cth)],[t13_zfmisc_1])).
% 0.19/0.41  fof(c_0_38, plain, ![X41, X42]:k2_xboole_0(X41,X42)=k5_xboole_0(X41,k4_xboole_0(X42,X41)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.19/0.41  fof(c_0_39, plain, ![X31, X32]:(~r1_tarski(X31,X32)|k3_xboole_0(X31,X32)=X31), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.19/0.41  cnf(c_0_40, plain, (r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X1)), inference(rw,[status(thm)],[c_0_33, c_0_26])).
% 0.19/0.41  cnf(c_0_41, plain, (~r2_hidden(X1,k3_xboole_0(X2,k5_xboole_0(X2,X2)))), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.19/0.41  cnf(c_0_42, plain, (X1=k1_xboole_0|r2_hidden(esk3_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.19/0.41  fof(c_0_43, plain, ![X35]:k5_xboole_0(X35,k1_xboole_0)=X35, inference(variable_rename,[status(thm)],[t5_boole])).
% 0.19/0.41  fof(c_0_44, plain, ![X9, X10]:k5_xboole_0(X9,X10)=k5_xboole_0(X10,X9), inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).
% 0.19/0.41  fof(c_0_45, negated_conjecture, (k2_xboole_0(k1_tarski(esk6_0),k1_tarski(esk7_0))=k1_tarski(esk6_0)&esk6_0!=esk7_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_37])])])).
% 0.19/0.41  fof(c_0_46, plain, ![X61]:k2_tarski(X61,X61)=k1_tarski(X61), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.19/0.41  fof(c_0_47, plain, ![X62, X63]:k1_enumset1(X62,X62,X63)=k2_tarski(X62,X63), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.19/0.41  cnf(c_0_48, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.19/0.41  fof(c_0_49, plain, ![X64, X65, X66]:k2_enumset1(X64,X64,X65,X66)=k1_enumset1(X64,X65,X66), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.19/0.41  fof(c_0_50, plain, ![X67, X68, X69, X70]:k3_enumset1(X67,X67,X68,X69,X70)=k2_enumset1(X67,X68,X69,X70), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.19/0.41  fof(c_0_51, plain, ![X71, X72, X73, X74, X75]:k4_enumset1(X71,X71,X72,X73,X74,X75)=k3_enumset1(X71,X72,X73,X74,X75), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.19/0.41  fof(c_0_52, plain, ![X76, X77, X78, X79, X80, X81]:k5_enumset1(X76,X76,X77,X78,X79,X80,X81)=k4_enumset1(X76,X77,X78,X79,X80,X81), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.19/0.41  fof(c_0_53, plain, ![X38, X39, X40]:k5_xboole_0(k5_xboole_0(X38,X39),X40)=k5_xboole_0(X38,k5_xboole_0(X39,X40)), inference(variable_rename,[status(thm)],[t91_xboole_1])).
% 0.19/0.41  cnf(c_0_54, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.19/0.41  cnf(c_0_55, plain, (r1_tarski(k5_xboole_0(X1,X1),X1)), inference(spm,[status(thm)],[c_0_40, c_0_35])).
% 0.19/0.41  cnf(c_0_56, plain, (k3_xboole_0(X1,k5_xboole_0(X1,X1))=k1_xboole_0), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.19/0.41  cnf(c_0_57, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.19/0.41  cnf(c_0_58, plain, (k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.19/0.41  cnf(c_0_59, negated_conjecture, (k2_xboole_0(k1_tarski(esk6_0),k1_tarski(esk7_0))=k1_tarski(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.19/0.41  cnf(c_0_60, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.19/0.41  cnf(c_0_61, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.19/0.41  cnf(c_0_62, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))), inference(rw,[status(thm)],[c_0_48, c_0_26])).
% 0.19/0.41  cnf(c_0_63, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.19/0.41  cnf(c_0_64, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.19/0.41  cnf(c_0_65, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.19/0.41  cnf(c_0_66, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.19/0.41  cnf(c_0_67, plain, (k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.19/0.41  cnf(c_0_68, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_31]), c_0_56])).
% 0.19/0.41  cnf(c_0_69, plain, (k5_xboole_0(k1_xboole_0,X1)=X1), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 0.19/0.41  cnf(c_0_70, negated_conjecture, (k5_xboole_0(k5_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k5_xboole_0(k5_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0),k3_xboole_0(k5_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0),k5_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))))=k5_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59, c_0_60]), c_0_60]), c_0_60]), c_0_61]), c_0_61]), c_0_61]), c_0_62]), c_0_63]), c_0_63]), c_0_63]), c_0_63]), c_0_63]), c_0_64]), c_0_64]), c_0_64]), c_0_64]), c_0_64]), c_0_65]), c_0_65]), c_0_65]), c_0_65]), c_0_65]), c_0_66]), c_0_66]), c_0_66]), c_0_66]), c_0_66])).
% 0.19/0.41  fof(c_0_71, plain, ![X11, X12, X13, X14, X15, X16, X17, X18]:((((r2_hidden(X14,X11)|~r2_hidden(X14,X13)|X13!=k3_xboole_0(X11,X12))&(r2_hidden(X14,X12)|~r2_hidden(X14,X13)|X13!=k3_xboole_0(X11,X12)))&(~r2_hidden(X15,X11)|~r2_hidden(X15,X12)|r2_hidden(X15,X13)|X13!=k3_xboole_0(X11,X12)))&((~r2_hidden(esk1_3(X16,X17,X18),X18)|(~r2_hidden(esk1_3(X16,X17,X18),X16)|~r2_hidden(esk1_3(X16,X17,X18),X17))|X18=k3_xboole_0(X16,X17))&((r2_hidden(esk1_3(X16,X17,X18),X16)|r2_hidden(esk1_3(X16,X17,X18),X18)|X18=k3_xboole_0(X16,X17))&(r2_hidden(esk1_3(X16,X17,X18),X17)|r2_hidden(esk1_3(X16,X17,X18),X18)|X18=k3_xboole_0(X16,X17))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).
% 0.19/0.41  cnf(c_0_72, plain, (k5_xboole_0(X1,k5_xboole_0(X1,X2))=X2), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_69])).
% 0.19/0.41  cnf(c_0_73, negated_conjecture, (k5_xboole_0(k5_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k5_xboole_0(k5_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0),k3_xboole_0(k5_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k5_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0))))=k5_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)), inference(rw,[status(thm)],[c_0_70, c_0_31])).
% 0.19/0.41  fof(c_0_74, plain, ![X43, X44, X45, X46, X47, X48, X49, X50, X51, X52]:(((~r2_hidden(X47,X46)|(X47=X43|X47=X44|X47=X45)|X46!=k1_enumset1(X43,X44,X45))&(((X48!=X43|r2_hidden(X48,X46)|X46!=k1_enumset1(X43,X44,X45))&(X48!=X44|r2_hidden(X48,X46)|X46!=k1_enumset1(X43,X44,X45)))&(X48!=X45|r2_hidden(X48,X46)|X46!=k1_enumset1(X43,X44,X45))))&((((esk4_4(X49,X50,X51,X52)!=X49|~r2_hidden(esk4_4(X49,X50,X51,X52),X52)|X52=k1_enumset1(X49,X50,X51))&(esk4_4(X49,X50,X51,X52)!=X50|~r2_hidden(esk4_4(X49,X50,X51,X52),X52)|X52=k1_enumset1(X49,X50,X51)))&(esk4_4(X49,X50,X51,X52)!=X51|~r2_hidden(esk4_4(X49,X50,X51,X52),X52)|X52=k1_enumset1(X49,X50,X51)))&(r2_hidden(esk4_4(X49,X50,X51,X52),X52)|(esk4_4(X49,X50,X51,X52)=X49|esk4_4(X49,X50,X51,X52)=X50|esk4_4(X49,X50,X51,X52)=X51)|X52=k1_enumset1(X49,X50,X51)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).
% 0.19/0.41  fof(c_0_75, plain, ![X54, X55, X56, X57, X58, X59]:(((~r2_hidden(X56,X55)|X56=X54|X55!=k1_tarski(X54))&(X57!=X54|r2_hidden(X57,X55)|X55!=k1_tarski(X54)))&((~r2_hidden(esk5_2(X58,X59),X59)|esk5_2(X58,X59)!=X58|X59=k1_tarski(X58))&(r2_hidden(esk5_2(X58,X59),X59)|esk5_2(X58,X59)=X58|X59=k1_tarski(X58)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.19/0.41  cnf(c_0_76, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_71])).
% 0.19/0.41  cnf(c_0_77, negated_conjecture, (k5_xboole_0(k5_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0),k3_xboole_0(k5_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k5_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0)))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_73]), c_0_68])).
% 0.19/0.41  cnf(c_0_78, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X4,X5,X2)), inference(split_conjunct,[status(thm)],[c_0_74])).
% 0.19/0.41  cnf(c_0_79, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_75])).
% 0.19/0.41  cnf(c_0_80, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k3_xboole_0(X2,X3))), inference(er,[status(thm)],[c_0_76])).
% 0.19/0.41  cnf(c_0_81, negated_conjecture, (k3_xboole_0(k5_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k5_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0))=k5_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_77]), c_0_57])).
% 0.19/0.42  cnf(c_0_82, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k5_enumset1(X4,X4,X4,X4,X4,X5,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_78, c_0_63]), c_0_64]), c_0_65]), c_0_66])).
% 0.19/0.42  cnf(c_0_83, plain, (X1=X3|X2!=k5_enumset1(X3,X3,X3,X3,X3,X3,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_79, c_0_60]), c_0_61]), c_0_63]), c_0_64]), c_0_65]), c_0_66])).
% 0.19/0.42  cnf(c_0_84, negated_conjecture, (r2_hidden(X1,k5_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))|~r2_hidden(X1,k5_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0))), inference(spm,[status(thm)],[c_0_80, c_0_81])).
% 0.19/0.42  cnf(c_0_85, plain, (r2_hidden(X1,k5_enumset1(X2,X2,X2,X2,X2,X3,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_82])])).
% 0.19/0.42  cnf(c_0_86, plain, (X1=X2|~r2_hidden(X1,k5_enumset1(X2,X2,X2,X2,X2,X2,X2))), inference(er,[status(thm)],[c_0_83])).
% 0.19/0.42  cnf(c_0_87, negated_conjecture, (r2_hidden(esk7_0,k5_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))), inference(spm,[status(thm)],[c_0_84, c_0_85])).
% 0.19/0.42  cnf(c_0_88, negated_conjecture, (esk6_0!=esk7_0), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.19/0.42  cnf(c_0_89, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_87]), c_0_88]), ['proof']).
% 0.19/0.42  # SZS output end CNFRefutation
% 0.19/0.42  # Proof object total steps             : 90
% 0.19/0.42  # Proof object clause steps            : 45
% 0.19/0.42  # Proof object formula steps           : 45
% 0.19/0.42  # Proof object conjectures             : 12
% 0.19/0.42  # Proof object clause conjectures      : 9
% 0.19/0.42  # Proof object formula conjectures     : 3
% 0.19/0.42  # Proof object initial clauses used    : 23
% 0.19/0.42  # Proof object initial formulas used   : 22
% 0.19/0.42  # Proof object generating inferences   : 12
% 0.19/0.42  # Proof object simplifying inferences  : 52
% 0.19/0.42  # Training examples: 0 positive, 0 negative
% 0.19/0.42  # Parsed axioms                        : 22
% 0.19/0.42  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.42  # Initial clauses                      : 39
% 0.19/0.42  # Removed in clause preprocessing      : 8
% 0.19/0.42  # Initial clauses in saturation        : 31
% 0.19/0.42  # Processed clauses                    : 214
% 0.19/0.42  # ...of these trivial                  : 18
% 0.19/0.42  # ...subsumed                          : 88
% 0.19/0.42  # ...remaining for further processing  : 108
% 0.19/0.42  # Other redundant clauses eliminated   : 13
% 0.19/0.42  # Clauses deleted for lack of memory   : 0
% 0.19/0.42  # Backward-subsumed                    : 0
% 0.19/0.42  # Backward-rewritten                   : 16
% 0.19/0.42  # Generated clauses                    : 400
% 0.19/0.42  # ...of the previous two non-trivial   : 302
% 0.19/0.42  # Contextual simplify-reflections      : 0
% 0.19/0.42  # Paramodulations                      : 387
% 0.19/0.42  # Factorizations                       : 4
% 0.19/0.42  # Equation resolutions                 : 13
% 0.19/0.42  # Propositional unsat checks           : 0
% 0.19/0.42  #    Propositional check models        : 0
% 0.19/0.42  #    Propositional check unsatisfiable : 0
% 0.19/0.42  #    Propositional clauses             : 0
% 0.19/0.42  #    Propositional clauses after purity: 0
% 0.19/0.42  #    Propositional unsat core size     : 0
% 0.19/0.42  #    Propositional preprocessing time  : 0.000
% 0.19/0.42  #    Propositional encoding time       : 0.000
% 0.19/0.42  #    Propositional solver time         : 0.000
% 0.19/0.42  #    Success case prop preproc time    : 0.000
% 0.19/0.42  #    Success case prop encoding time   : 0.000
% 0.19/0.42  #    Success case prop solver time     : 0.000
% 0.19/0.42  # Current number of processed clauses  : 53
% 0.19/0.42  #    Positive orientable unit clauses  : 29
% 0.19/0.42  #    Positive unorientable unit clauses: 2
% 0.19/0.42  #    Negative unit clauses             : 5
% 0.19/0.42  #    Non-unit-clauses                  : 17
% 0.19/0.42  # Current number of unprocessed clauses: 131
% 0.19/0.42  # ...number of literals in the above   : 245
% 0.19/0.42  # Current number of archived formulas  : 0
% 0.19/0.42  # Current number of archived clauses   : 54
% 0.19/0.42  # Clause-clause subsumption calls (NU) : 73
% 0.19/0.42  # Rec. Clause-clause subsumption calls : 59
% 0.19/0.42  # Non-unit clause-clause subsumptions  : 0
% 0.19/0.42  # Unit Clause-clause subsumption calls : 20
% 0.19/0.42  # Rewrite failures with RHS unbound    : 0
% 0.19/0.42  # BW rewrite match attempts            : 69
% 0.19/0.42  # BW rewrite match successes           : 32
% 0.19/0.42  # Condensation attempts                : 0
% 0.19/0.42  # Condensation successes               : 0
% 0.19/0.42  # Termbank termtop insertions          : 6854
% 0.19/0.42  
% 0.19/0.42  # -------------------------------------------------
% 0.19/0.42  # User time                : 0.067 s
% 0.19/0.42  # System time              : 0.005 s
% 0.19/0.42  # Total time               : 0.072 s
% 0.19/0.42  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
