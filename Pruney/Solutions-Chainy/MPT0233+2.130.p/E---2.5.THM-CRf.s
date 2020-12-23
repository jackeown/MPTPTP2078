%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:39:11 EST 2020

% Result     : Theorem 26.37s
% Output     : CNFRefutation 26.37s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 946 expanded)
%              Number of clauses        :   63 ( 433 expanded)
%              Number of leaves         :   19 ( 255 expanded)
%              Depth                    :   15
%              Number of atoms          :  249 (1598 expanded)
%              Number of equality atoms :  173 (1073 expanded)
%              Maximal formula depth    :   52 (   4 average)
%              Maximal clause size      :   76 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l97_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l97_xboole_1)).

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(t83_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k4_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(t91_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(t64_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] : k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_enumset1(X1,X2,X3),k3_enumset1(X4,X5,X6,X7,X8)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t94_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

fof(t90_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_enumset1)).

fof(l142_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8,X9] : k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k3_enumset1(X5,X6,X7,X8,X9)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l142_enumset1)).

fof(t65_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] : k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_enumset1)).

fof(t28_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ~ ( r1_tarski(k2_tarski(X1,X2),k2_tarski(X3,X4))
        & X1 != X3
        & X1 != X4 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t45_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_enumset1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_enumset1)).

fof(c_0_19,plain,(
    ! [X23,X24] : r1_xboole_0(k3_xboole_0(X23,X24),k5_xboole_0(X23,X24)) ),
    inference(variable_rename,[status(thm)],[l97_xboole_1])).

fof(c_0_20,plain,(
    ! [X12] : k3_xboole_0(X12,X12) = X12 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

fof(c_0_21,plain,(
    ! [X21,X22] :
      ( ( k4_xboole_0(X21,X22) != k1_xboole_0
        | r1_tarski(X21,X22) )
      & ( ~ r1_tarski(X21,X22)
        | k4_xboole_0(X21,X22) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

fof(c_0_22,plain,(
    ! [X25,X26] : k4_xboole_0(X25,X26) = k5_xboole_0(X25,k3_xboole_0(X25,X26)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_23,plain,(
    ! [X19,X20] :
      ( ( r1_tarski(X19,X20)
        | X19 != X20 )
      & ( r1_tarski(X20,X19)
        | X19 != X20 )
      & ( ~ r1_tarski(X19,X20)
        | ~ r1_tarski(X20,X19)
        | X19 = X20 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_24,plain,(
    ! [X13,X14,X16,X17,X18] :
      ( ( r1_xboole_0(X13,X14)
        | r2_hidden(esk1_2(X13,X14),k3_xboole_0(X13,X14)) )
      & ( ~ r2_hidden(X18,k3_xboole_0(X16,X17))
        | ~ r1_xboole_0(X16,X17) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

cnf(c_0_25,plain,
    ( r1_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,plain,
    ( r1_xboole_0(X1,k5_xboole_0(X1,X1)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_32,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_33,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_29])).

fof(c_0_34,plain,(
    ! [X29,X30] :
      ( ( ~ r1_xboole_0(X29,X30)
        | k4_xboole_0(X29,X30) = X29 )
      & ( k4_xboole_0(X29,X30) != X29
        | r1_xboole_0(X29,X30) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).

cnf(c_0_35,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,k5_xboole_0(X2,X2))) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_36,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_26])).

cnf(c_0_37,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk1_2(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_38,plain,(
    ! [X31,X32,X33] : k5_xboole_0(k5_xboole_0(X31,X32),X33) = k5_xboole_0(X31,k5_xboole_0(X32,X33)) ),
    inference(variable_rename,[status(thm)],[t91_xboole_1])).

cnf(c_0_39,plain,
    ( k4_xboole_0(X1,X2) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_40,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,k1_xboole_0)) ),
    inference(rw,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_41,plain,
    ( r2_hidden(esk1_2(X1,X1),X1)
    | r1_xboole_0(X1,X1) ),
    inference(spm,[status(thm)],[c_0_37,c_0_26])).

fof(c_0_42,plain,(
    ! [X85,X86,X87,X88,X89,X90,X91,X92] : k6_enumset1(X85,X86,X87,X88,X89,X90,X91,X92) = k2_xboole_0(k1_enumset1(X85,X86,X87),k3_enumset1(X88,X89,X90,X91,X92)) ),
    inference(variable_rename,[status(thm)],[t64_enumset1])).

fof(c_0_43,plain,(
    ! [X103,X104,X105] : k2_enumset1(X103,X103,X104,X105) = k1_enumset1(X103,X104,X105) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_44,plain,(
    ! [X34,X35] : k2_xboole_0(X34,X35) = k5_xboole_0(k5_xboole_0(X34,X35),k3_xboole_0(X34,X35)) ),
    inference(variable_rename,[status(thm)],[t94_xboole_1])).

fof(c_0_45,plain,(
    ! [X106,X107,X108,X109] : k6_enumset1(X106,X106,X106,X106,X106,X107,X108,X109) = k2_enumset1(X106,X107,X108,X109) ),
    inference(variable_rename,[status(thm)],[t90_enumset1])).

fof(c_0_46,plain,(
    ! [X68,X69,X70,X71,X72,X73,X74,X75,X76] : k7_enumset1(X68,X69,X70,X71,X72,X73,X74,X75,X76) = k2_xboole_0(k2_enumset1(X68,X69,X70,X71),k3_enumset1(X72,X73,X74,X75,X76)) ),
    inference(variable_rename,[status(thm)],[l142_enumset1])).

cnf(c_0_47,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_48,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_39,c_0_28])).

cnf(c_0_49,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_31,c_0_36])).

cnf(c_0_50,plain,
    ( r1_xboole_0(k3_xboole_0(X1,k1_xboole_0),k3_xboole_0(X1,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

fof(c_0_51,plain,(
    ! [X93,X94,X95,X96,X97,X98,X99,X100] : k6_enumset1(X93,X94,X95,X96,X97,X98,X99,X100) = k2_xboole_0(k2_enumset1(X93,X94,X95,X96),k2_enumset1(X97,X98,X99,X100)) ),
    inference(variable_rename,[status(thm)],[t65_enumset1])).

cnf(c_0_52,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_enumset1(X1,X2,X3),k3_enumset1(X4,X5,X6,X7,X8)) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_53,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_54,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_55,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_56,plain,
    ( k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k3_enumset1(X5,X6,X7,X8,X9)) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

fof(c_0_57,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ~ ( r1_tarski(k2_tarski(X1,X2),k2_tarski(X3,X4))
          & X1 != X3
          & X1 != X4 ) ),
    inference(assume_negation,[status(cth)],[t28_zfmisc_1])).

cnf(c_0_58,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,X2)) = k5_xboole_0(k1_xboole_0,X2) ),
    inference(spm,[status(thm)],[c_0_47,c_0_36])).

cnf(c_0_59,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0)) = X1 ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_60,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_50]),c_0_26]),c_0_36])).

cnf(c_0_61,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_62,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k5_xboole_0(k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3),k3_enumset1(X4,X5,X6,X7,X8)),k3_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3),k3_enumset1(X4,X5,X6,X7,X8))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_53]),c_0_54]),c_0_55]),c_0_55])).

cnf(c_0_63,plain,
    ( k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k5_xboole_0(k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4),k3_enumset1(X5,X6,X7,X8,X9)),k3_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4),k3_enumset1(X5,X6,X7,X8,X9))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_54]),c_0_55]),c_0_55])).

fof(c_0_64,negated_conjecture,
    ( r1_tarski(k2_tarski(esk4_0,esk5_0),k2_tarski(esk6_0,esk7_0))
    & esk4_0 != esk6_0
    & esk4_0 != esk7_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_57])])])).

fof(c_0_65,plain,(
    ! [X101,X102] : k1_enumset1(X101,X101,X102) = k2_tarski(X101,X102) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

cnf(c_0_66,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_58,c_0_36])).

cnf(c_0_67,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[c_0_59,c_0_60])).

fof(c_0_68,plain,(
    ! [X81,X82,X83,X84] : k2_enumset1(X81,X82,X83,X84) = k2_xboole_0(k2_tarski(X81,X82),k2_tarski(X83,X84)) ),
    inference(variable_rename,[status(thm)],[t45_enumset1])).

cnf(c_0_69,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k5_xboole_0(k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4),k6_enumset1(X5,X5,X5,X5,X5,X6,X7,X8)),k3_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4),k6_enumset1(X5,X5,X5,X5,X5,X6,X7,X8))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_54]),c_0_55]),c_0_55]),c_0_55]),c_0_55])).

cnf(c_0_70,plain,
    ( k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3),k5_xboole_0(k3_enumset1(X4,X5,X6,X7,X8),k3_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3),k3_enumset1(X4,X5,X6,X7,X8)))) = k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(rw,[status(thm)],[c_0_62,c_0_47])).

cnf(c_0_71,plain,
    ( k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4),k5_xboole_0(k3_enumset1(X5,X6,X7,X8,X9),k3_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4),k3_enumset1(X5,X6,X7,X8,X9)))) = k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) ),
    inference(rw,[status(thm)],[c_0_63,c_0_47])).

cnf(c_0_72,negated_conjecture,
    ( r1_tarski(k2_tarski(esk4_0,esk5_0),k2_tarski(esk6_0,esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_73,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_74,plain,
    ( k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(rw,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_75,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_76,plain,
    ( k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4),k5_xboole_0(k6_enumset1(X5,X5,X5,X5,X5,X6,X7,X8),k3_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4),k6_enumset1(X5,X5,X5,X5,X5,X6,X7,X8)))) = k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(rw,[status(thm)],[c_0_69,c_0_47])).

cnf(c_0_77,plain,
    ( k7_enumset1(X1,X1,X2,X3,X4,X5,X6,X7,X8) = k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(rw,[status(thm)],[c_0_70,c_0_71])).

fof(c_0_78,plain,(
    ! [X27,X28] :
      ( ~ r1_tarski(X27,X28)
      | k3_xboole_0(X27,X28) = X27 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_79,negated_conjecture,
    ( r1_tarski(k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk7_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_72,c_0_73]),c_0_73]),c_0_53]),c_0_53]),c_0_55]),c_0_55])).

cnf(c_0_80,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,X2)) = X2 ),
    inference(rw,[status(thm)],[c_0_58,c_0_74])).

cnf(c_0_81,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,X2))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_47,c_0_36])).

cnf(c_0_82,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4) = k5_xboole_0(k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2),k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X4)),k3_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2),k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X4))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_75,c_0_73]),c_0_73]),c_0_53]),c_0_53]),c_0_54]),c_0_55]),c_0_55]),c_0_55]),c_0_55]),c_0_55])).

fof(c_0_83,plain,(
    ! [X45,X46,X47,X48,X49,X50,X51,X52,X53,X54,X55,X56,X57,X58,X59,X60,X61,X62,X63,X64,X65,X66] :
      ( ( ~ r2_hidden(X55,X54)
        | X55 = X45
        | X55 = X46
        | X55 = X47
        | X55 = X48
        | X55 = X49
        | X55 = X50
        | X55 = X51
        | X55 = X52
        | X55 = X53
        | X54 != k7_enumset1(X45,X46,X47,X48,X49,X50,X51,X52,X53) )
      & ( X56 != X45
        | r2_hidden(X56,X54)
        | X54 != k7_enumset1(X45,X46,X47,X48,X49,X50,X51,X52,X53) )
      & ( X56 != X46
        | r2_hidden(X56,X54)
        | X54 != k7_enumset1(X45,X46,X47,X48,X49,X50,X51,X52,X53) )
      & ( X56 != X47
        | r2_hidden(X56,X54)
        | X54 != k7_enumset1(X45,X46,X47,X48,X49,X50,X51,X52,X53) )
      & ( X56 != X48
        | r2_hidden(X56,X54)
        | X54 != k7_enumset1(X45,X46,X47,X48,X49,X50,X51,X52,X53) )
      & ( X56 != X49
        | r2_hidden(X56,X54)
        | X54 != k7_enumset1(X45,X46,X47,X48,X49,X50,X51,X52,X53) )
      & ( X56 != X50
        | r2_hidden(X56,X54)
        | X54 != k7_enumset1(X45,X46,X47,X48,X49,X50,X51,X52,X53) )
      & ( X56 != X51
        | r2_hidden(X56,X54)
        | X54 != k7_enumset1(X45,X46,X47,X48,X49,X50,X51,X52,X53) )
      & ( X56 != X52
        | r2_hidden(X56,X54)
        | X54 != k7_enumset1(X45,X46,X47,X48,X49,X50,X51,X52,X53) )
      & ( X56 != X53
        | r2_hidden(X56,X54)
        | X54 != k7_enumset1(X45,X46,X47,X48,X49,X50,X51,X52,X53) )
      & ( esk3_10(X57,X58,X59,X60,X61,X62,X63,X64,X65,X66) != X57
        | ~ r2_hidden(esk3_10(X57,X58,X59,X60,X61,X62,X63,X64,X65,X66),X66)
        | X66 = k7_enumset1(X57,X58,X59,X60,X61,X62,X63,X64,X65) )
      & ( esk3_10(X57,X58,X59,X60,X61,X62,X63,X64,X65,X66) != X58
        | ~ r2_hidden(esk3_10(X57,X58,X59,X60,X61,X62,X63,X64,X65,X66),X66)
        | X66 = k7_enumset1(X57,X58,X59,X60,X61,X62,X63,X64,X65) )
      & ( esk3_10(X57,X58,X59,X60,X61,X62,X63,X64,X65,X66) != X59
        | ~ r2_hidden(esk3_10(X57,X58,X59,X60,X61,X62,X63,X64,X65,X66),X66)
        | X66 = k7_enumset1(X57,X58,X59,X60,X61,X62,X63,X64,X65) )
      & ( esk3_10(X57,X58,X59,X60,X61,X62,X63,X64,X65,X66) != X60
        | ~ r2_hidden(esk3_10(X57,X58,X59,X60,X61,X62,X63,X64,X65,X66),X66)
        | X66 = k7_enumset1(X57,X58,X59,X60,X61,X62,X63,X64,X65) )
      & ( esk3_10(X57,X58,X59,X60,X61,X62,X63,X64,X65,X66) != X61
        | ~ r2_hidden(esk3_10(X57,X58,X59,X60,X61,X62,X63,X64,X65,X66),X66)
        | X66 = k7_enumset1(X57,X58,X59,X60,X61,X62,X63,X64,X65) )
      & ( esk3_10(X57,X58,X59,X60,X61,X62,X63,X64,X65,X66) != X62
        | ~ r2_hidden(esk3_10(X57,X58,X59,X60,X61,X62,X63,X64,X65,X66),X66)
        | X66 = k7_enumset1(X57,X58,X59,X60,X61,X62,X63,X64,X65) )
      & ( esk3_10(X57,X58,X59,X60,X61,X62,X63,X64,X65,X66) != X63
        | ~ r2_hidden(esk3_10(X57,X58,X59,X60,X61,X62,X63,X64,X65,X66),X66)
        | X66 = k7_enumset1(X57,X58,X59,X60,X61,X62,X63,X64,X65) )
      & ( esk3_10(X57,X58,X59,X60,X61,X62,X63,X64,X65,X66) != X64
        | ~ r2_hidden(esk3_10(X57,X58,X59,X60,X61,X62,X63,X64,X65,X66),X66)
        | X66 = k7_enumset1(X57,X58,X59,X60,X61,X62,X63,X64,X65) )
      & ( esk3_10(X57,X58,X59,X60,X61,X62,X63,X64,X65,X66) != X65
        | ~ r2_hidden(esk3_10(X57,X58,X59,X60,X61,X62,X63,X64,X65,X66),X66)
        | X66 = k7_enumset1(X57,X58,X59,X60,X61,X62,X63,X64,X65) )
      & ( r2_hidden(esk3_10(X57,X58,X59,X60,X61,X62,X63,X64,X65,X66),X66)
        | esk3_10(X57,X58,X59,X60,X61,X62,X63,X64,X65,X66) = X57
        | esk3_10(X57,X58,X59,X60,X61,X62,X63,X64,X65,X66) = X58
        | esk3_10(X57,X58,X59,X60,X61,X62,X63,X64,X65,X66) = X59
        | esk3_10(X57,X58,X59,X60,X61,X62,X63,X64,X65,X66) = X60
        | esk3_10(X57,X58,X59,X60,X61,X62,X63,X64,X65,X66) = X61
        | esk3_10(X57,X58,X59,X60,X61,X62,X63,X64,X65,X66) = X62
        | esk3_10(X57,X58,X59,X60,X61,X62,X63,X64,X65,X66) = X63
        | esk3_10(X57,X58,X59,X60,X61,X62,X63,X64,X65,X66) = X64
        | esk3_10(X57,X58,X59,X60,X61,X62,X63,X64,X65,X66) = X65
        | X66 = k7_enumset1(X57,X58,X59,X60,X61,X62,X63,X64,X65) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_enumset1])])])])])])).

cnf(c_0_84,plain,
    ( k5_xboole_0(k7_enumset1(X1,X1,X1,X1,X1,X1,X2,X3,X4),k5_xboole_0(k6_enumset1(X5,X5,X5,X5,X5,X6,X7,X8),k3_xboole_0(k7_enumset1(X1,X1,X1,X1,X1,X1,X2,X3,X4),k6_enumset1(X5,X5,X5,X5,X5,X6,X7,X8)))) = k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(spm,[status(thm)],[c_0_76,c_0_77])).

cnf(c_0_85,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_78])).

cnf(c_0_86,negated_conjecture,
    ( r1_tarski(k7_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),k7_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk7_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_79,c_0_77]),c_0_77])).

cnf(c_0_87,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_81]),c_0_67])).

cnf(c_0_88,plain,
    ( k6_enumset1(X1,X1,X1,X2,X3,X3,X3,X4) = k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_82,c_0_47]),c_0_76])).

cnf(c_0_89,plain,
    ( X1 = X3
    | X1 = X4
    | X1 = X5
    | X1 = X6
    | X1 = X7
    | X1 = X8
    | X1 = X9
    | X1 = X10
    | X1 = X11
    | ~ r2_hidden(X1,X2)
    | X2 != k7_enumset1(X3,X4,X5,X6,X7,X8,X9,X10,X11) ),
    inference(split_conjunct,[status(thm)],[c_0_83])).

cnf(c_0_90,plain,
    ( k5_xboole_0(k7_enumset1(X1,X1,X1,X1,X1,X1,X2,X3,X4),k5_xboole_0(k7_enumset1(X5,X5,X5,X5,X5,X5,X6,X7,X8),k3_xboole_0(k7_enumset1(X1,X1,X1,X1,X1,X1,X2,X3,X4),k7_enumset1(X5,X5,X5,X5,X5,X5,X6,X7,X8)))) = k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(spm,[status(thm)],[c_0_84,c_0_77])).

cnf(c_0_91,negated_conjecture,
    ( k3_xboole_0(k7_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),k7_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk7_0)) = k7_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_85,c_0_86])).

cnf(c_0_92,plain,
    ( k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_80,c_0_87])).

cnf(c_0_93,plain,
    ( k7_enumset1(X1,X1,X1,X1,X2,X3,X3,X3,X4) = k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4) ),
    inference(spm,[status(thm)],[c_0_77,c_0_88])).

cnf(c_0_94,plain,
    ( X1 = X2
    | X1 = X3
    | X1 = X4
    | X1 = X5
    | X1 = X6
    | X1 = X7
    | X1 = X8
    | X1 = X9
    | X1 = X10
    | ~ r2_hidden(X1,k7_enumset1(X10,X9,X8,X7,X6,X5,X4,X3,X2)) ),
    inference(er,[status(thm)],[c_0_89])).

cnf(c_0_95,negated_conjecture,
    ( k7_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk7_0) = k7_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk5_0,esk6_0,esk6_0,esk6_0,esk7_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_91]),c_0_92]),c_0_80]),c_0_88]),c_0_93])).

cnf(c_0_96,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k7_enumset1(X2,X4,X5,X6,X7,X8,X9,X10,X11) ),
    inference(split_conjunct,[status(thm)],[c_0_83])).

cnf(c_0_97,negated_conjecture,
    ( X1 = esk7_0
    | X1 = esk6_0
    | ~ r2_hidden(X1,k7_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk5_0,esk6_0,esk6_0,esk6_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_94,c_0_95])).

cnf(c_0_98,plain,
    ( r2_hidden(X1,k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_96])])).

cnf(c_0_99,negated_conjecture,
    ( esk4_0 != esk7_0 ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_100,negated_conjecture,
    ( esk4_0 != esk6_0 ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_101,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_98]),c_0_99]),c_0_100]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n009.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 20:56:11 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  # Version: 2.5pre002
% 0.13/0.33  # No SInE strategy applied
% 0.13/0.33  # Trying AutoSched0 for 299 seconds
% 26.37/26.59  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S054N
% 26.37/26.59  # and selection function GSelectMinInfpos.
% 26.37/26.59  #
% 26.37/26.59  # Preprocessing time       : 0.029 s
% 26.37/26.59  # Presaturation interreduction done
% 26.37/26.59  
% 26.37/26.59  # Proof found!
% 26.37/26.59  # SZS status Theorem
% 26.37/26.59  # SZS output start CNFRefutation
% 26.37/26.59  fof(l97_xboole_1, axiom, ![X1, X2]:r1_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l97_xboole_1)).
% 26.37/26.59  fof(idempotence_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 26.37/26.59  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 26.37/26.59  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 26.37/26.59  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 26.37/26.59  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 26.37/26.59  fof(t83_xboole_1, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k4_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 26.37/26.59  fof(t91_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 26.37/26.59  fof(t64_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8]:k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k1_enumset1(X1,X2,X3),k3_enumset1(X4,X5,X6,X7,X8)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_enumset1)).
% 26.37/26.59  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 26.37/26.59  fof(t94_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_xboole_1)).
% 26.37/26.59  fof(t90_enumset1, axiom, ![X1, X2, X3, X4]:k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_enumset1)).
% 26.37/26.59  fof(l142_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8, X9]:k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k3_enumset1(X5,X6,X7,X8,X9)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l142_enumset1)).
% 26.37/26.59  fof(t65_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8]:k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_enumset1)).
% 26.37/26.59  fof(t28_zfmisc_1, conjecture, ![X1, X2, X3, X4]:~(((r1_tarski(k2_tarski(X1,X2),k2_tarski(X3,X4))&X1!=X3)&X1!=X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_zfmisc_1)).
% 26.37/26.59  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 26.37/26.59  fof(t45_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_enumset1)).
% 26.37/26.59  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 26.37/26.59  fof(d7_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8, X9, X10]:(X10=k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)<=>![X11]:(r2_hidden(X11,X10)<=>~(((((((((X11!=X1&X11!=X2)&X11!=X3)&X11!=X4)&X11!=X5)&X11!=X6)&X11!=X7)&X11!=X8)&X11!=X9)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_enumset1)).
% 26.37/26.59  fof(c_0_19, plain, ![X23, X24]:r1_xboole_0(k3_xboole_0(X23,X24),k5_xboole_0(X23,X24)), inference(variable_rename,[status(thm)],[l97_xboole_1])).
% 26.37/26.59  fof(c_0_20, plain, ![X12]:k3_xboole_0(X12,X12)=X12, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).
% 26.37/26.59  fof(c_0_21, plain, ![X21, X22]:((k4_xboole_0(X21,X22)!=k1_xboole_0|r1_tarski(X21,X22))&(~r1_tarski(X21,X22)|k4_xboole_0(X21,X22)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 26.37/26.59  fof(c_0_22, plain, ![X25, X26]:k4_xboole_0(X25,X26)=k5_xboole_0(X25,k3_xboole_0(X25,X26)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 26.37/26.59  fof(c_0_23, plain, ![X19, X20]:(((r1_tarski(X19,X20)|X19!=X20)&(r1_tarski(X20,X19)|X19!=X20))&(~r1_tarski(X19,X20)|~r1_tarski(X20,X19)|X19=X20)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 26.37/26.59  fof(c_0_24, plain, ![X13, X14, X16, X17, X18]:((r1_xboole_0(X13,X14)|r2_hidden(esk1_2(X13,X14),k3_xboole_0(X13,X14)))&(~r2_hidden(X18,k3_xboole_0(X16,X17))|~r1_xboole_0(X16,X17))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 26.37/26.59  cnf(c_0_25, plain, (r1_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 26.37/26.59  cnf(c_0_26, plain, (k3_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_20])).
% 26.37/26.59  cnf(c_0_27, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 26.37/26.59  cnf(c_0_28, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 26.37/26.59  cnf(c_0_29, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_23])).
% 26.37/26.59  cnf(c_0_30, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 26.37/26.59  cnf(c_0_31, plain, (r1_xboole_0(X1,k5_xboole_0(X1,X1))), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 26.37/26.59  cnf(c_0_32, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X2))=k1_xboole_0|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_27, c_0_28])).
% 26.37/26.59  cnf(c_0_33, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_29])).
% 26.37/26.59  fof(c_0_34, plain, ![X29, X30]:((~r1_xboole_0(X29,X30)|k4_xboole_0(X29,X30)=X29)&(k4_xboole_0(X29,X30)!=X29|r1_xboole_0(X29,X30))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).
% 26.37/26.59  cnf(c_0_35, plain, (~r2_hidden(X1,k3_xboole_0(X2,k5_xboole_0(X2,X2)))), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 26.37/26.59  cnf(c_0_36, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_26])).
% 26.37/26.59  cnf(c_0_37, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk1_2(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 26.37/26.59  fof(c_0_38, plain, ![X31, X32, X33]:k5_xboole_0(k5_xboole_0(X31,X32),X33)=k5_xboole_0(X31,k5_xboole_0(X32,X33)), inference(variable_rename,[status(thm)],[t91_xboole_1])).
% 26.37/26.59  cnf(c_0_39, plain, (k4_xboole_0(X1,X2)=X1|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 26.37/26.59  cnf(c_0_40, plain, (~r2_hidden(X1,k3_xboole_0(X2,k1_xboole_0))), inference(rw,[status(thm)],[c_0_35, c_0_36])).
% 26.37/26.59  cnf(c_0_41, plain, (r2_hidden(esk1_2(X1,X1),X1)|r1_xboole_0(X1,X1)), inference(spm,[status(thm)],[c_0_37, c_0_26])).
% 26.37/26.59  fof(c_0_42, plain, ![X85, X86, X87, X88, X89, X90, X91, X92]:k6_enumset1(X85,X86,X87,X88,X89,X90,X91,X92)=k2_xboole_0(k1_enumset1(X85,X86,X87),k3_enumset1(X88,X89,X90,X91,X92)), inference(variable_rename,[status(thm)],[t64_enumset1])).
% 26.37/26.59  fof(c_0_43, plain, ![X103, X104, X105]:k2_enumset1(X103,X103,X104,X105)=k1_enumset1(X103,X104,X105), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 26.37/26.59  fof(c_0_44, plain, ![X34, X35]:k2_xboole_0(X34,X35)=k5_xboole_0(k5_xboole_0(X34,X35),k3_xboole_0(X34,X35)), inference(variable_rename,[status(thm)],[t94_xboole_1])).
% 26.37/26.59  fof(c_0_45, plain, ![X106, X107, X108, X109]:k6_enumset1(X106,X106,X106,X106,X106,X107,X108,X109)=k2_enumset1(X106,X107,X108,X109), inference(variable_rename,[status(thm)],[t90_enumset1])).
% 26.37/26.59  fof(c_0_46, plain, ![X68, X69, X70, X71, X72, X73, X74, X75, X76]:k7_enumset1(X68,X69,X70,X71,X72,X73,X74,X75,X76)=k2_xboole_0(k2_enumset1(X68,X69,X70,X71),k3_enumset1(X72,X73,X74,X75,X76)), inference(variable_rename,[status(thm)],[l142_enumset1])).
% 26.37/26.59  cnf(c_0_47, plain, (k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 26.37/26.59  cnf(c_0_48, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X2))=X1|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_39, c_0_28])).
% 26.37/26.59  cnf(c_0_49, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(rw,[status(thm)],[c_0_31, c_0_36])).
% 26.37/26.59  cnf(c_0_50, plain, (r1_xboole_0(k3_xboole_0(X1,k1_xboole_0),k3_xboole_0(X1,k1_xboole_0))), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 26.37/26.59  fof(c_0_51, plain, ![X93, X94, X95, X96, X97, X98, X99, X100]:k6_enumset1(X93,X94,X95,X96,X97,X98,X99,X100)=k2_xboole_0(k2_enumset1(X93,X94,X95,X96),k2_enumset1(X97,X98,X99,X100)), inference(variable_rename,[status(thm)],[t65_enumset1])).
% 26.37/26.59  cnf(c_0_52, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k1_enumset1(X1,X2,X3),k3_enumset1(X4,X5,X6,X7,X8))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 26.37/26.59  cnf(c_0_53, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 26.37/26.59  cnf(c_0_54, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 26.37/26.59  cnf(c_0_55, plain, (k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 26.37/26.59  cnf(c_0_56, plain, (k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k3_enumset1(X5,X6,X7,X8,X9))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 26.37/26.59  fof(c_0_57, negated_conjecture, ~(![X1, X2, X3, X4]:~(((r1_tarski(k2_tarski(X1,X2),k2_tarski(X3,X4))&X1!=X3)&X1!=X4))), inference(assume_negation,[status(cth)],[t28_zfmisc_1])).
% 26.37/26.59  cnf(c_0_58, plain, (k5_xboole_0(X1,k5_xboole_0(X1,X2))=k5_xboole_0(k1_xboole_0,X2)), inference(spm,[status(thm)],[c_0_47, c_0_36])).
% 26.37/26.59  cnf(c_0_59, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0))=X1), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 26.37/26.59  cnf(c_0_60, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_50]), c_0_26]), c_0_36])).
% 26.37/26.59  cnf(c_0_61, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8))), inference(split_conjunct,[status(thm)],[c_0_51])).
% 26.37/26.59  cnf(c_0_62, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k5_xboole_0(k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3),k3_enumset1(X4,X5,X6,X7,X8)),k3_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3),k3_enumset1(X4,X5,X6,X7,X8)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52, c_0_53]), c_0_54]), c_0_55]), c_0_55])).
% 26.37/26.59  cnf(c_0_63, plain, (k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k5_xboole_0(k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4),k3_enumset1(X5,X6,X7,X8,X9)),k3_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4),k3_enumset1(X5,X6,X7,X8,X9)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56, c_0_54]), c_0_55]), c_0_55])).
% 26.37/26.59  fof(c_0_64, negated_conjecture, ((r1_tarski(k2_tarski(esk4_0,esk5_0),k2_tarski(esk6_0,esk7_0))&esk4_0!=esk6_0)&esk4_0!=esk7_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_57])])])).
% 26.37/26.59  fof(c_0_65, plain, ![X101, X102]:k1_enumset1(X101,X101,X102)=k2_tarski(X101,X102), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 26.37/26.59  cnf(c_0_66, plain, (k5_xboole_0(X1,k1_xboole_0)=k5_xboole_0(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_58, c_0_36])).
% 26.37/26.59  cnf(c_0_67, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[c_0_59, c_0_60])).
% 26.37/26.59  fof(c_0_68, plain, ![X81, X82, X83, X84]:k2_enumset1(X81,X82,X83,X84)=k2_xboole_0(k2_tarski(X81,X82),k2_tarski(X83,X84)), inference(variable_rename,[status(thm)],[t45_enumset1])).
% 26.37/26.59  cnf(c_0_69, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k5_xboole_0(k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4),k6_enumset1(X5,X5,X5,X5,X5,X6,X7,X8)),k3_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4),k6_enumset1(X5,X5,X5,X5,X5,X6,X7,X8)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61, c_0_54]), c_0_55]), c_0_55]), c_0_55]), c_0_55])).
% 26.37/26.59  cnf(c_0_70, plain, (k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3),k5_xboole_0(k3_enumset1(X4,X5,X6,X7,X8),k3_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3),k3_enumset1(X4,X5,X6,X7,X8))))=k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)), inference(rw,[status(thm)],[c_0_62, c_0_47])).
% 26.37/26.59  cnf(c_0_71, plain, (k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4),k5_xboole_0(k3_enumset1(X5,X6,X7,X8,X9),k3_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4),k3_enumset1(X5,X6,X7,X8,X9))))=k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)), inference(rw,[status(thm)],[c_0_63, c_0_47])).
% 26.37/26.59  cnf(c_0_72, negated_conjecture, (r1_tarski(k2_tarski(esk4_0,esk5_0),k2_tarski(esk6_0,esk7_0))), inference(split_conjunct,[status(thm)],[c_0_64])).
% 26.37/26.59  cnf(c_0_73, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_65])).
% 26.37/26.59  cnf(c_0_74, plain, (k5_xboole_0(k1_xboole_0,X1)=X1), inference(rw,[status(thm)],[c_0_66, c_0_67])).
% 26.37/26.59  cnf(c_0_75, plain, (k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4))), inference(split_conjunct,[status(thm)],[c_0_68])).
% 26.37/26.59  cnf(c_0_76, plain, (k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4),k5_xboole_0(k6_enumset1(X5,X5,X5,X5,X5,X6,X7,X8),k3_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4),k6_enumset1(X5,X5,X5,X5,X5,X6,X7,X8))))=k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)), inference(rw,[status(thm)],[c_0_69, c_0_47])).
% 26.37/26.59  cnf(c_0_77, plain, (k7_enumset1(X1,X1,X2,X3,X4,X5,X6,X7,X8)=k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)), inference(rw,[status(thm)],[c_0_70, c_0_71])).
% 26.37/26.59  fof(c_0_78, plain, ![X27, X28]:(~r1_tarski(X27,X28)|k3_xboole_0(X27,X28)=X27), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 26.37/26.59  cnf(c_0_79, negated_conjecture, (r1_tarski(k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk7_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_72, c_0_73]), c_0_73]), c_0_53]), c_0_53]), c_0_55]), c_0_55])).
% 26.37/26.59  cnf(c_0_80, plain, (k5_xboole_0(X1,k5_xboole_0(X1,X2))=X2), inference(rw,[status(thm)],[c_0_58, c_0_74])).
% 26.37/26.59  cnf(c_0_81, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,X2)))=k1_xboole_0), inference(spm,[status(thm)],[c_0_47, c_0_36])).
% 26.37/26.59  cnf(c_0_82, plain, (k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4)=k5_xboole_0(k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2),k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X4)),k3_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2),k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X4)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_75, c_0_73]), c_0_73]), c_0_53]), c_0_53]), c_0_54]), c_0_55]), c_0_55]), c_0_55]), c_0_55]), c_0_55])).
% 26.37/26.59  fof(c_0_83, plain, ![X45, X46, X47, X48, X49, X50, X51, X52, X53, X54, X55, X56, X57, X58, X59, X60, X61, X62, X63, X64, X65, X66]:(((~r2_hidden(X55,X54)|(X55=X45|X55=X46|X55=X47|X55=X48|X55=X49|X55=X50|X55=X51|X55=X52|X55=X53)|X54!=k7_enumset1(X45,X46,X47,X48,X49,X50,X51,X52,X53))&(((((((((X56!=X45|r2_hidden(X56,X54)|X54!=k7_enumset1(X45,X46,X47,X48,X49,X50,X51,X52,X53))&(X56!=X46|r2_hidden(X56,X54)|X54!=k7_enumset1(X45,X46,X47,X48,X49,X50,X51,X52,X53)))&(X56!=X47|r2_hidden(X56,X54)|X54!=k7_enumset1(X45,X46,X47,X48,X49,X50,X51,X52,X53)))&(X56!=X48|r2_hidden(X56,X54)|X54!=k7_enumset1(X45,X46,X47,X48,X49,X50,X51,X52,X53)))&(X56!=X49|r2_hidden(X56,X54)|X54!=k7_enumset1(X45,X46,X47,X48,X49,X50,X51,X52,X53)))&(X56!=X50|r2_hidden(X56,X54)|X54!=k7_enumset1(X45,X46,X47,X48,X49,X50,X51,X52,X53)))&(X56!=X51|r2_hidden(X56,X54)|X54!=k7_enumset1(X45,X46,X47,X48,X49,X50,X51,X52,X53)))&(X56!=X52|r2_hidden(X56,X54)|X54!=k7_enumset1(X45,X46,X47,X48,X49,X50,X51,X52,X53)))&(X56!=X53|r2_hidden(X56,X54)|X54!=k7_enumset1(X45,X46,X47,X48,X49,X50,X51,X52,X53))))&((((((((((esk3_10(X57,X58,X59,X60,X61,X62,X63,X64,X65,X66)!=X57|~r2_hidden(esk3_10(X57,X58,X59,X60,X61,X62,X63,X64,X65,X66),X66)|X66=k7_enumset1(X57,X58,X59,X60,X61,X62,X63,X64,X65))&(esk3_10(X57,X58,X59,X60,X61,X62,X63,X64,X65,X66)!=X58|~r2_hidden(esk3_10(X57,X58,X59,X60,X61,X62,X63,X64,X65,X66),X66)|X66=k7_enumset1(X57,X58,X59,X60,X61,X62,X63,X64,X65)))&(esk3_10(X57,X58,X59,X60,X61,X62,X63,X64,X65,X66)!=X59|~r2_hidden(esk3_10(X57,X58,X59,X60,X61,X62,X63,X64,X65,X66),X66)|X66=k7_enumset1(X57,X58,X59,X60,X61,X62,X63,X64,X65)))&(esk3_10(X57,X58,X59,X60,X61,X62,X63,X64,X65,X66)!=X60|~r2_hidden(esk3_10(X57,X58,X59,X60,X61,X62,X63,X64,X65,X66),X66)|X66=k7_enumset1(X57,X58,X59,X60,X61,X62,X63,X64,X65)))&(esk3_10(X57,X58,X59,X60,X61,X62,X63,X64,X65,X66)!=X61|~r2_hidden(esk3_10(X57,X58,X59,X60,X61,X62,X63,X64,X65,X66),X66)|X66=k7_enumset1(X57,X58,X59,X60,X61,X62,X63,X64,X65)))&(esk3_10(X57,X58,X59,X60,X61,X62,X63,X64,X65,X66)!=X62|~r2_hidden(esk3_10(X57,X58,X59,X60,X61,X62,X63,X64,X65,X66),X66)|X66=k7_enumset1(X57,X58,X59,X60,X61,X62,X63,X64,X65)))&(esk3_10(X57,X58,X59,X60,X61,X62,X63,X64,X65,X66)!=X63|~r2_hidden(esk3_10(X57,X58,X59,X60,X61,X62,X63,X64,X65,X66),X66)|X66=k7_enumset1(X57,X58,X59,X60,X61,X62,X63,X64,X65)))&(esk3_10(X57,X58,X59,X60,X61,X62,X63,X64,X65,X66)!=X64|~r2_hidden(esk3_10(X57,X58,X59,X60,X61,X62,X63,X64,X65,X66),X66)|X66=k7_enumset1(X57,X58,X59,X60,X61,X62,X63,X64,X65)))&(esk3_10(X57,X58,X59,X60,X61,X62,X63,X64,X65,X66)!=X65|~r2_hidden(esk3_10(X57,X58,X59,X60,X61,X62,X63,X64,X65,X66),X66)|X66=k7_enumset1(X57,X58,X59,X60,X61,X62,X63,X64,X65)))&(r2_hidden(esk3_10(X57,X58,X59,X60,X61,X62,X63,X64,X65,X66),X66)|(esk3_10(X57,X58,X59,X60,X61,X62,X63,X64,X65,X66)=X57|esk3_10(X57,X58,X59,X60,X61,X62,X63,X64,X65,X66)=X58|esk3_10(X57,X58,X59,X60,X61,X62,X63,X64,X65,X66)=X59|esk3_10(X57,X58,X59,X60,X61,X62,X63,X64,X65,X66)=X60|esk3_10(X57,X58,X59,X60,X61,X62,X63,X64,X65,X66)=X61|esk3_10(X57,X58,X59,X60,X61,X62,X63,X64,X65,X66)=X62|esk3_10(X57,X58,X59,X60,X61,X62,X63,X64,X65,X66)=X63|esk3_10(X57,X58,X59,X60,X61,X62,X63,X64,X65,X66)=X64|esk3_10(X57,X58,X59,X60,X61,X62,X63,X64,X65,X66)=X65)|X66=k7_enumset1(X57,X58,X59,X60,X61,X62,X63,X64,X65)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_enumset1])])])])])])).
% 26.37/26.59  cnf(c_0_84, plain, (k5_xboole_0(k7_enumset1(X1,X1,X1,X1,X1,X1,X2,X3,X4),k5_xboole_0(k6_enumset1(X5,X5,X5,X5,X5,X6,X7,X8),k3_xboole_0(k7_enumset1(X1,X1,X1,X1,X1,X1,X2,X3,X4),k6_enumset1(X5,X5,X5,X5,X5,X6,X7,X8))))=k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)), inference(spm,[status(thm)],[c_0_76, c_0_77])).
% 26.37/26.59  cnf(c_0_85, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_78])).
% 26.37/26.59  cnf(c_0_86, negated_conjecture, (r1_tarski(k7_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),k7_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk7_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_79, c_0_77]), c_0_77])).
% 26.37/26.59  cnf(c_0_87, plain, (k5_xboole_0(X1,k5_xboole_0(X2,X1))=X2), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_81]), c_0_67])).
% 26.37/26.59  cnf(c_0_88, plain, (k6_enumset1(X1,X1,X1,X2,X3,X3,X3,X4)=k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_82, c_0_47]), c_0_76])).
% 26.37/26.59  cnf(c_0_89, plain, (X1=X3|X1=X4|X1=X5|X1=X6|X1=X7|X1=X8|X1=X9|X1=X10|X1=X11|~r2_hidden(X1,X2)|X2!=k7_enumset1(X3,X4,X5,X6,X7,X8,X9,X10,X11)), inference(split_conjunct,[status(thm)],[c_0_83])).
% 26.37/26.59  cnf(c_0_90, plain, (k5_xboole_0(k7_enumset1(X1,X1,X1,X1,X1,X1,X2,X3,X4),k5_xboole_0(k7_enumset1(X5,X5,X5,X5,X5,X5,X6,X7,X8),k3_xboole_0(k7_enumset1(X1,X1,X1,X1,X1,X1,X2,X3,X4),k7_enumset1(X5,X5,X5,X5,X5,X5,X6,X7,X8))))=k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)), inference(spm,[status(thm)],[c_0_84, c_0_77])).
% 26.37/26.59  cnf(c_0_91, negated_conjecture, (k3_xboole_0(k7_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),k7_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk7_0))=k7_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_85, c_0_86])).
% 26.37/26.59  cnf(c_0_92, plain, (k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_80, c_0_87])).
% 26.37/26.59  cnf(c_0_93, plain, (k7_enumset1(X1,X1,X1,X1,X2,X3,X3,X3,X4)=k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4)), inference(spm,[status(thm)],[c_0_77, c_0_88])).
% 26.37/26.59  cnf(c_0_94, plain, (X1=X2|X1=X3|X1=X4|X1=X5|X1=X6|X1=X7|X1=X8|X1=X9|X1=X10|~r2_hidden(X1,k7_enumset1(X10,X9,X8,X7,X6,X5,X4,X3,X2))), inference(er,[status(thm)],[c_0_89])).
% 26.37/26.59  cnf(c_0_95, negated_conjecture, (k7_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk7_0)=k7_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk5_0,esk6_0,esk6_0,esk6_0,esk7_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_91]), c_0_92]), c_0_80]), c_0_88]), c_0_93])).
% 26.37/26.59  cnf(c_0_96, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k7_enumset1(X2,X4,X5,X6,X7,X8,X9,X10,X11)), inference(split_conjunct,[status(thm)],[c_0_83])).
% 26.37/26.59  cnf(c_0_97, negated_conjecture, (X1=esk7_0|X1=esk6_0|~r2_hidden(X1,k7_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk5_0,esk6_0,esk6_0,esk6_0,esk7_0))), inference(spm,[status(thm)],[c_0_94, c_0_95])).
% 26.37/26.59  cnf(c_0_98, plain, (r2_hidden(X1,k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_96])])).
% 26.37/26.59  cnf(c_0_99, negated_conjecture, (esk4_0!=esk7_0), inference(split_conjunct,[status(thm)],[c_0_64])).
% 26.37/26.59  cnf(c_0_100, negated_conjecture, (esk4_0!=esk6_0), inference(split_conjunct,[status(thm)],[c_0_64])).
% 26.37/26.59  cnf(c_0_101, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_97, c_0_98]), c_0_99]), c_0_100]), ['proof']).
% 26.37/26.59  # SZS output end CNFRefutation
% 26.37/26.59  # Proof object total steps             : 102
% 26.37/26.59  # Proof object clause steps            : 63
% 26.37/26.59  # Proof object formula steps           : 39
% 26.37/26.59  # Proof object conjectures             : 12
% 26.37/26.59  # Proof object clause conjectures      : 9
% 26.37/26.59  # Proof object formula conjectures     : 3
% 26.37/26.59  # Proof object initial clauses used    : 23
% 26.37/26.59  # Proof object initial formulas used   : 19
% 26.37/26.59  # Proof object generating inferences   : 19
% 26.37/26.59  # Proof object simplifying inferences  : 57
% 26.37/26.59  # Training examples: 0 positive, 0 negative
% 26.37/26.59  # Parsed axioms                        : 21
% 26.37/26.59  # Removed by relevancy pruning/SinE    : 0
% 26.37/26.59  # Initial clauses                      : 52
% 26.37/26.59  # Removed in clause preprocessing      : 5
% 26.37/26.59  # Initial clauses in saturation        : 47
% 26.37/26.59  # Processed clauses                    : 18344
% 26.37/26.59  # ...of these trivial                  : 947
% 26.37/26.59  # ...subsumed                          : 15832
% 26.37/26.59  # ...remaining for further processing  : 1565
% 26.37/26.59  # Other redundant clauses eliminated   : 4195
% 26.37/26.59  # Clauses deleted for lack of memory   : 0
% 26.37/26.59  # Backward-subsumed                    : 5
% 26.37/26.59  # Backward-rewritten                   : 139
% 26.37/26.59  # Generated clauses                    : 965187
% 26.37/26.59  # ...of the previous two non-trivial   : 931899
% 26.37/26.59  # Contextual simplify-reflections      : 0
% 26.37/26.59  # Paramodulations                      : 959097
% 26.37/26.59  # Factorizations                       : 1905
% 26.37/26.59  # Equation resolutions                 : 4196
% 26.37/26.59  # Propositional unsat checks           : 0
% 26.37/26.59  #    Propositional check models        : 0
% 26.37/26.59  #    Propositional check unsatisfiable : 0
% 26.37/26.59  #    Propositional clauses             : 0
% 26.37/26.59  #    Propositional clauses after purity: 0
% 26.37/26.59  #    Propositional unsat core size     : 0
% 26.37/26.59  #    Propositional preprocessing time  : 0.000
% 26.37/26.59  #    Propositional encoding time       : 0.000
% 26.37/26.59  #    Propositional solver time         : 0.000
% 26.37/26.59  #    Success case prop preproc time    : 0.000
% 26.37/26.59  #    Success case prop encoding time   : 0.000
% 26.37/26.59  #    Success case prop solver time     : 0.000
% 26.37/26.59  # Current number of processed clauses  : 1359
% 26.37/26.59  #    Positive orientable unit clauses  : 501
% 26.37/26.59  #    Positive unorientable unit clauses: 73
% 26.37/26.59  #    Negative unit clauses             : 301
% 26.37/26.59  #    Non-unit-clauses                  : 484
% 26.37/26.59  # Current number of unprocessed clauses: 911757
% 26.37/26.59  # ...number of literals in the above   : 4521827
% 26.37/26.59  # Current number of archived formulas  : 0
% 26.37/26.59  # Current number of archived clauses   : 195
% 26.37/26.59  # Clause-clause subsumption calls (NU) : 70425
% 26.37/26.59  # Rec. Clause-clause subsumption calls : 37566
% 26.37/26.59  # Non-unit clause-clause subsumptions  : 2427
% 26.37/26.59  # Unit Clause-clause subsumption calls : 89348
% 26.37/26.59  # Rewrite failures with RHS unbound    : 0
% 26.37/26.59  # BW rewrite match attempts            : 12418
% 26.37/26.59  # BW rewrite match successes           : 1606
% 26.37/26.59  # Condensation attempts                : 0
% 26.37/26.59  # Condensation successes               : 0
% 26.37/26.59  # Termbank termtop insertions          : 25748001
% 26.44/26.64  
% 26.44/26.64  # -------------------------------------------------
% 26.44/26.64  # User time                : 25.763 s
% 26.44/26.64  # System time              : 0.542 s
% 26.44/26.64  # Total time               : 26.305 s
% 26.44/26.64  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------
