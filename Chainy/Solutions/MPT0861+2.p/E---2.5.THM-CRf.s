%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0861+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:55 EST 2020

% Result     : Theorem 1.73s
% Output     : CNFRefutation 1.73s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 403 expanded)
%              Number of clauses        :   32 ( 150 expanded)
%              Number of leaves         :   17 ( 123 expanded)
%              Depth                    :   10
%              Number of atoms          :  115 ( 548 expanded)
%              Number of equality atoms :   62 ( 409 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    7 (   1 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t17_mcart_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(X1,k2_zfmisc_1(k2_tarski(X2,X3),k1_tarski(X4)))
     => ( ( k1_mcart_1(X1) = X2
          | k1_mcart_1(X1) = X3 )
        & k2_mcart_1(X1) = X4 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_mcart_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT003+2.ax',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT003+2.ax',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT003+2.ax',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT003+2.ax',t72_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT003+2.ax',t73_enumset1)).

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT003+2.ax',t74_enumset1)).

fof(t75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT003+2.ax',t75_enumset1)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT006+2.ax',t12_setfam_1)).

fof(t10_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k2_zfmisc_1(X2,X3))
     => ( r2_hidden(k1_mcart_1(X1),X2)
        & r2_hidden(k2_mcart_1(X1),X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

fof(t31_zfmisc_1,axiom,(
    ! [X1] : k3_tarski(k1_tarski(X1)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT004+2.ax',t31_zfmisc_1)).

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',idempotence_k3_xboole_0)).

fof(l49_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => r1_tarski(X1,k3_tarski(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT004+2.ax',l49_zfmisc_1)).

fof(t4_setfam_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => r1_tarski(k1_setfam_1(X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT006+2.ax',t4_setfam_1)).

fof(t60_xboole_1,axiom,(
    ! [X1,X2] :
      ~ ( r1_tarski(X1,X2)
        & r2_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT002+2.ax',t60_xboole_1)).

fof(d8_xboole_0,axiom,(
    ! [X1,X2] :
      ( r2_xboole_0(X1,X2)
    <=> ( r1_tarski(X1,X2)
        & X1 != X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',d8_xboole_0)).

fof(t15_mcart_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(X1,k2_zfmisc_1(k2_tarski(X2,X3),X4))
     => ( ( k1_mcart_1(X1) = X2
          | k1_mcart_1(X1) = X3 )
        & r2_hidden(k2_mcart_1(X1),X4) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_mcart_1)).

fof(c_0_17,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( r2_hidden(X1,k2_zfmisc_1(k2_tarski(X2,X3),k1_tarski(X4)))
       => ( ( k1_mcart_1(X1) = X2
            | k1_mcart_1(X1) = X3 )
          & k2_mcart_1(X1) = X4 ) ) ),
    inference(assume_negation,[status(cth)],[t17_mcart_1])).

fof(c_0_18,negated_conjecture,
    ( r2_hidden(esk1_0,k2_zfmisc_1(k2_tarski(esk2_0,esk3_0),k1_tarski(esk4_0)))
    & ( k1_mcart_1(esk1_0) != esk2_0
      | k2_mcart_1(esk1_0) != esk4_0 )
    & ( k1_mcart_1(esk1_0) != esk3_0
      | k2_mcart_1(esk1_0) != esk4_0 ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])])).

fof(c_0_19,plain,(
    ! [X743] : k2_tarski(X743,X743) = k1_tarski(X743) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_20,plain,(
    ! [X950,X951] : k1_enumset1(X950,X950,X951) = k2_tarski(X950,X951) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_21,plain,(
    ! [X2477,X2478,X2479] : k2_enumset1(X2477,X2477,X2478,X2479) = k1_enumset1(X2477,X2478,X2479) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_22,plain,(
    ! [X2480,X2481,X2482,X2483] : k3_enumset1(X2480,X2480,X2481,X2482,X2483) = k2_enumset1(X2480,X2481,X2482,X2483) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_23,plain,(
    ! [X2815,X2816,X2817,X2818,X2819] : k4_enumset1(X2815,X2815,X2816,X2817,X2818,X2819) = k3_enumset1(X2815,X2816,X2817,X2818,X2819) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_24,plain,(
    ! [X2866,X2867,X2868,X2869,X2870,X2871] : k5_enumset1(X2866,X2866,X2867,X2868,X2869,X2870,X2871) = k4_enumset1(X2866,X2867,X2868,X2869,X2870,X2871) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_25,plain,(
    ! [X2937,X2938,X2939,X2940,X2941,X2942,X2943] : k6_enumset1(X2937,X2937,X2938,X2939,X2940,X2941,X2942,X2943) = k5_enumset1(X2937,X2938,X2939,X2940,X2941,X2942,X2943) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_26,plain,(
    ! [X982,X983] : k1_setfam_1(k2_tarski(X982,X983)) = k3_xboole_0(X982,X983) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_27,plain,(
    ! [X26,X27,X28] :
      ( ( r2_hidden(k1_mcart_1(X26),X27)
        | ~ r2_hidden(X26,k2_zfmisc_1(X27,X28)) )
      & ( r2_hidden(k2_mcart_1(X26),X28)
        | ~ r2_hidden(X26,k2_zfmisc_1(X27,X28)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_mcart_1])])])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(esk1_0,k2_zfmisc_1(k2_tarski(esk2_0,esk3_0),k1_tarski(esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_29,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_30,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_31,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_32,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_33,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_34,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_35,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_36,plain,(
    ! [X795] : k3_tarski(k1_tarski(X795)) = X795 ),
    inference(variable_rename,[status(thm)],[t31_zfmisc_1])).

fof(c_0_37,plain,(
    ! [X1623] : k3_xboole_0(X1623,X1623) = X1623 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

cnf(c_0_38,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_39,plain,(
    ! [X2747,X2748] :
      ( ~ r2_hidden(X2747,X2748)
      | r1_tarski(X2747,k3_tarski(X2748)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l49_zfmisc_1])])).

cnf(c_0_40,plain,
    ( r2_hidden(k2_mcart_1(X1),X2)
    | ~ r2_hidden(X1,k2_zfmisc_1(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(esk1_0,k2_zfmisc_1(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0),k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_29]),c_0_30]),c_0_30]),c_0_31]),c_0_31]),c_0_32]),c_0_32]),c_0_33]),c_0_33]),c_0_34]),c_0_34]),c_0_35]),c_0_35])).

cnf(c_0_42,plain,
    ( k3_tarski(k1_tarski(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

fof(c_0_43,plain,(
    ! [X3051,X3052] :
      ( ~ r2_hidden(X3051,X3052)
      | r1_tarski(k1_setfam_1(X3052),X3051) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_setfam_1])])).

cnf(c_0_44,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_45,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_38,c_0_30])).

fof(c_0_46,plain,(
    ! [X3195,X3196] :
      ( ~ r1_tarski(X3195,X3196)
      | ~ r2_xboole_0(X3196,X3195) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t60_xboole_1])])).

cnf(c_0_47,plain,
    ( r1_tarski(X1,k3_tarski(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_48,negated_conjecture,
    ( r2_hidden(k2_mcart_1(esk1_0),k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_49,plain,
    ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_29]),c_0_30]),c_0_31]),c_0_32]),c_0_33]),c_0_34]),c_0_35])).

fof(c_0_50,plain,(
    ! [X3172,X3173] :
      ( ( r1_tarski(X3172,X3173)
        | ~ r2_xboole_0(X3172,X3173) )
      & ( X3172 != X3173
        | ~ r2_xboole_0(X3172,X3173) )
      & ( ~ r1_tarski(X3172,X3173)
        | X3172 = X3173
        | r2_xboole_0(X3172,X3173) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_xboole_0])])])).

cnf(c_0_51,plain,
    ( r1_tarski(k1_setfam_1(X2),X1)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_52,plain,
    ( k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44,c_0_45]),c_0_31]),c_0_32]),c_0_33]),c_0_34]),c_0_35])).

cnf(c_0_53,plain,
    ( ~ r1_tarski(X1,X2)
    | ~ r2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_54,negated_conjecture,
    ( r1_tarski(k2_mcart_1(esk1_0),esk4_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_49])).

fof(c_0_55,plain,(
    ! [X43,X44,X45,X46] :
      ( ( k1_mcart_1(X43) = X44
        | k1_mcart_1(X43) = X45
        | ~ r2_hidden(X43,k2_zfmisc_1(k2_tarski(X44,X45),X46)) )
      & ( r2_hidden(k2_mcart_1(X43),X46)
        | ~ r2_hidden(X43,k2_zfmisc_1(k2_tarski(X44,X45),X46)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t15_mcart_1])])])).

cnf(c_0_56,plain,
    ( X1 = X2
    | r2_xboole_0(X1,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_57,negated_conjecture,
    ( r1_tarski(esk4_0,k2_mcart_1(esk1_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_48]),c_0_52])).

cnf(c_0_58,negated_conjecture,
    ( ~ r2_xboole_0(esk4_0,k2_mcart_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_59,plain,
    ( k1_mcart_1(X1) = X2
    | k1_mcart_1(X1) = X3
    | ~ r2_hidden(X1,k2_zfmisc_1(k2_tarski(X2,X3),X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_60,negated_conjecture,
    ( k1_mcart_1(esk1_0) != esk3_0
    | k2_mcart_1(esk1_0) != esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_61,negated_conjecture,
    ( k2_mcart_1(esk1_0) = esk4_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_58])).

cnf(c_0_62,negated_conjecture,
    ( k1_mcart_1(esk1_0) != esk2_0
    | k2_mcart_1(esk1_0) != esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_63,plain,
    ( k1_mcart_1(X1) = X3
    | k1_mcart_1(X1) = X2
    | ~ r2_hidden(X1,k2_zfmisc_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3),X4)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59,c_0_30]),c_0_31]),c_0_32]),c_0_33]),c_0_34]),c_0_35])).

cnf(c_0_64,negated_conjecture,
    ( k1_mcart_1(esk1_0) != esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_60,c_0_61])])).

cnf(c_0_65,negated_conjecture,
    ( k1_mcart_1(esk1_0) != esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_62,c_0_61])])).

cnf(c_0_66,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_41]),c_0_64]),c_0_65]),
    [proof]).
%------------------------------------------------------------------------------
