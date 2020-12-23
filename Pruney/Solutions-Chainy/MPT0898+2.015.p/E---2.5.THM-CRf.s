%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:00:03 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  116 (2536 expanded)
%              Number of clauses        :   71 (1221 expanded)
%              Number of leaves         :   22 ( 641 expanded)
%              Depth                    :   16
%              Number of atoms          :  227 (4321 expanded)
%              Number of equality atoms :  140 (3919 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t58_mcart_1,conjecture,(
    ! [X1,X2] :
      ( k4_zfmisc_1(X1,X1,X1,X1) = k4_zfmisc_1(X2,X2,X2,X2)
     => X1 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_mcart_1)).

fof(d4_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] : k4_zfmisc_1(X1,X2,X3,X4) = k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_zfmisc_1)).

fof(t53_mcart_1,axiom,(
    ! [X1,X2,X3,X4] : k4_zfmisc_1(X1,X2,X3,X4) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_mcart_1)).

fof(t54_mcart_1,axiom,(
    ! [X1,X2,X3,X4] : k3_zfmisc_1(k2_zfmisc_1(X1,X2),X3,X4) = k4_zfmisc_1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_mcart_1)).

fof(t138_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))
     => ( k2_zfmisc_1(X1,X2) = k1_xboole_0
        | ( r1_tarski(X1,X3)
          & r1_tarski(X2,X4) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_zfmisc_1)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(t60_xboole_1,axiom,(
    ! [X1,X2] :
      ~ ( r1_tarski(X1,X2)
        & r2_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_xboole_1)).

fof(d8_xboole_0,axiom,(
    ! [X1,X2] :
      ( r2_xboole_0(X1,X2)
    <=> ( r1_tarski(X1,X2)
        & X1 != X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

fof(t35_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ( ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0 )
    <=> k3_zfmisc_1(X1,X2,X3) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_mcart_1)).

fof(t127_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( r1_xboole_0(X1,X2)
        | r1_xboole_0(X3,X4) )
     => r1_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_zfmisc_1)).

fof(t130_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X1 != k1_xboole_0
     => ( k2_zfmisc_1(k1_tarski(X2),X1) != k1_xboole_0
        & k2_zfmisc_1(X1,k1_tarski(X2)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t130_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t92_enumset1,axiom,(
    ! [X1,X2] : k5_enumset1(X1,X1,X1,X1,X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_enumset1)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(l98_xboole_1,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k4_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l98_xboole_1)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t5_boole,axiom,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(t38_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_tarski(X1,X2),X3)
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(t38_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,k4_xboole_0(X2,X1))
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_xboole_1)).

fof(c_0_22,negated_conjecture,(
    ~ ! [X1,X2] :
        ( k4_zfmisc_1(X1,X1,X1,X1) = k4_zfmisc_1(X2,X2,X2,X2)
       => X1 = X2 ) ),
    inference(assume_negation,[status(cth)],[t58_mcart_1])).

fof(c_0_23,negated_conjecture,
    ( k4_zfmisc_1(esk2_0,esk2_0,esk2_0,esk2_0) = k4_zfmisc_1(esk3_0,esk3_0,esk3_0,esk3_0)
    & esk2_0 != esk3_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_22])])])).

fof(c_0_24,plain,(
    ! [X45,X46,X47,X48] : k4_zfmisc_1(X45,X46,X47,X48) = k2_zfmisc_1(k3_zfmisc_1(X45,X46,X47),X48) ),
    inference(variable_rename,[status(thm)],[d4_zfmisc_1])).

fof(c_0_25,plain,(
    ! [X52,X53,X54,X55] : k4_zfmisc_1(X52,X53,X54,X55) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X52,X53),X54),X55) ),
    inference(variable_rename,[status(thm)],[t53_mcart_1])).

cnf(c_0_26,negated_conjecture,
    ( k4_zfmisc_1(esk2_0,esk2_0,esk2_0,esk2_0) = k4_zfmisc_1(esk3_0,esk3_0,esk3_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_27,plain,
    ( k4_zfmisc_1(X1,X2,X3,X4) = k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_28,plain,
    ( k4_zfmisc_1(X1,X2,X3,X4) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_29,plain,(
    ! [X56,X57,X58,X59] : k3_zfmisc_1(k2_zfmisc_1(X56,X57),X58,X59) = k4_zfmisc_1(X56,X57,X58,X59) ),
    inference(variable_rename,[status(thm)],[t54_mcart_1])).

fof(c_0_30,plain,(
    ! [X38,X39,X40,X41] :
      ( ( r1_tarski(X38,X40)
        | k2_zfmisc_1(X38,X39) = k1_xboole_0
        | ~ r1_tarski(k2_zfmisc_1(X38,X39),k2_zfmisc_1(X40,X41)) )
      & ( r1_tarski(X39,X41)
        | k2_zfmisc_1(X38,X39) = k1_xboole_0
        | ~ r1_tarski(k2_zfmisc_1(X38,X39),k2_zfmisc_1(X40,X41)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t138_zfmisc_1])])])).

cnf(c_0_31,negated_conjecture,
    ( k2_zfmisc_1(k3_zfmisc_1(esk3_0,esk3_0,esk3_0),esk3_0) = k2_zfmisc_1(k3_zfmisc_1(esk2_0,esk2_0,esk2_0),esk2_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_27]),c_0_27])).

cnf(c_0_32,plain,
    ( k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4) ),
    inference(rw,[status(thm)],[c_0_28,c_0_27])).

fof(c_0_33,plain,(
    ! [X18,X19] : r1_tarski(k3_xboole_0(X18,X19),X18) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

fof(c_0_34,plain,(
    ! [X9] : k3_xboole_0(X9,X9) = X9 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

cnf(c_0_35,plain,
    ( k3_zfmisc_1(k2_zfmisc_1(X1,X2),X3,X4) = k4_zfmisc_1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_36,plain,(
    ! [X24,X25] :
      ( ~ r1_tarski(X24,X25)
      | ~ r2_xboole_0(X25,X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t60_xboole_1])])).

fof(c_0_37,plain,(
    ! [X7,X8] :
      ( ( r1_tarski(X7,X8)
        | ~ r2_xboole_0(X7,X8) )
      & ( X7 != X8
        | ~ r2_xboole_0(X7,X8) )
      & ( ~ r1_tarski(X7,X8)
        | X7 = X8
        | r2_xboole_0(X7,X8) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_xboole_0])])])).

cnf(c_0_38,plain,
    ( r1_tarski(X1,X2)
    | k2_zfmisc_1(X3,X1) = k1_xboole_0
    | ~ r1_tarski(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X4,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_39,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0),esk2_0),esk2_0) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0),esk3_0),esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_32]),c_0_32])).

cnf(c_0_40,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_41,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

fof(c_0_42,plain,(
    ! [X49,X50,X51] :
      ( ( X49 = k1_xboole_0
        | X50 = k1_xboole_0
        | X51 = k1_xboole_0
        | k3_zfmisc_1(X49,X50,X51) != k1_xboole_0 )
      & ( X49 != k1_xboole_0
        | k3_zfmisc_1(X49,X50,X51) = k1_xboole_0 )
      & ( X50 != k1_xboole_0
        | k3_zfmisc_1(X49,X50,X51) = k1_xboole_0 )
      & ( X51 != k1_xboole_0
        | k3_zfmisc_1(X49,X50,X51) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_mcart_1])])])).

fof(c_0_43,plain,(
    ! [X32,X33,X34,X35] :
      ( ( ~ r1_xboole_0(X32,X33)
        | r1_xboole_0(k2_zfmisc_1(X32,X34),k2_zfmisc_1(X33,X35)) )
      & ( ~ r1_xboole_0(X34,X35)
        | r1_xboole_0(k2_zfmisc_1(X32,X34),k2_zfmisc_1(X33,X35)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t127_zfmisc_1])])])).

cnf(c_0_44,plain,
    ( k3_zfmisc_1(k2_zfmisc_1(X1,X2),X3,X4) = k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4) ),
    inference(rw,[status(thm)],[c_0_35,c_0_27])).

cnf(c_0_45,plain,
    ( ~ r1_tarski(X1,X2)
    | ~ r2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_46,plain,
    ( X1 = X2
    | r2_xboole_0(X1,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_47,negated_conjecture,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | r1_tarski(X2,esk2_0)
    | ~ r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0),esk3_0),esk3_0)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_48,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_49,plain,
    ( k3_zfmisc_1(X2,X1,X3) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_50,plain,
    ( r1_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X4,X2))
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

fof(c_0_51,plain,(
    ! [X36,X37] :
      ( ( k2_zfmisc_1(k1_tarski(X37),X36) != k1_xboole_0
        | X36 = k1_xboole_0 )
      & ( k2_zfmisc_1(X36,k1_tarski(X37)) != k1_xboole_0
        | X36 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t130_zfmisc_1])])])).

fof(c_0_52,plain,(
    ! [X27] : k2_tarski(X27,X27) = k1_tarski(X27) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_53,plain,(
    ! [X28,X29] : k5_enumset1(X28,X28,X28,X28,X28,X28,X29) = k2_tarski(X28,X29) ),
    inference(variable_rename,[status(thm)],[t92_enumset1])).

cnf(c_0_54,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | k3_zfmisc_1(X1,X2,X3) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_55,plain,
    ( k3_zfmisc_1(k2_zfmisc_1(X1,X2),X3,X4) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4) ),
    inference(rw,[status(thm)],[c_0_44,c_0_32])).

cnf(c_0_56,plain,
    ( X1 = X2
    | ~ r1_tarski(X2,X1)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_57,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0),esk3_0),esk3_0) = k1_xboole_0
    | r1_tarski(esk3_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_58,negated_conjecture,
    ( esk2_0 != esk3_0 ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_59,plain,
    ( k3_zfmisc_1(X1,k1_xboole_0,X2) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_49])).

fof(c_0_60,plain,(
    ! [X5,X6] :
      ( ( ~ r1_xboole_0(X5,X6)
        | k3_xboole_0(X5,X6) = k1_xboole_0 )
      & ( k3_xboole_0(X5,X6) != k1_xboole_0
        | r1_xboole_0(X5,X6) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

cnf(c_0_61,negated_conjecture,
    ( r1_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0),esk3_0),esk3_0))
    | ~ r1_xboole_0(X2,esk2_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_39])).

cnf(c_0_62,plain,
    ( X1 = k1_xboole_0
    | k2_zfmisc_1(X1,k1_tarski(X2)) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_63,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_64,plain,
    ( k5_enumset1(X1,X1,X1,X1,X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_65,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_66,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0),esk3_0),esk3_0) = k1_xboole_0
    | r1_tarski(esk2_0,X1)
    | ~ r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0),esk3_0),esk3_0),k2_zfmisc_1(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_67,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0),esk3_0),esk3_0) = k1_xboole_0
    | ~ r1_tarski(esk2_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_58])).

cnf(c_0_68,plain,
    ( k3_zfmisc_1(X1,X2,X3) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_69,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0),X2),X3) = k2_zfmisc_1(k1_xboole_0,X3) ),
    inference(spm,[status(thm)],[c_0_32,c_0_59])).

cnf(c_0_70,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_71,negated_conjecture,
    ( r1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0),esk3_0),esk3_0),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0),esk3_0),esk3_0))
    | ~ r1_xboole_0(esk2_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_61,c_0_39])).

cnf(c_0_72,plain,
    ( X1 = k1_xboole_0
    | k2_zfmisc_1(X1,k5_enumset1(X2,X2,X2,X2,X2,X2,X2)) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_62,c_0_63]),c_0_64])).

cnf(c_0_73,negated_conjecture,
    ( k2_zfmisc_1(esk2_0,esk2_0) = k1_xboole_0
    | esk2_0 = k1_xboole_0
    | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0),esk3_0),esk3_0) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_65,c_0_39])).

cnf(c_0_74,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0),esk3_0),esk3_0) = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_48]),c_0_67])).

cnf(c_0_75,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),k1_xboole_0),X3) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_59,c_0_55])).

cnf(c_0_76,plain,
    ( k3_zfmisc_1(k1_xboole_0,X1,X2) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_68])).

cnf(c_0_77,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1),X2) = k2_zfmisc_1(k1_xboole_0,X2) ),
    inference(spm,[status(thm)],[c_0_69,c_0_69])).

fof(c_0_78,plain,(
    ! [X16,X17] : k5_xboole_0(X16,X17) = k4_xboole_0(k2_xboole_0(X16,X17),k3_xboole_0(X16,X17)) ),
    inference(variable_rename,[status(thm)],[l98_xboole_1])).

fof(c_0_79,plain,(
    ! [X30,X31] : k3_tarski(k2_tarski(X30,X31)) = k2_xboole_0(X30,X31) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

cnf(c_0_80,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0),esk3_0),esk3_0) = k1_xboole_0
    | ~ r1_xboole_0(esk2_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_41])).

cnf(c_0_81,plain,
    ( r1_xboole_0(X1,X2)
    | k3_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_82,plain,
    ( k3_zfmisc_1(X1,X2,X3) = k1_xboole_0
    | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),k5_enumset1(X4,X4,X4,X4,X4,X4,X4)) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_72,c_0_32])).

cnf(c_0_83,negated_conjecture,
    ( k2_zfmisc_1(esk2_0,esk2_0) = k1_xboole_0
    | esk2_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_73,c_0_74])])).

cnf(c_0_84,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_75]),c_0_76]),c_0_77])).

fof(c_0_85,plain,(
    ! [X23] : k5_xboole_0(X23,k1_xboole_0) = X23 ),
    inference(variable_rename,[status(thm)],[t5_boole])).

cnf(c_0_86,plain,
    ( k5_xboole_0(X1,X2) = k4_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_78])).

cnf(c_0_87,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_79])).

fof(c_0_88,plain,(
    ! [X20] : k2_xboole_0(X20,k1_xboole_0) = X20 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

fof(c_0_89,plain,(
    ! [X42,X43,X44] :
      ( ( r2_hidden(X42,X44)
        | ~ r1_tarski(k2_tarski(X42,X43),X44) )
      & ( r2_hidden(X43,X44)
        | ~ r1_tarski(k2_tarski(X42,X43),X44) )
      & ( ~ r2_hidden(X42,X44)
        | ~ r2_hidden(X43,X44)
        | r1_tarski(k2_tarski(X42,X43),X44) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_zfmisc_1])])])).

cnf(c_0_90,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0),esk3_0),esk3_0) = k1_xboole_0
    | esk2_0 != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_81]),c_0_41])).

cnf(c_0_91,negated_conjecture,
    ( k3_zfmisc_1(esk2_0,esk2_0,X1) = k1_xboole_0
    | esk2_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_84]),c_0_84])])).

cnf(c_0_92,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_85])).

cnf(c_0_93,plain,
    ( k5_xboole_0(X1,X2) = k4_xboole_0(k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X2)),k3_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_86,c_0_87]),c_0_64])).

cnf(c_0_94,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_88])).

fof(c_0_95,plain,(
    ! [X10,X11,X13,X14,X15] :
      ( ( r1_xboole_0(X10,X11)
        | r2_hidden(esk1_2(X10,X11),k3_xboole_0(X10,X11)) )
      & ( ~ r2_hidden(X15,k3_xboole_0(X13,X14))
        | ~ r1_xboole_0(X13,X14) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

cnf(c_0_96,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k2_tarski(X3,X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_89])).

cnf(c_0_97,negated_conjecture,
    ( k2_zfmisc_1(esk3_0,esk3_0) = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | esk2_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_65,c_0_90])).

cnf(c_0_98,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | X1 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_54,c_0_91])).

fof(c_0_99,plain,(
    ! [X21,X22] :
      ( ~ r1_tarski(X21,k4_xboole_0(X22,X21))
      | X21 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_xboole_1])])).

cnf(c_0_100,plain,
    ( k4_xboole_0(k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,k1_xboole_0)),k3_xboole_0(X1,k1_xboole_0)) = X1 ),
    inference(rw,[status(thm)],[c_0_92,c_0_93])).

cnf(c_0_101,plain,
    ( k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,k1_xboole_0)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_94,c_0_87]),c_0_64])).

cnf(c_0_102,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_95])).

cnf(c_0_103,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k5_enumset1(X3,X3,X3,X3,X3,X3,X1),X2) ),
    inference(rw,[status(thm)],[c_0_96,c_0_64])).

cnf(c_0_104,negated_conjecture,
    ( k3_zfmisc_1(esk3_0,esk3_0,X1) = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | esk2_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_97]),c_0_84]),c_0_84])])).

cnf(c_0_105,negated_conjecture,
    ( esk2_0 = k1_xboole_0 ),
    inference(ef,[status(thm)],[c_0_98])).

cnf(c_0_106,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_99])).

cnf(c_0_107,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0)) = X1 ),
    inference(rw,[status(thm)],[c_0_100,c_0_101])).

cnf(c_0_108,plain,
    ( ~ r1_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X2),k3_xboole_0(X3,X4))
    | ~ r1_xboole_0(X3,X4) ),
    inference(spm,[status(thm)],[c_0_102,c_0_103])).

cnf(c_0_109,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | X1 = k1_xboole_0
    | esk2_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_54,c_0_104])).

cnf(c_0_110,negated_conjecture,
    ( esk3_0 != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_58,c_0_105])).

cnf(c_0_111,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_107]),c_0_40])])).

cnf(c_0_112,plain,
    ( k3_xboole_0(X1,X2) != k1_xboole_0
    | ~ r1_tarski(k5_enumset1(X3,X3,X3,X3,X3,X3,X4),k3_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_108,c_0_81])).

cnf(c_0_113,negated_conjecture,
    ( X1 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_109,c_0_105])]),c_0_110])).

cnf(c_0_114,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_111])).

cnf(c_0_115,plain,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_112,c_0_113]),c_0_113]),c_0_113]),c_0_114])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:01:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.19/0.42  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S032I
% 0.19/0.42  # and selection function SelectUnlessUniqMax.
% 0.19/0.42  #
% 0.19/0.42  # Preprocessing time       : 0.029 s
% 0.19/0.42  # Presaturation interreduction done
% 0.19/0.42  
% 0.19/0.42  # Proof found!
% 0.19/0.42  # SZS status Theorem
% 0.19/0.42  # SZS output start CNFRefutation
% 0.19/0.42  fof(t58_mcart_1, conjecture, ![X1, X2]:(k4_zfmisc_1(X1,X1,X1,X1)=k4_zfmisc_1(X2,X2,X2,X2)=>X1=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_mcart_1)).
% 0.19/0.42  fof(d4_zfmisc_1, axiom, ![X1, X2, X3, X4]:k4_zfmisc_1(X1,X2,X3,X4)=k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_zfmisc_1)).
% 0.19/0.42  fof(t53_mcart_1, axiom, ![X1, X2, X3, X4]:k4_zfmisc_1(X1,X2,X3,X4)=k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t53_mcart_1)).
% 0.19/0.42  fof(t54_mcart_1, axiom, ![X1, X2, X3, X4]:k3_zfmisc_1(k2_zfmisc_1(X1,X2),X3,X4)=k4_zfmisc_1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_mcart_1)).
% 0.19/0.42  fof(t138_zfmisc_1, axiom, ![X1, X2, X3, X4]:(r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))=>(k2_zfmisc_1(X1,X2)=k1_xboole_0|(r1_tarski(X1,X3)&r1_tarski(X2,X4)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t138_zfmisc_1)).
% 0.19/0.42  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 0.19/0.42  fof(idempotence_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 0.19/0.42  fof(t60_xboole_1, axiom, ![X1, X2]:~((r1_tarski(X1,X2)&r2_xboole_0(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_xboole_1)).
% 0.19/0.42  fof(d8_xboole_0, axiom, ![X1, X2]:(r2_xboole_0(X1,X2)<=>(r1_tarski(X1,X2)&X1!=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 0.19/0.42  fof(t35_mcart_1, axiom, ![X1, X2, X3]:(((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)<=>k3_zfmisc_1(X1,X2,X3)!=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_mcart_1)).
% 0.19/0.42  fof(t127_zfmisc_1, axiom, ![X1, X2, X3, X4]:((r1_xboole_0(X1,X2)|r1_xboole_0(X3,X4))=>r1_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t127_zfmisc_1)).
% 0.19/0.42  fof(t130_zfmisc_1, axiom, ![X1, X2]:(X1!=k1_xboole_0=>(k2_zfmisc_1(k1_tarski(X2),X1)!=k1_xboole_0&k2_zfmisc_1(X1,k1_tarski(X2))!=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t130_zfmisc_1)).
% 0.19/0.42  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.19/0.42  fof(t92_enumset1, axiom, ![X1, X2]:k5_enumset1(X1,X1,X1,X1,X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_enumset1)).
% 0.19/0.42  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 0.19/0.42  fof(l98_xboole_1, axiom, ![X1, X2]:k5_xboole_0(X1,X2)=k4_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l98_xboole_1)).
% 0.19/0.42  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.19/0.42  fof(t5_boole, axiom, ![X1]:k5_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 0.19/0.42  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 0.19/0.42  fof(t38_zfmisc_1, axiom, ![X1, X2, X3]:(r1_tarski(k2_tarski(X1,X2),X3)<=>(r2_hidden(X1,X3)&r2_hidden(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 0.19/0.42  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 0.19/0.42  fof(t38_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,k4_xboole_0(X2,X1))=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_xboole_1)).
% 0.19/0.42  fof(c_0_22, negated_conjecture, ~(![X1, X2]:(k4_zfmisc_1(X1,X1,X1,X1)=k4_zfmisc_1(X2,X2,X2,X2)=>X1=X2)), inference(assume_negation,[status(cth)],[t58_mcart_1])).
% 0.19/0.42  fof(c_0_23, negated_conjecture, (k4_zfmisc_1(esk2_0,esk2_0,esk2_0,esk2_0)=k4_zfmisc_1(esk3_0,esk3_0,esk3_0,esk3_0)&esk2_0!=esk3_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_22])])])).
% 0.19/0.42  fof(c_0_24, plain, ![X45, X46, X47, X48]:k4_zfmisc_1(X45,X46,X47,X48)=k2_zfmisc_1(k3_zfmisc_1(X45,X46,X47),X48), inference(variable_rename,[status(thm)],[d4_zfmisc_1])).
% 0.19/0.42  fof(c_0_25, plain, ![X52, X53, X54, X55]:k4_zfmisc_1(X52,X53,X54,X55)=k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X52,X53),X54),X55), inference(variable_rename,[status(thm)],[t53_mcart_1])).
% 0.19/0.42  cnf(c_0_26, negated_conjecture, (k4_zfmisc_1(esk2_0,esk2_0,esk2_0,esk2_0)=k4_zfmisc_1(esk3_0,esk3_0,esk3_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.42  cnf(c_0_27, plain, (k4_zfmisc_1(X1,X2,X3,X4)=k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.42  cnf(c_0_28, plain, (k4_zfmisc_1(X1,X2,X3,X4)=k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.42  fof(c_0_29, plain, ![X56, X57, X58, X59]:k3_zfmisc_1(k2_zfmisc_1(X56,X57),X58,X59)=k4_zfmisc_1(X56,X57,X58,X59), inference(variable_rename,[status(thm)],[t54_mcart_1])).
% 0.19/0.42  fof(c_0_30, plain, ![X38, X39, X40, X41]:((r1_tarski(X38,X40)|k2_zfmisc_1(X38,X39)=k1_xboole_0|~r1_tarski(k2_zfmisc_1(X38,X39),k2_zfmisc_1(X40,X41)))&(r1_tarski(X39,X41)|k2_zfmisc_1(X38,X39)=k1_xboole_0|~r1_tarski(k2_zfmisc_1(X38,X39),k2_zfmisc_1(X40,X41)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t138_zfmisc_1])])])).
% 0.19/0.42  cnf(c_0_31, negated_conjecture, (k2_zfmisc_1(k3_zfmisc_1(esk3_0,esk3_0,esk3_0),esk3_0)=k2_zfmisc_1(k3_zfmisc_1(esk2_0,esk2_0,esk2_0),esk2_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26, c_0_27]), c_0_27])).
% 0.19/0.42  cnf(c_0_32, plain, (k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4)=k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4)), inference(rw,[status(thm)],[c_0_28, c_0_27])).
% 0.19/0.42  fof(c_0_33, plain, ![X18, X19]:r1_tarski(k3_xboole_0(X18,X19),X18), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 0.19/0.42  fof(c_0_34, plain, ![X9]:k3_xboole_0(X9,X9)=X9, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).
% 0.19/0.42  cnf(c_0_35, plain, (k3_zfmisc_1(k2_zfmisc_1(X1,X2),X3,X4)=k4_zfmisc_1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.42  fof(c_0_36, plain, ![X24, X25]:(~r1_tarski(X24,X25)|~r2_xboole_0(X25,X24)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t60_xboole_1])])).
% 0.19/0.42  fof(c_0_37, plain, ![X7, X8]:(((r1_tarski(X7,X8)|~r2_xboole_0(X7,X8))&(X7!=X8|~r2_xboole_0(X7,X8)))&(~r1_tarski(X7,X8)|X7=X8|r2_xboole_0(X7,X8))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_xboole_0])])])).
% 0.19/0.42  cnf(c_0_38, plain, (r1_tarski(X1,X2)|k2_zfmisc_1(X3,X1)=k1_xboole_0|~r1_tarski(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X4,X2))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.42  cnf(c_0_39, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0),esk2_0),esk2_0)=k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0),esk3_0),esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_32]), c_0_32])).
% 0.19/0.42  cnf(c_0_40, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.42  cnf(c_0_41, plain, (k3_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.19/0.42  fof(c_0_42, plain, ![X49, X50, X51]:((X49=k1_xboole_0|X50=k1_xboole_0|X51=k1_xboole_0|k3_zfmisc_1(X49,X50,X51)!=k1_xboole_0)&(((X49!=k1_xboole_0|k3_zfmisc_1(X49,X50,X51)=k1_xboole_0)&(X50!=k1_xboole_0|k3_zfmisc_1(X49,X50,X51)=k1_xboole_0))&(X51!=k1_xboole_0|k3_zfmisc_1(X49,X50,X51)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_mcart_1])])])).
% 0.19/0.42  fof(c_0_43, plain, ![X32, X33, X34, X35]:((~r1_xboole_0(X32,X33)|r1_xboole_0(k2_zfmisc_1(X32,X34),k2_zfmisc_1(X33,X35)))&(~r1_xboole_0(X34,X35)|r1_xboole_0(k2_zfmisc_1(X32,X34),k2_zfmisc_1(X33,X35)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t127_zfmisc_1])])])).
% 0.19/0.42  cnf(c_0_44, plain, (k3_zfmisc_1(k2_zfmisc_1(X1,X2),X3,X4)=k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4)), inference(rw,[status(thm)],[c_0_35, c_0_27])).
% 0.19/0.42  cnf(c_0_45, plain, (~r1_tarski(X1,X2)|~r2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.19/0.42  cnf(c_0_46, plain, (X1=X2|r2_xboole_0(X1,X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.19/0.42  cnf(c_0_47, negated_conjecture, (k2_zfmisc_1(X1,X2)=k1_xboole_0|r1_tarski(X2,esk2_0)|~r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0),esk3_0),esk3_0))), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.19/0.42  cnf(c_0_48, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.19/0.42  cnf(c_0_49, plain, (k3_zfmisc_1(X2,X1,X3)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.19/0.42  cnf(c_0_50, plain, (r1_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X4,X2))|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.19/0.42  fof(c_0_51, plain, ![X36, X37]:((k2_zfmisc_1(k1_tarski(X37),X36)!=k1_xboole_0|X36=k1_xboole_0)&(k2_zfmisc_1(X36,k1_tarski(X37))!=k1_xboole_0|X36=k1_xboole_0)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t130_zfmisc_1])])])).
% 0.19/0.42  fof(c_0_52, plain, ![X27]:k2_tarski(X27,X27)=k1_tarski(X27), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.19/0.42  fof(c_0_53, plain, ![X28, X29]:k5_enumset1(X28,X28,X28,X28,X28,X28,X29)=k2_tarski(X28,X29), inference(variable_rename,[status(thm)],[t92_enumset1])).
% 0.19/0.42  cnf(c_0_54, plain, (X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|k3_zfmisc_1(X1,X2,X3)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.19/0.42  cnf(c_0_55, plain, (k3_zfmisc_1(k2_zfmisc_1(X1,X2),X3,X4)=k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4)), inference(rw,[status(thm)],[c_0_44, c_0_32])).
% 0.19/0.42  cnf(c_0_56, plain, (X1=X2|~r1_tarski(X2,X1)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.19/0.42  cnf(c_0_57, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0),esk3_0),esk3_0)=k1_xboole_0|r1_tarski(esk3_0,esk2_0)), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.19/0.42  cnf(c_0_58, negated_conjecture, (esk2_0!=esk3_0), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.42  cnf(c_0_59, plain, (k3_zfmisc_1(X1,k1_xboole_0,X2)=k1_xboole_0), inference(er,[status(thm)],[c_0_49])).
% 0.19/0.42  fof(c_0_60, plain, ![X5, X6]:((~r1_xboole_0(X5,X6)|k3_xboole_0(X5,X6)=k1_xboole_0)&(k3_xboole_0(X5,X6)!=k1_xboole_0|r1_xboole_0(X5,X6))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 0.19/0.42  cnf(c_0_61, negated_conjecture, (r1_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0),esk3_0),esk3_0))|~r1_xboole_0(X2,esk2_0)), inference(spm,[status(thm)],[c_0_50, c_0_39])).
% 0.19/0.42  cnf(c_0_62, plain, (X1=k1_xboole_0|k2_zfmisc_1(X1,k1_tarski(X2))!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.19/0.42  cnf(c_0_63, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.19/0.42  cnf(c_0_64, plain, (k5_enumset1(X1,X1,X1,X1,X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.19/0.42  cnf(c_0_65, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.19/0.42  cnf(c_0_66, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0),esk3_0),esk3_0)=k1_xboole_0|r1_tarski(esk2_0,X1)|~r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0),esk3_0),esk3_0),k2_zfmisc_1(X2,X1))), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.19/0.42  cnf(c_0_67, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0),esk3_0),esk3_0)=k1_xboole_0|~r1_tarski(esk2_0,esk3_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_58])).
% 0.19/0.42  cnf(c_0_68, plain, (k3_zfmisc_1(X1,X2,X3)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.19/0.42  cnf(c_0_69, plain, (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0),X2),X3)=k2_zfmisc_1(k1_xboole_0,X3)), inference(spm,[status(thm)],[c_0_32, c_0_59])).
% 0.19/0.42  cnf(c_0_70, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.19/0.42  cnf(c_0_71, negated_conjecture, (r1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0),esk3_0),esk3_0),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0),esk3_0),esk3_0))|~r1_xboole_0(esk2_0,esk2_0)), inference(spm,[status(thm)],[c_0_61, c_0_39])).
% 0.19/0.42  cnf(c_0_72, plain, (X1=k1_xboole_0|k2_zfmisc_1(X1,k5_enumset1(X2,X2,X2,X2,X2,X2,X2))!=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_62, c_0_63]), c_0_64])).
% 0.19/0.42  cnf(c_0_73, negated_conjecture, (k2_zfmisc_1(esk2_0,esk2_0)=k1_xboole_0|esk2_0=k1_xboole_0|k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0),esk3_0),esk3_0)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_65, c_0_39])).
% 0.19/0.42  cnf(c_0_74, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0),esk3_0),esk3_0)=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_48]), c_0_67])).
% 0.19/0.42  cnf(c_0_75, plain, (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),k1_xboole_0),X3)=k1_xboole_0), inference(spm,[status(thm)],[c_0_59, c_0_55])).
% 0.19/0.42  cnf(c_0_76, plain, (k3_zfmisc_1(k1_xboole_0,X1,X2)=k1_xboole_0), inference(er,[status(thm)],[c_0_68])).
% 0.19/0.42  cnf(c_0_77, plain, (k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1),X2)=k2_zfmisc_1(k1_xboole_0,X2)), inference(spm,[status(thm)],[c_0_69, c_0_69])).
% 0.19/0.42  fof(c_0_78, plain, ![X16, X17]:k5_xboole_0(X16,X17)=k4_xboole_0(k2_xboole_0(X16,X17),k3_xboole_0(X16,X17)), inference(variable_rename,[status(thm)],[l98_xboole_1])).
% 0.19/0.42  fof(c_0_79, plain, ![X30, X31]:k3_tarski(k2_tarski(X30,X31))=k2_xboole_0(X30,X31), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.19/0.42  cnf(c_0_80, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0),esk3_0),esk3_0)=k1_xboole_0|~r1_xboole_0(esk2_0,esk2_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_71]), c_0_41])).
% 0.19/0.42  cnf(c_0_81, plain, (r1_xboole_0(X1,X2)|k3_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.19/0.42  cnf(c_0_82, plain, (k3_zfmisc_1(X1,X2,X3)=k1_xboole_0|k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),k5_enumset1(X4,X4,X4,X4,X4,X4,X4))!=k1_xboole_0), inference(spm,[status(thm)],[c_0_72, c_0_32])).
% 0.19/0.42  cnf(c_0_83, negated_conjecture, (k2_zfmisc_1(esk2_0,esk2_0)=k1_xboole_0|esk2_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_73, c_0_74])])).
% 0.19/0.42  cnf(c_0_84, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_75]), c_0_76]), c_0_77])).
% 0.19/0.42  fof(c_0_85, plain, ![X23]:k5_xboole_0(X23,k1_xboole_0)=X23, inference(variable_rename,[status(thm)],[t5_boole])).
% 0.19/0.42  cnf(c_0_86, plain, (k5_xboole_0(X1,X2)=k4_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_78])).
% 0.19/0.42  cnf(c_0_87, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_79])).
% 0.19/0.42  fof(c_0_88, plain, ![X20]:k2_xboole_0(X20,k1_xboole_0)=X20, inference(variable_rename,[status(thm)],[t1_boole])).
% 0.19/0.42  fof(c_0_89, plain, ![X42, X43, X44]:(((r2_hidden(X42,X44)|~r1_tarski(k2_tarski(X42,X43),X44))&(r2_hidden(X43,X44)|~r1_tarski(k2_tarski(X42,X43),X44)))&(~r2_hidden(X42,X44)|~r2_hidden(X43,X44)|r1_tarski(k2_tarski(X42,X43),X44))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_zfmisc_1])])])).
% 0.19/0.42  cnf(c_0_90, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0),esk3_0),esk3_0)=k1_xboole_0|esk2_0!=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_81]), c_0_41])).
% 0.19/0.42  cnf(c_0_91, negated_conjecture, (k3_zfmisc_1(esk2_0,esk2_0,X1)=k1_xboole_0|esk2_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_83]), c_0_84]), c_0_84])])).
% 0.19/0.42  cnf(c_0_92, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_85])).
% 0.19/0.42  cnf(c_0_93, plain, (k5_xboole_0(X1,X2)=k4_xboole_0(k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X2)),k3_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_86, c_0_87]), c_0_64])).
% 0.19/0.42  cnf(c_0_94, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_88])).
% 0.19/0.42  fof(c_0_95, plain, ![X10, X11, X13, X14, X15]:((r1_xboole_0(X10,X11)|r2_hidden(esk1_2(X10,X11),k3_xboole_0(X10,X11)))&(~r2_hidden(X15,k3_xboole_0(X13,X14))|~r1_xboole_0(X13,X14))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 0.19/0.42  cnf(c_0_96, plain, (r2_hidden(X1,X2)|~r1_tarski(k2_tarski(X3,X1),X2)), inference(split_conjunct,[status(thm)],[c_0_89])).
% 0.19/0.42  cnf(c_0_97, negated_conjecture, (k2_zfmisc_1(esk3_0,esk3_0)=k1_xboole_0|esk3_0=k1_xboole_0|esk2_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_65, c_0_90])).
% 0.19/0.42  cnf(c_0_98, negated_conjecture, (esk2_0=k1_xboole_0|X1=k1_xboole_0), inference(spm,[status(thm)],[c_0_54, c_0_91])).
% 0.19/0.42  fof(c_0_99, plain, ![X21, X22]:(~r1_tarski(X21,k4_xboole_0(X22,X21))|X21=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_xboole_1])])).
% 0.19/0.42  cnf(c_0_100, plain, (k4_xboole_0(k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,k1_xboole_0)),k3_xboole_0(X1,k1_xboole_0))=X1), inference(rw,[status(thm)],[c_0_92, c_0_93])).
% 0.19/0.42  cnf(c_0_101, plain, (k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,k1_xboole_0))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_94, c_0_87]), c_0_64])).
% 0.19/0.42  cnf(c_0_102, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_95])).
% 0.19/0.42  cnf(c_0_103, plain, (r2_hidden(X1,X2)|~r1_tarski(k5_enumset1(X3,X3,X3,X3,X3,X3,X1),X2)), inference(rw,[status(thm)],[c_0_96, c_0_64])).
% 0.19/0.42  cnf(c_0_104, negated_conjecture, (k3_zfmisc_1(esk3_0,esk3_0,X1)=k1_xboole_0|esk3_0=k1_xboole_0|esk2_0!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_97]), c_0_84]), c_0_84])])).
% 0.19/0.42  cnf(c_0_105, negated_conjecture, (esk2_0=k1_xboole_0), inference(ef,[status(thm)],[c_0_98])).
% 0.19/0.42  cnf(c_0_106, plain, (X1=k1_xboole_0|~r1_tarski(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_99])).
% 0.19/0.42  cnf(c_0_107, plain, (k4_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0))=X1), inference(rw,[status(thm)],[c_0_100, c_0_101])).
% 0.19/0.42  cnf(c_0_108, plain, (~r1_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X2),k3_xboole_0(X3,X4))|~r1_xboole_0(X3,X4)), inference(spm,[status(thm)],[c_0_102, c_0_103])).
% 0.19/0.42  cnf(c_0_109, negated_conjecture, (esk3_0=k1_xboole_0|X1=k1_xboole_0|esk2_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_54, c_0_104])).
% 0.19/0.42  cnf(c_0_110, negated_conjecture, (esk3_0!=k1_xboole_0), inference(rw,[status(thm)],[c_0_58, c_0_105])).
% 0.19/0.42  cnf(c_0_111, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106, c_0_107]), c_0_40])])).
% 0.19/0.42  cnf(c_0_112, plain, (k3_xboole_0(X1,X2)!=k1_xboole_0|~r1_tarski(k5_enumset1(X3,X3,X3,X3,X3,X3,X4),k3_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_108, c_0_81])).
% 0.19/0.42  cnf(c_0_113, negated_conjecture, (X1=k1_xboole_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_109, c_0_105])]), c_0_110])).
% 0.19/0.42  cnf(c_0_114, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_40, c_0_111])).
% 0.19/0.42  cnf(c_0_115, plain, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_112, c_0_113]), c_0_113]), c_0_113]), c_0_114])]), ['proof']).
% 0.19/0.42  # SZS output end CNFRefutation
% 0.19/0.42  # Proof object total steps             : 116
% 0.19/0.42  # Proof object clause steps            : 71
% 0.19/0.42  # Proof object formula steps           : 45
% 0.19/0.42  # Proof object conjectures             : 26
% 0.19/0.42  # Proof object clause conjectures      : 23
% 0.19/0.42  # Proof object formula conjectures     : 3
% 0.19/0.42  # Proof object initial clauses used    : 26
% 0.19/0.42  # Proof object initial formulas used   : 22
% 0.19/0.42  # Proof object generating inferences   : 28
% 0.19/0.42  # Proof object simplifying inferences  : 43
% 0.19/0.42  # Training examples: 0 positive, 0 negative
% 0.19/0.42  # Parsed axioms                        : 23
% 0.19/0.42  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.42  # Initial clauses                      : 37
% 0.19/0.42  # Removed in clause preprocessing      : 5
% 0.19/0.42  # Initial clauses in saturation        : 32
% 0.19/0.42  # Processed clauses                    : 617
% 0.19/0.42  # ...of these trivial                  : 18
% 0.19/0.42  # ...subsumed                          : 279
% 0.19/0.42  # ...remaining for further processing  : 320
% 0.19/0.42  # Other redundant clauses eliminated   : 58
% 0.19/0.42  # Clauses deleted for lack of memory   : 0
% 0.19/0.42  # Backward-subsumed                    : 17
% 0.19/0.42  # Backward-rewritten                   : 253
% 0.19/0.42  # Generated clauses                    : 2582
% 0.19/0.42  # ...of the previous two non-trivial   : 1505
% 0.19/0.42  # Contextual simplify-reflections      : 1
% 0.19/0.42  # Paramodulations                      : 2520
% 0.19/0.42  # Factorizations                       : 3
% 0.19/0.42  # Equation resolutions                 : 58
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
% 0.19/0.42  # Current number of processed clauses  : 12
% 0.19/0.42  #    Positive orientable unit clauses  : 4
% 0.19/0.42  #    Positive unorientable unit clauses: 1
% 0.19/0.42  #    Negative unit clauses             : 2
% 0.19/0.42  #    Non-unit-clauses                  : 5
% 0.19/0.42  # Current number of unprocessed clauses: 905
% 0.19/0.42  # ...number of literals in the above   : 2083
% 0.19/0.42  # Current number of archived formulas  : 0
% 0.19/0.42  # Current number of archived clauses   : 308
% 0.19/0.42  # Clause-clause subsumption calls (NU) : 9130
% 0.19/0.42  # Rec. Clause-clause subsumption calls : 8799
% 0.19/0.42  # Non-unit clause-clause subsumptions  : 155
% 0.19/0.42  # Unit Clause-clause subsumption calls : 32
% 0.19/0.42  # Rewrite failures with RHS unbound    : 3
% 0.19/0.42  # BW rewrite match attempts            : 146
% 0.19/0.42  # BW rewrite match successes           : 129
% 0.19/0.42  # Condensation attempts                : 0
% 0.19/0.42  # Condensation successes               : 0
% 0.19/0.42  # Termbank termtop insertions          : 37395
% 0.19/0.42  
% 0.19/0.42  # -------------------------------------------------
% 0.19/0.42  # User time                : 0.072 s
% 0.19/0.42  # System time              : 0.003 s
% 0.19/0.42  # Total time               : 0.075 s
% 0.19/0.42  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
