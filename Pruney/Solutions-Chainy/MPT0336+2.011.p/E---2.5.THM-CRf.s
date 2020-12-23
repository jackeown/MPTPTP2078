%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:44:49 EST 2020

% Result     : Theorem 0.58s
% Output     : CNFRefutation 0.58s
% Verified   : 
% Statistics : Number of formulae       :  109 (1071 expanded)
%              Number of clauses        :   70 ( 491 expanded)
%              Number of leaves         :   19 ( 284 expanded)
%              Depth                    :   19
%              Number of atoms          :  167 (2569 expanded)
%              Number of equality atoms :   66 ( 672 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal clause size      :    7 (   1 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(t79_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t83_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k4_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(t149_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( r1_tarski(k3_xboole_0(X1,X2),k1_tarski(X4))
        & r2_hidden(X4,X3)
        & r1_xboole_0(X3,X2) )
     => r1_xboole_0(k2_xboole_0(X1,X3),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_zfmisc_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(l27_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( ~ r2_hidden(X1,X2)
     => r1_xboole_0(k1_tarski(X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t16_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

fof(t74_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( ~ r1_xboole_0(X1,k3_xboole_0(X2,X3))
        & r1_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_xboole_1)).

fof(t78_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_xboole_0(X1,X2)
     => k3_xboole_0(X1,k2_xboole_0(X2,X3)) = k3_xboole_0(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_xboole_1)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(c_0_19,plain,(
    ! [X14,X15,X17,X18,X19] :
      ( ( r2_hidden(esk1_2(X14,X15),X14)
        | r1_xboole_0(X14,X15) )
      & ( r2_hidden(esk1_2(X14,X15),X15)
        | r1_xboole_0(X14,X15) )
      & ( ~ r2_hidden(X19,X17)
        | ~ r2_hidden(X19,X18)
        | ~ r1_xboole_0(X17,X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

cnf(c_0_20,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_21,plain,
    ( r2_hidden(esk1_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_22,plain,(
    ! [X9,X10] :
      ( ( ~ r1_xboole_0(X9,X10)
        | k3_xboole_0(X9,X10) = k1_xboole_0 )
      & ( k3_xboole_0(X9,X10) != k1_xboole_0
        | r1_xboole_0(X9,X10) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

fof(c_0_23,plain,(
    ! [X11] : k3_xboole_0(X11,X11) = X11 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

cnf(c_0_24,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X3)
    | ~ r1_xboole_0(X3,X2) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_25,plain,
    ( r1_xboole_0(X1,X2)
    | k3_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_26,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_27,plain,(
    ! [X33,X34] : r1_xboole_0(k4_xboole_0(X33,X34),X34) ),
    inference(variable_rename,[status(thm)],[t79_xboole_1])).

fof(c_0_28,plain,(
    ! [X20,X21] : k4_xboole_0(X20,X21) = k5_xboole_0(X20,k3_xboole_0(X20,X21)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_29,plain,(
    ! [X35,X36] :
      ( ( ~ r1_xboole_0(X35,X36)
        | k4_xboole_0(X35,X36) = X35 )
      & ( k4_xboole_0(X35,X36) != X35
        | r1_xboole_0(X35,X36) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).

cnf(c_0_30,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X2,X2) ),
    inference(spm,[status(thm)],[c_0_24,c_0_21])).

cnf(c_0_31,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26])])).

fof(c_0_32,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( r1_tarski(k3_xboole_0(X1,X2),k1_tarski(X4))
          & r2_hidden(X4,X3)
          & r1_xboole_0(X3,X2) )
       => r1_xboole_0(k2_xboole_0(X1,X3),X2) ) ),
    inference(assume_negation,[status(cth)],[t149_zfmisc_1])).

cnf(c_0_33,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_34,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_35,plain,(
    ! [X7,X8] : k3_xboole_0(X7,X8) = k3_xboole_0(X8,X7) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_36,plain,
    ( k4_xboole_0(X1,X2) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_37,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_38,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

fof(c_0_39,negated_conjecture,
    ( r1_tarski(k3_xboole_0(esk2_0,esk3_0),k1_tarski(esk5_0))
    & r2_hidden(esk5_0,esk4_0)
    & r1_xboole_0(esk4_0,esk3_0)
    & ~ r1_xboole_0(k2_xboole_0(esk2_0,esk4_0),esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_32])])])).

fof(c_0_40,plain,(
    ! [X39] : k2_tarski(X39,X39) = k1_tarski(X39) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_41,plain,(
    ! [X40,X41] : k1_enumset1(X40,X40,X41) = k2_tarski(X40,X41) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_42,plain,(
    ! [X42,X43,X44] : k2_enumset1(X42,X42,X43,X44) = k1_enumset1(X42,X43,X44) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_43,plain,(
    ! [X45,X46] :
      ( r2_hidden(X45,X46)
      | r1_xboole_0(k1_tarski(X45),X46) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l27_zfmisc_1])])])).

cnf(c_0_44,plain,
    ( r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X2) ),
    inference(rw,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_45,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_46,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_36,c_0_34])).

cnf(c_0_47,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_48,negated_conjecture,
    ( r1_tarski(k3_xboole_0(esk2_0,esk3_0),k1_tarski(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_49,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_50,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_51,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_52,negated_conjecture,
    ( r2_hidden(esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_53,plain,
    ( r2_hidden(X1,X2)
    | r1_xboole_0(k1_tarski(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

fof(c_0_54,plain,(
    ! [X12,X13] :
      ( ~ r1_xboole_0(X12,X13)
      | r1_xboole_0(X13,X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

cnf(c_0_55,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_44]),c_0_45])).

cnf(c_0_56,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_38]),c_0_47])).

fof(c_0_57,plain,(
    ! [X25,X26] :
      ( ~ r1_tarski(X25,X26)
      | k3_xboole_0(X25,X26) = X25 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_58,negated_conjecture,
    ( r1_tarski(k3_xboole_0(esk2_0,esk3_0),k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_49]),c_0_50]),c_0_51])).

cnf(c_0_59,negated_conjecture,
    ( ~ r2_hidden(esk5_0,X1)
    | ~ r1_xboole_0(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_52])).

cnf(c_0_60,plain,
    ( r2_hidden(X1,X2)
    | r1_xboole_0(k2_enumset1(X1,X1,X1,X1),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53,c_0_49]),c_0_50]),c_0_51])).

cnf(c_0_61,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_62,negated_conjecture,
    ( r1_xboole_0(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_63,plain,
    ( r1_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_55]),c_0_56])).

fof(c_0_64,plain,(
    ! [X22,X23,X24] : k3_xboole_0(k3_xboole_0(X22,X23),X24) = k3_xboole_0(X22,k3_xboole_0(X23,X24)) ),
    inference(variable_rename,[status(thm)],[t16_xboole_1])).

cnf(c_0_65,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_66,negated_conjecture,
    ( r1_tarski(k3_xboole_0(esk3_0,esk2_0),k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)) ),
    inference(rw,[status(thm)],[c_0_58,c_0_45])).

cnf(c_0_67,negated_conjecture,
    ( r1_xboole_0(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),X1)
    | ~ r1_xboole_0(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_68,negated_conjecture,
    ( r1_xboole_0(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

fof(c_0_69,plain,(
    ! [X27,X28,X29] :
      ( r1_xboole_0(X27,k3_xboole_0(X28,X29))
      | ~ r1_xboole_0(X27,X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t74_xboole_1])])])).

cnf(c_0_70,plain,
    ( r1_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_63,c_0_45])).

cnf(c_0_71,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_72,negated_conjecture,
    ( k3_xboole_0(k3_xboole_0(esk3_0,esk2_0),k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)) = k3_xboole_0(esk3_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_73,negated_conjecture,
    ( r1_xboole_0(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_74,plain,
    ( r1_xboole_0(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_75,plain,
    ( r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X2,X1)),X2) ),
    inference(spm,[status(thm)],[c_0_61,c_0_70])).

cnf(c_0_76,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,k3_xboole_0(X1,X2))) = k3_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_26,c_0_71])).

cnf(c_0_77,negated_conjecture,
    ( k3_xboole_0(esk3_0,k3_xboole_0(esk2_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))) = k3_xboole_0(esk3_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_72,c_0_71])).

cnf(c_0_78,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,X3)) = k3_xboole_0(X3,k3_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_71])).

cnf(c_0_79,negated_conjecture,
    ( k3_xboole_0(esk3_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_73]),c_0_45])).

fof(c_0_80,plain,(
    ! [X30,X31,X32] :
      ( ~ r1_xboole_0(X30,X31)
      | k3_xboole_0(X30,k2_xboole_0(X31,X32)) = k3_xboole_0(X30,X32) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t78_xboole_1])])).

fof(c_0_81,plain,(
    ! [X37,X38] : k2_xboole_0(X37,X38) = k5_xboole_0(X37,k4_xboole_0(X38,X37)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

cnf(c_0_82,plain,
    ( r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X2,X1)),k3_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_83,negated_conjecture,
    ( k3_xboole_0(esk3_0,esk2_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_71]),c_0_78]),c_0_45]),c_0_79]),c_0_47]),c_0_47]),c_0_47])).

cnf(c_0_84,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X2,X3)) = k3_xboole_0(X1,X3)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_80])).

cnf(c_0_85,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_81])).

cnf(c_0_86,negated_conjecture,
    ( r1_xboole_0(esk2_0,k3_xboole_0(esk3_0,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_56])).

fof(c_0_87,plain,(
    ! [X5,X6] : k2_xboole_0(X5,X6) = k2_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_88,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2)))) = k3_xboole_0(X1,X3)
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_84,c_0_85]),c_0_34])).

cnf(c_0_89,negated_conjecture,
    ( r1_xboole_0(esk4_0,k3_xboole_0(esk3_0,X1)) ),
    inference(spm,[status(thm)],[c_0_74,c_0_62])).

cnf(c_0_90,negated_conjecture,
    ( r1_xboole_0(esk2_0,k3_xboole_0(X1,k3_xboole_0(esk3_0,X2))) ),
    inference(spm,[status(thm)],[c_0_86,c_0_78])).

cnf(c_0_91,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_87])).

cnf(c_0_92,negated_conjecture,
    ( k3_xboole_0(esk4_0,k5_xboole_0(k3_xboole_0(esk3_0,X1),k5_xboole_0(X2,k3_xboole_0(X2,k3_xboole_0(esk3_0,X1))))) = k3_xboole_0(esk4_0,X2) ),
    inference(spm,[status(thm)],[c_0_88,c_0_89])).

cnf(c_0_93,negated_conjecture,
    ( k3_xboole_0(esk2_0,k3_xboole_0(X1,k3_xboole_0(esk3_0,X2))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_37,c_0_90])).

cnf(c_0_94,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_71,c_0_26])).

cnf(c_0_95,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) = k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_91,c_0_85]),c_0_85]),c_0_34]),c_0_34])).

cnf(c_0_96,negated_conjecture,
    ( k3_xboole_0(esk4_0,k5_xboole_0(k3_xboole_0(esk3_0,X1),esk2_0)) = k3_xboole_0(esk4_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_93]),c_0_94]),c_0_56])).

cnf(c_0_97,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k3_xboole_0(X2,X3),k3_xboole_0(X2,k3_xboole_0(X3,X1)))) = k5_xboole_0(k3_xboole_0(X2,X3),k5_xboole_0(X1,k3_xboole_0(X2,k3_xboole_0(X3,X1)))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_78]),c_0_71])).

cnf(c_0_98,negated_conjecture,
    ( k3_xboole_0(esk4_0,k5_xboole_0(k3_xboole_0(X1,esk3_0),esk2_0)) = k3_xboole_0(esk4_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_96,c_0_45])).

cnf(c_0_99,negated_conjecture,
    ( k5_xboole_0(k3_xboole_0(X1,esk3_0),esk2_0) = k5_xboole_0(esk2_0,k3_xboole_0(X1,esk3_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_83]),c_0_47]),c_0_56]),c_0_47]),c_0_56])).

cnf(c_0_100,negated_conjecture,
    ( ~ r1_xboole_0(k2_xboole_0(esk2_0,esk4_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_101,plain,
    ( k3_xboole_0(X1,k5_xboole_0(k5_xboole_0(X2,k3_xboole_0(X2,X1)),k5_xboole_0(X3,k3_xboole_0(X3,k5_xboole_0(X2,k3_xboole_0(X2,X1)))))) = k3_xboole_0(X1,X3) ),
    inference(spm,[status(thm)],[c_0_88,c_0_63])).

cnf(c_0_102,negated_conjecture,
    ( k3_xboole_0(esk4_0,k5_xboole_0(esk2_0,k3_xboole_0(X1,esk3_0))) = k3_xboole_0(esk4_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_98,c_0_99])).

cnf(c_0_103,negated_conjecture,
    ( k3_xboole_0(esk4_0,esk3_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_37,c_0_62])).

cnf(c_0_104,negated_conjecture,
    ( ~ r1_xboole_0(k5_xboole_0(esk2_0,k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,esk2_0))),esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_100,c_0_85]),c_0_34])).

cnf(c_0_105,plain,
    ( r1_xboole_0(X1,X2)
    | k3_xboole_0(X2,X1) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_25,c_0_45])).

cnf(c_0_106,negated_conjecture,
    ( k3_xboole_0(esk3_0,k5_xboole_0(esk4_0,k5_xboole_0(esk2_0,k3_xboole_0(esk4_0,esk2_0)))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_102]),c_0_45]),c_0_83]),c_0_56]),c_0_95]),c_0_45]),c_0_45]),c_0_103])).

cnf(c_0_107,negated_conjecture,
    ( ~ r1_xboole_0(k5_xboole_0(esk4_0,k5_xboole_0(esk2_0,k3_xboole_0(esk4_0,esk2_0))),esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_104,c_0_95]),c_0_45])).

cnf(c_0_108,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_106]),c_0_107]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:04:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.58/0.81  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S03EI
% 0.58/0.81  # and selection function SelectLComplex.
% 0.58/0.81  #
% 0.58/0.81  # Preprocessing time       : 0.027 s
% 0.58/0.81  # Presaturation interreduction done
% 0.58/0.81  
% 0.58/0.81  # Proof found!
% 0.58/0.81  # SZS status Theorem
% 0.58/0.81  # SZS output start CNFRefutation
% 0.58/0.81  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.58/0.81  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 0.58/0.81  fof(idempotence_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 0.58/0.81  fof(t79_xboole_1, axiom, ![X1, X2]:r1_xboole_0(k4_xboole_0(X1,X2),X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 0.58/0.81  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.58/0.81  fof(t83_xboole_1, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k4_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 0.58/0.81  fof(t149_zfmisc_1, conjecture, ![X1, X2, X3, X4]:(((r1_tarski(k3_xboole_0(X1,X2),k1_tarski(X4))&r2_hidden(X4,X3))&r1_xboole_0(X3,X2))=>r1_xboole_0(k2_xboole_0(X1,X3),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t149_zfmisc_1)).
% 0.58/0.81  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.58/0.81  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.58/0.81  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.58/0.81  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.58/0.81  fof(l27_zfmisc_1, axiom, ![X1, X2]:(~(r2_hidden(X1,X2))=>r1_xboole_0(k1_tarski(X1),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 0.58/0.81  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 0.58/0.81  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.58/0.81  fof(t16_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(k3_xboole_0(X1,X2),X3)=k3_xboole_0(X1,k3_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_xboole_1)).
% 0.58/0.81  fof(t74_xboole_1, axiom, ![X1, X2, X3]:~((~(r1_xboole_0(X1,k3_xboole_0(X2,X3)))&r1_xboole_0(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_xboole_1)).
% 0.58/0.81  fof(t78_xboole_1, axiom, ![X1, X2, X3]:(r1_xboole_0(X1,X2)=>k3_xboole_0(X1,k2_xboole_0(X2,X3))=k3_xboole_0(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_xboole_1)).
% 0.58/0.81  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.58/0.81  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.58/0.81  fof(c_0_19, plain, ![X14, X15, X17, X18, X19]:(((r2_hidden(esk1_2(X14,X15),X14)|r1_xboole_0(X14,X15))&(r2_hidden(esk1_2(X14,X15),X15)|r1_xboole_0(X14,X15)))&(~r2_hidden(X19,X17)|~r2_hidden(X19,X18)|~r1_xboole_0(X17,X18))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.58/0.81  cnf(c_0_20, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.58/0.81  cnf(c_0_21, plain, (r2_hidden(esk1_2(X1,X2),X2)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.58/0.81  fof(c_0_22, plain, ![X9, X10]:((~r1_xboole_0(X9,X10)|k3_xboole_0(X9,X10)=k1_xboole_0)&(k3_xboole_0(X9,X10)!=k1_xboole_0|r1_xboole_0(X9,X10))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 0.58/0.81  fof(c_0_23, plain, ![X11]:k3_xboole_0(X11,X11)=X11, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).
% 0.58/0.81  cnf(c_0_24, plain, (r1_xboole_0(X1,X2)|~r2_hidden(esk1_2(X1,X2),X3)|~r1_xboole_0(X3,X2)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.58/0.81  cnf(c_0_25, plain, (r1_xboole_0(X1,X2)|k3_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.58/0.81  cnf(c_0_26, plain, (k3_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.58/0.81  fof(c_0_27, plain, ![X33, X34]:r1_xboole_0(k4_xboole_0(X33,X34),X34), inference(variable_rename,[status(thm)],[t79_xboole_1])).
% 0.58/0.81  fof(c_0_28, plain, ![X20, X21]:k4_xboole_0(X20,X21)=k5_xboole_0(X20,k3_xboole_0(X20,X21)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.58/0.81  fof(c_0_29, plain, ![X35, X36]:((~r1_xboole_0(X35,X36)|k4_xboole_0(X35,X36)=X35)&(k4_xboole_0(X35,X36)!=X35|r1_xboole_0(X35,X36))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).
% 0.58/0.81  cnf(c_0_30, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(X2,X2)), inference(spm,[status(thm)],[c_0_24, c_0_21])).
% 0.58/0.81  cnf(c_0_31, plain, (r1_xboole_0(k1_xboole_0,k1_xboole_0)), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26])])).
% 0.58/0.81  fof(c_0_32, negated_conjecture, ~(![X1, X2, X3, X4]:(((r1_tarski(k3_xboole_0(X1,X2),k1_tarski(X4))&r2_hidden(X4,X3))&r1_xboole_0(X3,X2))=>r1_xboole_0(k2_xboole_0(X1,X3),X2))), inference(assume_negation,[status(cth)],[t149_zfmisc_1])).
% 0.58/0.81  cnf(c_0_33, plain, (r1_xboole_0(k4_xboole_0(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.58/0.81  cnf(c_0_34, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.58/0.81  fof(c_0_35, plain, ![X7, X8]:k3_xboole_0(X7,X8)=k3_xboole_0(X8,X7), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.58/0.81  cnf(c_0_36, plain, (k4_xboole_0(X1,X2)=X1|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.58/0.81  cnf(c_0_37, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.58/0.81  cnf(c_0_38, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.58/0.81  fof(c_0_39, negated_conjecture, (((r1_tarski(k3_xboole_0(esk2_0,esk3_0),k1_tarski(esk5_0))&r2_hidden(esk5_0,esk4_0))&r1_xboole_0(esk4_0,esk3_0))&~r1_xboole_0(k2_xboole_0(esk2_0,esk4_0),esk3_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_32])])])).
% 0.58/0.81  fof(c_0_40, plain, ![X39]:k2_tarski(X39,X39)=k1_tarski(X39), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.58/0.81  fof(c_0_41, plain, ![X40, X41]:k1_enumset1(X40,X40,X41)=k2_tarski(X40,X41), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.58/0.81  fof(c_0_42, plain, ![X42, X43, X44]:k2_enumset1(X42,X42,X43,X44)=k1_enumset1(X42,X43,X44), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.58/0.81  fof(c_0_43, plain, ![X45, X46]:(r2_hidden(X45,X46)|r1_xboole_0(k1_tarski(X45),X46)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l27_zfmisc_1])])])).
% 0.58/0.81  cnf(c_0_44, plain, (r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X2)), inference(rw,[status(thm)],[c_0_33, c_0_34])).
% 0.58/0.81  cnf(c_0_45, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.58/0.81  cnf(c_0_46, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X2))=X1|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_36, c_0_34])).
% 0.58/0.81  cnf(c_0_47, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.58/0.81  cnf(c_0_48, negated_conjecture, (r1_tarski(k3_xboole_0(esk2_0,esk3_0),k1_tarski(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.58/0.81  cnf(c_0_49, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.58/0.81  cnf(c_0_50, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.58/0.81  cnf(c_0_51, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.58/0.81  cnf(c_0_52, negated_conjecture, (r2_hidden(esk5_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.58/0.81  cnf(c_0_53, plain, (r2_hidden(X1,X2)|r1_xboole_0(k1_tarski(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.58/0.81  fof(c_0_54, plain, ![X12, X13]:(~r1_xboole_0(X12,X13)|r1_xboole_0(X13,X12)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 0.58/0.81  cnf(c_0_55, plain, (k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_44]), c_0_45])).
% 0.58/0.81  cnf(c_0_56, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_38]), c_0_47])).
% 0.58/0.81  fof(c_0_57, plain, ![X25, X26]:(~r1_tarski(X25,X26)|k3_xboole_0(X25,X26)=X25), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.58/0.81  cnf(c_0_58, negated_conjecture, (r1_tarski(k3_xboole_0(esk2_0,esk3_0),k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48, c_0_49]), c_0_50]), c_0_51])).
% 0.58/0.81  cnf(c_0_59, negated_conjecture, (~r2_hidden(esk5_0,X1)|~r1_xboole_0(X1,esk4_0)), inference(spm,[status(thm)],[c_0_20, c_0_52])).
% 0.58/0.81  cnf(c_0_60, plain, (r2_hidden(X1,X2)|r1_xboole_0(k2_enumset1(X1,X1,X1,X1),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53, c_0_49]), c_0_50]), c_0_51])).
% 0.58/0.81  cnf(c_0_61, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.58/0.81  cnf(c_0_62, negated_conjecture, (r1_xboole_0(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.58/0.81  cnf(c_0_63, plain, (r1_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_55]), c_0_56])).
% 0.58/0.81  fof(c_0_64, plain, ![X22, X23, X24]:k3_xboole_0(k3_xboole_0(X22,X23),X24)=k3_xboole_0(X22,k3_xboole_0(X23,X24)), inference(variable_rename,[status(thm)],[t16_xboole_1])).
% 0.58/0.81  cnf(c_0_65, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.58/0.81  cnf(c_0_66, negated_conjecture, (r1_tarski(k3_xboole_0(esk3_0,esk2_0),k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))), inference(rw,[status(thm)],[c_0_58, c_0_45])).
% 0.58/0.81  cnf(c_0_67, negated_conjecture, (r1_xboole_0(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),X1)|~r1_xboole_0(X1,esk4_0)), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 0.58/0.81  cnf(c_0_68, negated_conjecture, (r1_xboole_0(esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 0.58/0.81  fof(c_0_69, plain, ![X27, X28, X29]:(r1_xboole_0(X27,k3_xboole_0(X28,X29))|~r1_xboole_0(X27,X28)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t74_xboole_1])])])).
% 0.58/0.81  cnf(c_0_70, plain, (r1_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2)))), inference(spm,[status(thm)],[c_0_63, c_0_45])).
% 0.58/0.81  cnf(c_0_71, plain, (k3_xboole_0(k3_xboole_0(X1,X2),X3)=k3_xboole_0(X1,k3_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.58/0.81  cnf(c_0_72, negated_conjecture, (k3_xboole_0(k3_xboole_0(esk3_0,esk2_0),k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))=k3_xboole_0(esk3_0,esk2_0)), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 0.58/0.81  cnf(c_0_73, negated_conjecture, (r1_xboole_0(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),esk3_0)), inference(spm,[status(thm)],[c_0_67, c_0_68])).
% 0.58/0.81  cnf(c_0_74, plain, (r1_xboole_0(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_69])).
% 0.58/0.81  cnf(c_0_75, plain, (r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X2,X1)),X2)), inference(spm,[status(thm)],[c_0_61, c_0_70])).
% 0.58/0.81  cnf(c_0_76, plain, (k3_xboole_0(X1,k3_xboole_0(X2,k3_xboole_0(X1,X2)))=k3_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_26, c_0_71])).
% 0.58/0.81  cnf(c_0_77, negated_conjecture, (k3_xboole_0(esk3_0,k3_xboole_0(esk2_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)))=k3_xboole_0(esk3_0,esk2_0)), inference(rw,[status(thm)],[c_0_72, c_0_71])).
% 0.58/0.81  cnf(c_0_78, plain, (k3_xboole_0(X1,k3_xboole_0(X2,X3))=k3_xboole_0(X3,k3_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_45, c_0_71])).
% 0.58/0.81  cnf(c_0_79, negated_conjecture, (k3_xboole_0(esk3_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_73]), c_0_45])).
% 0.58/0.81  fof(c_0_80, plain, ![X30, X31, X32]:(~r1_xboole_0(X30,X31)|k3_xboole_0(X30,k2_xboole_0(X31,X32))=k3_xboole_0(X30,X32)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t78_xboole_1])])).
% 0.58/0.81  fof(c_0_81, plain, ![X37, X38]:k2_xboole_0(X37,X38)=k5_xboole_0(X37,k4_xboole_0(X38,X37)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.58/0.81  cnf(c_0_82, plain, (r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X2,X1)),k3_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_74, c_0_75])).
% 0.58/0.81  cnf(c_0_83, negated_conjecture, (k3_xboole_0(esk3_0,esk2_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_77]), c_0_71]), c_0_78]), c_0_45]), c_0_79]), c_0_47]), c_0_47]), c_0_47])).
% 0.58/0.81  cnf(c_0_84, plain, (k3_xboole_0(X1,k2_xboole_0(X2,X3))=k3_xboole_0(X1,X3)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_80])).
% 0.58/0.81  cnf(c_0_85, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_81])).
% 0.58/0.81  cnf(c_0_86, negated_conjecture, (r1_xboole_0(esk2_0,k3_xboole_0(esk3_0,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_83]), c_0_56])).
% 0.58/0.81  fof(c_0_87, plain, ![X5, X6]:k2_xboole_0(X5,X6)=k2_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.58/0.81  cnf(c_0_88, plain, (k3_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2))))=k3_xboole_0(X1,X3)|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_84, c_0_85]), c_0_34])).
% 0.58/0.81  cnf(c_0_89, negated_conjecture, (r1_xboole_0(esk4_0,k3_xboole_0(esk3_0,X1))), inference(spm,[status(thm)],[c_0_74, c_0_62])).
% 0.58/0.81  cnf(c_0_90, negated_conjecture, (r1_xboole_0(esk2_0,k3_xboole_0(X1,k3_xboole_0(esk3_0,X2)))), inference(spm,[status(thm)],[c_0_86, c_0_78])).
% 0.58/0.81  cnf(c_0_91, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_87])).
% 0.58/0.81  cnf(c_0_92, negated_conjecture, (k3_xboole_0(esk4_0,k5_xboole_0(k3_xboole_0(esk3_0,X1),k5_xboole_0(X2,k3_xboole_0(X2,k3_xboole_0(esk3_0,X1)))))=k3_xboole_0(esk4_0,X2)), inference(spm,[status(thm)],[c_0_88, c_0_89])).
% 0.58/0.81  cnf(c_0_93, negated_conjecture, (k3_xboole_0(esk2_0,k3_xboole_0(X1,k3_xboole_0(esk3_0,X2)))=k1_xboole_0), inference(spm,[status(thm)],[c_0_37, c_0_90])).
% 0.58/0.81  cnf(c_0_94, plain, (k3_xboole_0(X1,k3_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_71, c_0_26])).
% 0.58/0.81  cnf(c_0_95, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))=k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_91, c_0_85]), c_0_85]), c_0_34]), c_0_34])).
% 0.58/0.81  cnf(c_0_96, negated_conjecture, (k3_xboole_0(esk4_0,k5_xboole_0(k3_xboole_0(esk3_0,X1),esk2_0))=k3_xboole_0(esk4_0,esk2_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_93]), c_0_94]), c_0_56])).
% 0.58/0.81  cnf(c_0_97, plain, (k5_xboole_0(X1,k5_xboole_0(k3_xboole_0(X2,X3),k3_xboole_0(X2,k3_xboole_0(X3,X1))))=k5_xboole_0(k3_xboole_0(X2,X3),k5_xboole_0(X1,k3_xboole_0(X2,k3_xboole_0(X3,X1))))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_78]), c_0_71])).
% 0.58/0.81  cnf(c_0_98, negated_conjecture, (k3_xboole_0(esk4_0,k5_xboole_0(k3_xboole_0(X1,esk3_0),esk2_0))=k3_xboole_0(esk4_0,esk2_0)), inference(spm,[status(thm)],[c_0_96, c_0_45])).
% 0.58/0.81  cnf(c_0_99, negated_conjecture, (k5_xboole_0(k3_xboole_0(X1,esk3_0),esk2_0)=k5_xboole_0(esk2_0,k3_xboole_0(X1,esk3_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97, c_0_83]), c_0_47]), c_0_56]), c_0_47]), c_0_56])).
% 0.58/0.81  cnf(c_0_100, negated_conjecture, (~r1_xboole_0(k2_xboole_0(esk2_0,esk4_0),esk3_0)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.58/0.81  cnf(c_0_101, plain, (k3_xboole_0(X1,k5_xboole_0(k5_xboole_0(X2,k3_xboole_0(X2,X1)),k5_xboole_0(X3,k3_xboole_0(X3,k5_xboole_0(X2,k3_xboole_0(X2,X1))))))=k3_xboole_0(X1,X3)), inference(spm,[status(thm)],[c_0_88, c_0_63])).
% 0.58/0.81  cnf(c_0_102, negated_conjecture, (k3_xboole_0(esk4_0,k5_xboole_0(esk2_0,k3_xboole_0(X1,esk3_0)))=k3_xboole_0(esk4_0,esk2_0)), inference(rw,[status(thm)],[c_0_98, c_0_99])).
% 0.58/0.81  cnf(c_0_103, negated_conjecture, (k3_xboole_0(esk4_0,esk3_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_37, c_0_62])).
% 0.58/0.81  cnf(c_0_104, negated_conjecture, (~r1_xboole_0(k5_xboole_0(esk2_0,k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,esk2_0))),esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_100, c_0_85]), c_0_34])).
% 0.58/0.81  cnf(c_0_105, plain, (r1_xboole_0(X1,X2)|k3_xboole_0(X2,X1)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_25, c_0_45])).
% 0.58/0.81  cnf(c_0_106, negated_conjecture, (k3_xboole_0(esk3_0,k5_xboole_0(esk4_0,k5_xboole_0(esk2_0,k3_xboole_0(esk4_0,esk2_0))))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101, c_0_102]), c_0_45]), c_0_83]), c_0_56]), c_0_95]), c_0_45]), c_0_45]), c_0_103])).
% 0.58/0.81  cnf(c_0_107, negated_conjecture, (~r1_xboole_0(k5_xboole_0(esk4_0,k5_xboole_0(esk2_0,k3_xboole_0(esk4_0,esk2_0))),esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_104, c_0_95]), c_0_45])).
% 0.58/0.81  cnf(c_0_108, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_105, c_0_106]), c_0_107]), ['proof']).
% 0.58/0.81  # SZS output end CNFRefutation
% 0.58/0.81  # Proof object total steps             : 109
% 0.58/0.81  # Proof object clause steps            : 70
% 0.58/0.81  # Proof object formula steps           : 39
% 0.58/0.81  # Proof object conjectures             : 31
% 0.58/0.81  # Proof object clause conjectures      : 28
% 0.58/0.81  # Proof object formula conjectures     : 3
% 0.58/0.81  # Proof object initial clauses used    : 24
% 0.58/0.81  # Proof object initial formulas used   : 19
% 0.58/0.81  # Proof object generating inferences   : 35
% 0.58/0.81  # Proof object simplifying inferences  : 49
% 0.58/0.81  # Training examples: 0 positive, 0 negative
% 0.58/0.81  # Parsed axioms                        : 19
% 0.58/0.81  # Removed by relevancy pruning/SinE    : 0
% 0.58/0.81  # Initial clauses                      : 26
% 0.58/0.81  # Removed in clause preprocessing      : 5
% 0.58/0.81  # Initial clauses in saturation        : 21
% 0.58/0.81  # Processed clauses                    : 2953
% 0.58/0.81  # ...of these trivial                  : 920
% 0.58/0.81  # ...subsumed                          : 1035
% 0.58/0.81  # ...remaining for further processing  : 998
% 0.58/0.81  # Other redundant clauses eliminated   : 12
% 0.58/0.81  # Clauses deleted for lack of memory   : 0
% 0.58/0.81  # Backward-subsumed                    : 6
% 0.58/0.81  # Backward-rewritten                   : 110
% 0.58/0.81  # Generated clauses                    : 48450
% 0.58/0.81  # ...of the previous two non-trivial   : 24286
% 0.58/0.81  # Contextual simplify-reflections      : 0
% 0.58/0.81  # Paramodulations                      : 48438
% 0.58/0.81  # Factorizations                       : 0
% 0.58/0.81  # Equation resolutions                 : 12
% 0.58/0.81  # Propositional unsat checks           : 0
% 0.58/0.81  #    Propositional check models        : 0
% 0.58/0.81  #    Propositional check unsatisfiable : 0
% 0.58/0.81  #    Propositional clauses             : 0
% 0.58/0.81  #    Propositional clauses after purity: 0
% 0.58/0.81  #    Propositional unsat core size     : 0
% 0.58/0.81  #    Propositional preprocessing time  : 0.000
% 0.58/0.81  #    Propositional encoding time       : 0.000
% 0.58/0.81  #    Propositional solver time         : 0.000
% 0.58/0.81  #    Success case prop preproc time    : 0.000
% 0.58/0.81  #    Success case prop encoding time   : 0.000
% 0.58/0.81  #    Success case prop solver time     : 0.000
% 0.58/0.81  # Current number of processed clauses  : 861
% 0.58/0.81  #    Positive orientable unit clauses  : 637
% 0.58/0.81  #    Positive unorientable unit clauses: 7
% 0.58/0.81  #    Negative unit clauses             : 4
% 0.58/0.81  #    Non-unit-clauses                  : 213
% 0.58/0.81  # Current number of unprocessed clauses: 21116
% 0.58/0.81  # ...number of literals in the above   : 24981
% 0.58/0.81  # Current number of archived formulas  : 0
% 0.58/0.81  # Current number of archived clauses   : 142
% 0.58/0.81  # Clause-clause subsumption calls (NU) : 12188
% 0.58/0.81  # Rec. Clause-clause subsumption calls : 12171
% 0.58/0.81  # Non-unit clause-clause subsumptions  : 869
% 0.58/0.81  # Unit Clause-clause subsumption calls : 689
% 0.58/0.81  # Rewrite failures with RHS unbound    : 0
% 0.58/0.81  # BW rewrite match attempts            : 1174
% 0.58/0.81  # BW rewrite match successes           : 149
% 0.58/0.81  # Condensation attempts                : 0
% 0.58/0.81  # Condensation successes               : 0
% 0.58/0.81  # Termbank termtop insertions          : 695208
% 0.58/0.82  
% 0.58/0.82  # -------------------------------------------------
% 0.58/0.82  # User time                : 0.434 s
% 0.58/0.82  # System time              : 0.019 s
% 0.58/0.82  # Total time               : 0.454 s
% 0.58/0.82  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
