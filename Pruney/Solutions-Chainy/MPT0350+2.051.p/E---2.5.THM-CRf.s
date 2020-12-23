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
% DateTime   : Thu Dec  3 10:45:21 EST 2020

% Result     : Theorem 0.50s
% Output     : CNFRefutation 0.50s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 288 expanded)
%              Number of clauses        :   59 ( 122 expanded)
%              Number of leaves         :   28 (  79 expanded)
%              Depth                    :   12
%              Number of atoms          :  177 ( 456 expanded)
%              Number of equality atoms :   95 ( 248 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal clause size      :   12 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t25_subset_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k4_subset_1(X1,X2,k3_subset_1(X1,X2)) = k2_subset_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_subset_1)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(fc1_subset_1,axiom,(
    ! [X1] : ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(t21_xboole_1,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,k2_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(t75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(t79_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t92_xboole_1,axiom,(
    ! [X1] : k5_xboole_0(X1,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(l98_xboole_1,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k4_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l98_xboole_1)).

fof(t16_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

fof(commutativity_k5_xboole_0,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(t91_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(redefinition_k4_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => k4_subset_1(X1,X2,X3) = k2_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(dt_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(t5_boole,axiom,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(c_0_28,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X1))
       => k4_subset_1(X1,X2,k3_subset_1(X1,X2)) = k2_subset_1(X1) ) ),
    inference(assume_negation,[status(cth)],[t25_subset_1])).

fof(c_0_29,plain,(
    ! [X68,X69] : k3_tarski(k2_tarski(X68,X69)) = k2_xboole_0(X68,X69) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_30,plain,(
    ! [X34,X35] : k1_enumset1(X34,X34,X35) = k2_tarski(X34,X35) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_31,plain,(
    ! [X70,X71] :
      ( ( ~ m1_subset_1(X71,X70)
        | r2_hidden(X71,X70)
        | v1_xboole_0(X70) )
      & ( ~ r2_hidden(X71,X70)
        | m1_subset_1(X71,X70)
        | v1_xboole_0(X70) )
      & ( ~ m1_subset_1(X71,X70)
        | v1_xboole_0(X71)
        | ~ v1_xboole_0(X70) )
      & ( ~ v1_xboole_0(X71)
        | m1_subset_1(X71,X70)
        | ~ v1_xboole_0(X70) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

fof(c_0_32,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))
    & k4_subset_1(esk2_0,esk3_0,k3_subset_1(esk2_0,esk3_0)) != k2_subset_1(esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_28])])])).

fof(c_0_33,plain,(
    ! [X77] : ~ v1_xboole_0(k1_zfmisc_1(X77)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).

fof(c_0_34,plain,(
    ! [X23,X24] : k3_xboole_0(X23,k2_xboole_0(X23,X24)) = X23 ),
    inference(variable_rename,[status(thm)],[t21_xboole_1])).

cnf(c_0_35,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_36,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_37,plain,(
    ! [X36,X37,X38] : k2_enumset1(X36,X36,X37,X38) = k1_enumset1(X36,X37,X38) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_38,plain,(
    ! [X39,X40,X41,X42] : k3_enumset1(X39,X39,X40,X41,X42) = k2_enumset1(X39,X40,X41,X42) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_39,plain,(
    ! [X43,X44,X45,X46,X47] : k4_enumset1(X43,X43,X44,X45,X46,X47) = k3_enumset1(X43,X44,X45,X46,X47) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_40,plain,(
    ! [X48,X49,X50,X51,X52,X53] : k5_enumset1(X48,X48,X49,X50,X51,X52,X53) = k4_enumset1(X48,X49,X50,X51,X52,X53) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_41,plain,(
    ! [X54,X55,X56,X57,X58,X59,X60] : k6_enumset1(X54,X54,X55,X56,X57,X58,X59,X60) = k5_enumset1(X54,X55,X56,X57,X58,X59,X60) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_42,plain,(
    ! [X61,X62,X63,X64,X65,X66] :
      ( ( ~ r2_hidden(X63,X62)
        | r1_tarski(X63,X61)
        | X62 != k1_zfmisc_1(X61) )
      & ( ~ r1_tarski(X64,X61)
        | r2_hidden(X64,X62)
        | X62 != k1_zfmisc_1(X61) )
      & ( ~ r2_hidden(esk1_2(X65,X66),X66)
        | ~ r1_tarski(esk1_2(X65,X66),X65)
        | X66 = k1_zfmisc_1(X65) )
      & ( r2_hidden(esk1_2(X65,X66),X66)
        | r1_tarski(esk1_2(X65,X66),X65)
        | X66 = k1_zfmisc_1(X65) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

cnf(c_0_43,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_44,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_45,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

fof(c_0_46,plain,(
    ! [X21,X22] : r1_tarski(k3_xboole_0(X21,X22),X21) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

cnf(c_0_47,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_48,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_49,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_50,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_51,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_52,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_53,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_54,plain,
    ( r1_tarski(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_55,negated_conjecture,
    ( r2_hidden(esk3_0,k1_zfmisc_1(esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45])).

fof(c_0_56,plain,(
    ! [X28,X29] : r1_xboole_0(k4_xboole_0(X28,X29),X29) ),
    inference(variable_rename,[status(thm)],[t79_xboole_1])).

fof(c_0_57,plain,(
    ! [X16,X17] : k4_xboole_0(X16,X17) = k5_xboole_0(X16,k3_xboole_0(X16,X17)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_58,plain,(
    ! [X25,X26] :
      ( ~ r1_tarski(X25,X26)
      | k3_xboole_0(X25,X26) = X25 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_59,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_60,plain,
    ( k3_xboole_0(X1,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_48]),c_0_49]),c_0_50]),c_0_51]),c_0_52]),c_0_53])).

cnf(c_0_61,negated_conjecture,
    ( r1_tarski(esk3_0,X1)
    | k1_zfmisc_1(esk2_0) != k1_zfmisc_1(X1) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

fof(c_0_62,plain,(
    ! [X8,X9] : k3_xboole_0(X8,X9) = k3_xboole_0(X9,X8) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_63,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_64,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_65,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_66,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

fof(c_0_67,plain,(
    ! [X33] : k5_xboole_0(X33,X33) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t92_xboole_1])).

cnf(c_0_68,negated_conjecture,
    ( r1_tarski(esk3_0,esk2_0) ),
    inference(er,[status(thm)],[c_0_61])).

cnf(c_0_69,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

fof(c_0_70,plain,(
    ! [X12,X13] :
      ( ( ~ r1_xboole_0(X12,X13)
        | k3_xboole_0(X12,X13) = k1_xboole_0 )
      & ( k3_xboole_0(X12,X13) != k1_xboole_0
        | r1_xboole_0(X12,X13) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

cnf(c_0_71,plain,
    ( r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X2) ),
    inference(rw,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_72,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_73,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

fof(c_0_74,plain,(
    ! [X73,X74] :
      ( ~ m1_subset_1(X74,k1_zfmisc_1(X73))
      | k3_subset_1(X73,X74) = k4_xboole_0(X73,X74) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

fof(c_0_75,plain,(
    ! [X14,X15] : k5_xboole_0(X14,X15) = k4_xboole_0(k2_xboole_0(X14,X15),k3_xboole_0(X14,X15)) ),
    inference(variable_rename,[status(thm)],[l98_xboole_1])).

fof(c_0_76,plain,(
    ! [X18,X19,X20] : k3_xboole_0(k3_xboole_0(X18,X19),X20) = k3_xboole_0(X18,k3_xboole_0(X19,X20)) ),
    inference(variable_rename,[status(thm)],[t16_xboole_1])).

cnf(c_0_77,negated_conjecture,
    ( k3_xboole_0(esk2_0,esk3_0) = esk3_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_68]),c_0_69])).

cnf(c_0_78,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_79,plain,
    ( r1_xboole_0(k1_xboole_0,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_73])).

fof(c_0_80,plain,(
    ! [X10,X11] : k5_xboole_0(X10,X11) = k5_xboole_0(X11,X10) ),
    inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).

fof(c_0_81,plain,(
    ! [X30,X31,X32] : k5_xboole_0(k5_xboole_0(X30,X31),X32) = k5_xboole_0(X30,k5_xboole_0(X31,X32)) ),
    inference(variable_rename,[status(thm)],[t91_xboole_1])).

fof(c_0_82,plain,(
    ! [X78,X79,X80] :
      ( ~ m1_subset_1(X79,k1_zfmisc_1(X78))
      | ~ m1_subset_1(X80,k1_zfmisc_1(X78))
      | k4_subset_1(X78,X79,X80) = k2_xboole_0(X79,X80) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).

fof(c_0_83,plain,(
    ! [X75,X76] :
      ( ~ m1_subset_1(X76,k1_zfmisc_1(X75))
      | m1_subset_1(k3_subset_1(X75,X76),k1_zfmisc_1(X75)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).

cnf(c_0_84,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

cnf(c_0_85,plain,
    ( k5_xboole_0(X1,X2) = k4_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_86,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_76])).

cnf(c_0_87,negated_conjecture,
    ( r1_xboole_0(k5_xboole_0(esk2_0,esk3_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_71,c_0_77])).

cnf(c_0_88,plain,
    ( k3_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_78,c_0_79])).

cnf(c_0_89,plain,
    ( k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_80])).

cnf(c_0_90,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_81])).

fof(c_0_91,plain,(
    ! [X27] : k5_xboole_0(X27,k1_xboole_0) = X27 ),
    inference(variable_rename,[status(thm)],[t5_boole])).

fof(c_0_92,plain,(
    ! [X72] : k2_subset_1(X72) = X72 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

cnf(c_0_93,plain,
    ( k4_subset_1(X2,X1,X3) = k2_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_82])).

cnf(c_0_94,plain,
    ( m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_83])).

cnf(c_0_95,plain,
    ( k3_subset_1(X2,X1) = k5_xboole_0(X2,k3_xboole_0(X2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_84,c_0_64])).

cnf(c_0_96,plain,
    ( k5_xboole_0(X1,X2) = k5_xboole_0(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),k3_xboole_0(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),k3_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_85,c_0_48]),c_0_64]),c_0_49]),c_0_49]),c_0_50]),c_0_50]),c_0_51]),c_0_51]),c_0_52]),c_0_52]),c_0_53]),c_0_53])).

cnf(c_0_97,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,X3)) = k3_xboole_0(X3,k3_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_69,c_0_86])).

cnf(c_0_98,negated_conjecture,
    ( k3_xboole_0(esk3_0,k5_xboole_0(esk2_0,esk3_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_87]),c_0_69])).

cnf(c_0_99,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_69,c_0_88])).

cnf(c_0_100,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,X3)) = k5_xboole_0(X3,k5_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_89,c_0_90])).

cnf(c_0_101,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_91])).

cnf(c_0_102,negated_conjecture,
    ( k4_subset_1(esk2_0,esk3_0,k3_subset_1(esk2_0,esk3_0)) != k2_subset_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_103,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_92])).

cnf(c_0_104,plain,
    ( k4_subset_1(X2,X1,X3) = k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_93,c_0_48]),c_0_49]),c_0_50]),c_0_51]),c_0_52]),c_0_53])).

cnf(c_0_105,negated_conjecture,
    ( m1_subset_1(k3_subset_1(esk2_0,esk3_0),k1_zfmisc_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_94,c_0_44])).

cnf(c_0_106,negated_conjecture,
    ( k3_subset_1(esk2_0,esk3_0) = k5_xboole_0(esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_44]),c_0_77])).

cnf(c_0_107,plain,
    ( k5_xboole_0(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),k3_xboole_0(X1,k3_xboole_0(X2,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))))) = k5_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_96,c_0_69]),c_0_86])).

cnf(c_0_108,negated_conjecture,
    ( k3_xboole_0(esk3_0,k3_xboole_0(k5_xboole_0(esk2_0,esk3_0),X1)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_98]),c_0_99])).

cnf(c_0_109,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_73]),c_0_101])).

cnf(c_0_110,negated_conjecture,
    ( k4_subset_1(esk2_0,esk3_0,k3_subset_1(esk2_0,esk3_0)) != esk2_0 ),
    inference(rw,[status(thm)],[c_0_102,c_0_103])).

cnf(c_0_111,negated_conjecture,
    ( k3_tarski(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,X1)) = k4_subset_1(esk2_0,esk3_0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_104,c_0_44])).

cnf(c_0_112,negated_conjecture,
    ( m1_subset_1(k5_xboole_0(esk2_0,esk3_0),k1_zfmisc_1(esk2_0)) ),
    inference(rw,[status(thm)],[c_0_105,c_0_106])).

cnf(c_0_113,negated_conjecture,
    ( k3_tarski(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k5_xboole_0(esk2_0,esk3_0))) = esk2_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_108]),c_0_101]),c_0_109])).

cnf(c_0_114,negated_conjecture,
    ( k4_subset_1(esk2_0,esk3_0,k5_xboole_0(esk2_0,esk3_0)) != esk2_0 ),
    inference(rw,[status(thm)],[c_0_110,c_0_106])).

cnf(c_0_115,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111,c_0_112]),c_0_113]),c_0_114]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n017.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 11:57:46 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.50/0.70  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_AE_CS_SP_PI_S0a
% 0.50/0.70  # and selection function SelectNegativeLiterals.
% 0.50/0.70  #
% 0.50/0.70  # Preprocessing time       : 0.027 s
% 0.50/0.70  
% 0.50/0.70  # Proof found!
% 0.50/0.70  # SZS status Theorem
% 0.50/0.70  # SZS output start CNFRefutation
% 0.50/0.70  fof(t25_subset_1, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k4_subset_1(X1,X2,k3_subset_1(X1,X2))=k2_subset_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_subset_1)).
% 0.50/0.70  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.50/0.70  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.50/0.70  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 0.50/0.70  fof(fc1_subset_1, axiom, ![X1]:~(v1_xboole_0(k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 0.50/0.70  fof(t21_xboole_1, axiom, ![X1, X2]:k3_xboole_0(X1,k2_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_xboole_1)).
% 0.50/0.70  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.50/0.70  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.50/0.70  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 0.50/0.70  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 0.50/0.70  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 0.50/0.70  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 0.50/0.70  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 0.50/0.70  fof(t79_xboole_1, axiom, ![X1, X2]:r1_xboole_0(k4_xboole_0(X1,X2),X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 0.50/0.70  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.50/0.70  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.50/0.70  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.50/0.70  fof(t92_xboole_1, axiom, ![X1]:k5_xboole_0(X1,X1)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 0.50/0.70  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 0.50/0.70  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 0.50/0.70  fof(l98_xboole_1, axiom, ![X1, X2]:k5_xboole_0(X1,X2)=k4_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l98_xboole_1)).
% 0.50/0.70  fof(t16_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(k3_xboole_0(X1,X2),X3)=k3_xboole_0(X1,k3_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_xboole_1)).
% 0.50/0.70  fof(commutativity_k5_xboole_0, axiom, ![X1, X2]:k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 0.50/0.70  fof(t91_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 0.50/0.70  fof(redefinition_k4_subset_1, axiom, ![X1, X2, X3]:((m1_subset_1(X2,k1_zfmisc_1(X1))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>k4_subset_1(X1,X2,X3)=k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 0.50/0.70  fof(dt_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 0.50/0.70  fof(t5_boole, axiom, ![X1]:k5_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 0.50/0.70  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 0.50/0.70  fof(c_0_28, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k4_subset_1(X1,X2,k3_subset_1(X1,X2))=k2_subset_1(X1))), inference(assume_negation,[status(cth)],[t25_subset_1])).
% 0.50/0.70  fof(c_0_29, plain, ![X68, X69]:k3_tarski(k2_tarski(X68,X69))=k2_xboole_0(X68,X69), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.50/0.70  fof(c_0_30, plain, ![X34, X35]:k1_enumset1(X34,X34,X35)=k2_tarski(X34,X35), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.50/0.70  fof(c_0_31, plain, ![X70, X71]:(((~m1_subset_1(X71,X70)|r2_hidden(X71,X70)|v1_xboole_0(X70))&(~r2_hidden(X71,X70)|m1_subset_1(X71,X70)|v1_xboole_0(X70)))&((~m1_subset_1(X71,X70)|v1_xboole_0(X71)|~v1_xboole_0(X70))&(~v1_xboole_0(X71)|m1_subset_1(X71,X70)|~v1_xboole_0(X70)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 0.50/0.70  fof(c_0_32, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))&k4_subset_1(esk2_0,esk3_0,k3_subset_1(esk2_0,esk3_0))!=k2_subset_1(esk2_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_28])])])).
% 0.50/0.70  fof(c_0_33, plain, ![X77]:~v1_xboole_0(k1_zfmisc_1(X77)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).
% 0.50/0.70  fof(c_0_34, plain, ![X23, X24]:k3_xboole_0(X23,k2_xboole_0(X23,X24))=X23, inference(variable_rename,[status(thm)],[t21_xboole_1])).
% 0.50/0.70  cnf(c_0_35, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.50/0.70  cnf(c_0_36, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.50/0.70  fof(c_0_37, plain, ![X36, X37, X38]:k2_enumset1(X36,X36,X37,X38)=k1_enumset1(X36,X37,X38), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.50/0.70  fof(c_0_38, plain, ![X39, X40, X41, X42]:k3_enumset1(X39,X39,X40,X41,X42)=k2_enumset1(X39,X40,X41,X42), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.50/0.70  fof(c_0_39, plain, ![X43, X44, X45, X46, X47]:k4_enumset1(X43,X43,X44,X45,X46,X47)=k3_enumset1(X43,X44,X45,X46,X47), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.50/0.70  fof(c_0_40, plain, ![X48, X49, X50, X51, X52, X53]:k5_enumset1(X48,X48,X49,X50,X51,X52,X53)=k4_enumset1(X48,X49,X50,X51,X52,X53), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.50/0.70  fof(c_0_41, plain, ![X54, X55, X56, X57, X58, X59, X60]:k6_enumset1(X54,X54,X55,X56,X57,X58,X59,X60)=k5_enumset1(X54,X55,X56,X57,X58,X59,X60), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.50/0.70  fof(c_0_42, plain, ![X61, X62, X63, X64, X65, X66]:(((~r2_hidden(X63,X62)|r1_tarski(X63,X61)|X62!=k1_zfmisc_1(X61))&(~r1_tarski(X64,X61)|r2_hidden(X64,X62)|X62!=k1_zfmisc_1(X61)))&((~r2_hidden(esk1_2(X65,X66),X66)|~r1_tarski(esk1_2(X65,X66),X65)|X66=k1_zfmisc_1(X65))&(r2_hidden(esk1_2(X65,X66),X66)|r1_tarski(esk1_2(X65,X66),X65)|X66=k1_zfmisc_1(X65)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 0.50/0.70  cnf(c_0_43, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.50/0.70  cnf(c_0_44, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.50/0.70  cnf(c_0_45, plain, (~v1_xboole_0(k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.50/0.70  fof(c_0_46, plain, ![X21, X22]:r1_tarski(k3_xboole_0(X21,X22),X21), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 0.50/0.70  cnf(c_0_47, plain, (k3_xboole_0(X1,k2_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.50/0.70  cnf(c_0_48, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_35, c_0_36])).
% 0.50/0.70  cnf(c_0_49, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.50/0.70  cnf(c_0_50, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.50/0.70  cnf(c_0_51, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.50/0.70  cnf(c_0_52, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.50/0.70  cnf(c_0_53, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.50/0.70  cnf(c_0_54, plain, (r1_tarski(X1,X3)|~r2_hidden(X1,X2)|X2!=k1_zfmisc_1(X3)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.50/0.70  cnf(c_0_55, negated_conjecture, (r2_hidden(esk3_0,k1_zfmisc_1(esk2_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_45])).
% 0.50/0.70  fof(c_0_56, plain, ![X28, X29]:r1_xboole_0(k4_xboole_0(X28,X29),X29), inference(variable_rename,[status(thm)],[t79_xboole_1])).
% 0.50/0.70  fof(c_0_57, plain, ![X16, X17]:k4_xboole_0(X16,X17)=k5_xboole_0(X16,k3_xboole_0(X16,X17)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.50/0.70  fof(c_0_58, plain, ![X25, X26]:(~r1_tarski(X25,X26)|k3_xboole_0(X25,X26)=X25), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.50/0.70  cnf(c_0_59, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.50/0.70  cnf(c_0_60, plain, (k3_xboole_0(X1,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47, c_0_48]), c_0_49]), c_0_50]), c_0_51]), c_0_52]), c_0_53])).
% 0.50/0.70  cnf(c_0_61, negated_conjecture, (r1_tarski(esk3_0,X1)|k1_zfmisc_1(esk2_0)!=k1_zfmisc_1(X1)), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.50/0.70  fof(c_0_62, plain, ![X8, X9]:k3_xboole_0(X8,X9)=k3_xboole_0(X9,X8), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.50/0.70  cnf(c_0_63, plain, (r1_xboole_0(k4_xboole_0(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.50/0.70  cnf(c_0_64, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.50/0.70  cnf(c_0_65, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.50/0.70  cnf(c_0_66, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 0.50/0.70  fof(c_0_67, plain, ![X33]:k5_xboole_0(X33,X33)=k1_xboole_0, inference(variable_rename,[status(thm)],[t92_xboole_1])).
% 0.50/0.70  cnf(c_0_68, negated_conjecture, (r1_tarski(esk3_0,esk2_0)), inference(er,[status(thm)],[c_0_61])).
% 0.50/0.70  cnf(c_0_69, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.50/0.70  fof(c_0_70, plain, ![X12, X13]:((~r1_xboole_0(X12,X13)|k3_xboole_0(X12,X13)=k1_xboole_0)&(k3_xboole_0(X12,X13)!=k1_xboole_0|r1_xboole_0(X12,X13))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 0.50/0.70  cnf(c_0_71, plain, (r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X2)), inference(rw,[status(thm)],[c_0_63, c_0_64])).
% 0.50/0.70  cnf(c_0_72, plain, (k3_xboole_0(X1,X1)=X1), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 0.50/0.70  cnf(c_0_73, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.50/0.70  fof(c_0_74, plain, ![X73, X74]:(~m1_subset_1(X74,k1_zfmisc_1(X73))|k3_subset_1(X73,X74)=k4_xboole_0(X73,X74)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 0.50/0.70  fof(c_0_75, plain, ![X14, X15]:k5_xboole_0(X14,X15)=k4_xboole_0(k2_xboole_0(X14,X15),k3_xboole_0(X14,X15)), inference(variable_rename,[status(thm)],[l98_xboole_1])).
% 0.50/0.70  fof(c_0_76, plain, ![X18, X19, X20]:k3_xboole_0(k3_xboole_0(X18,X19),X20)=k3_xboole_0(X18,k3_xboole_0(X19,X20)), inference(variable_rename,[status(thm)],[t16_xboole_1])).
% 0.50/0.70  cnf(c_0_77, negated_conjecture, (k3_xboole_0(esk2_0,esk3_0)=esk3_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_68]), c_0_69])).
% 0.50/0.70  cnf(c_0_78, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_70])).
% 0.50/0.70  cnf(c_0_79, plain, (r1_xboole_0(k1_xboole_0,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_73])).
% 0.50/0.70  fof(c_0_80, plain, ![X10, X11]:k5_xboole_0(X10,X11)=k5_xboole_0(X11,X10), inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).
% 0.50/0.70  fof(c_0_81, plain, ![X30, X31, X32]:k5_xboole_0(k5_xboole_0(X30,X31),X32)=k5_xboole_0(X30,k5_xboole_0(X31,X32)), inference(variable_rename,[status(thm)],[t91_xboole_1])).
% 0.50/0.70  fof(c_0_82, plain, ![X78, X79, X80]:(~m1_subset_1(X79,k1_zfmisc_1(X78))|~m1_subset_1(X80,k1_zfmisc_1(X78))|k4_subset_1(X78,X79,X80)=k2_xboole_0(X79,X80)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).
% 0.50/0.70  fof(c_0_83, plain, ![X75, X76]:(~m1_subset_1(X76,k1_zfmisc_1(X75))|m1_subset_1(k3_subset_1(X75,X76),k1_zfmisc_1(X75))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).
% 0.50/0.70  cnf(c_0_84, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_74])).
% 0.50/0.70  cnf(c_0_85, plain, (k5_xboole_0(X1,X2)=k4_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_75])).
% 0.50/0.70  cnf(c_0_86, plain, (k3_xboole_0(k3_xboole_0(X1,X2),X3)=k3_xboole_0(X1,k3_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_76])).
% 0.50/0.70  cnf(c_0_87, negated_conjecture, (r1_xboole_0(k5_xboole_0(esk2_0,esk3_0),esk3_0)), inference(spm,[status(thm)],[c_0_71, c_0_77])).
% 0.50/0.70  cnf(c_0_88, plain, (k3_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_78, c_0_79])).
% 0.50/0.70  cnf(c_0_89, plain, (k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_80])).
% 0.50/0.70  cnf(c_0_90, plain, (k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_81])).
% 0.50/0.70  fof(c_0_91, plain, ![X27]:k5_xboole_0(X27,k1_xboole_0)=X27, inference(variable_rename,[status(thm)],[t5_boole])).
% 0.50/0.70  fof(c_0_92, plain, ![X72]:k2_subset_1(X72)=X72, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 0.50/0.70  cnf(c_0_93, plain, (k4_subset_1(X2,X1,X3)=k2_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_82])).
% 0.50/0.70  cnf(c_0_94, plain, (m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_83])).
% 0.50/0.70  cnf(c_0_95, plain, (k3_subset_1(X2,X1)=k5_xboole_0(X2,k3_xboole_0(X2,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_84, c_0_64])).
% 0.50/0.70  cnf(c_0_96, plain, (k5_xboole_0(X1,X2)=k5_xboole_0(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),k3_xboole_0(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),k3_xboole_0(X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_85, c_0_48]), c_0_64]), c_0_49]), c_0_49]), c_0_50]), c_0_50]), c_0_51]), c_0_51]), c_0_52]), c_0_52]), c_0_53]), c_0_53])).
% 0.50/0.70  cnf(c_0_97, plain, (k3_xboole_0(X1,k3_xboole_0(X2,X3))=k3_xboole_0(X3,k3_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_69, c_0_86])).
% 0.50/0.70  cnf(c_0_98, negated_conjecture, (k3_xboole_0(esk3_0,k5_xboole_0(esk2_0,esk3_0))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_87]), c_0_69])).
% 0.50/0.70  cnf(c_0_99, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_69, c_0_88])).
% 0.50/0.70  cnf(c_0_100, plain, (k5_xboole_0(X1,k5_xboole_0(X2,X3))=k5_xboole_0(X3,k5_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_89, c_0_90])).
% 0.50/0.70  cnf(c_0_101, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_91])).
% 0.50/0.70  cnf(c_0_102, negated_conjecture, (k4_subset_1(esk2_0,esk3_0,k3_subset_1(esk2_0,esk3_0))!=k2_subset_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.50/0.70  cnf(c_0_103, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_92])).
% 0.50/0.70  cnf(c_0_104, plain, (k4_subset_1(X2,X1,X3)=k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X3))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_93, c_0_48]), c_0_49]), c_0_50]), c_0_51]), c_0_52]), c_0_53])).
% 0.50/0.70  cnf(c_0_105, negated_conjecture, (m1_subset_1(k3_subset_1(esk2_0,esk3_0),k1_zfmisc_1(esk2_0))), inference(spm,[status(thm)],[c_0_94, c_0_44])).
% 0.50/0.70  cnf(c_0_106, negated_conjecture, (k3_subset_1(esk2_0,esk3_0)=k5_xboole_0(esk2_0,esk3_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_44]), c_0_77])).
% 0.50/0.70  cnf(c_0_107, plain, (k5_xboole_0(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),k3_xboole_0(X1,k3_xboole_0(X2,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))))=k5_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_96, c_0_69]), c_0_86])).
% 0.50/0.70  cnf(c_0_108, negated_conjecture, (k3_xboole_0(esk3_0,k3_xboole_0(k5_xboole_0(esk2_0,esk3_0),X1))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97, c_0_98]), c_0_99])).
% 0.50/0.70  cnf(c_0_109, plain, (k5_xboole_0(X1,k5_xboole_0(X2,X1))=X2), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_73]), c_0_101])).
% 0.50/0.70  cnf(c_0_110, negated_conjecture, (k4_subset_1(esk2_0,esk3_0,k3_subset_1(esk2_0,esk3_0))!=esk2_0), inference(rw,[status(thm)],[c_0_102, c_0_103])).
% 0.50/0.70  cnf(c_0_111, negated_conjecture, (k3_tarski(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,X1))=k4_subset_1(esk2_0,esk3_0,X1)|~m1_subset_1(X1,k1_zfmisc_1(esk2_0))), inference(spm,[status(thm)],[c_0_104, c_0_44])).
% 0.50/0.70  cnf(c_0_112, negated_conjecture, (m1_subset_1(k5_xboole_0(esk2_0,esk3_0),k1_zfmisc_1(esk2_0))), inference(rw,[status(thm)],[c_0_105, c_0_106])).
% 0.50/0.70  cnf(c_0_113, negated_conjecture, (k3_tarski(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k5_xboole_0(esk2_0,esk3_0)))=esk2_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107, c_0_108]), c_0_101]), c_0_109])).
% 0.50/0.70  cnf(c_0_114, negated_conjecture, (k4_subset_1(esk2_0,esk3_0,k5_xboole_0(esk2_0,esk3_0))!=esk2_0), inference(rw,[status(thm)],[c_0_110, c_0_106])).
% 0.50/0.70  cnf(c_0_115, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111, c_0_112]), c_0_113]), c_0_114]), ['proof']).
% 0.50/0.70  # SZS output end CNFRefutation
% 0.50/0.70  # Proof object total steps             : 116
% 0.50/0.70  # Proof object clause steps            : 59
% 0.50/0.70  # Proof object formula steps           : 57
% 0.50/0.70  # Proof object conjectures             : 20
% 0.50/0.70  # Proof object clause conjectures      : 17
% 0.50/0.70  # Proof object formula conjectures     : 3
% 0.50/0.70  # Proof object initial clauses used    : 29
% 0.50/0.70  # Proof object initial formulas used   : 28
% 0.50/0.70  # Proof object generating inferences   : 20
% 0.50/0.70  # Proof object simplifying inferences  : 43
% 0.50/0.70  # Training examples: 0 positive, 0 negative
% 0.50/0.70  # Parsed axioms                        : 28
% 0.50/0.70  # Removed by relevancy pruning/SinE    : 0
% 0.50/0.70  # Initial clauses                      : 36
% 0.50/0.70  # Removed in clause preprocessing      : 9
% 0.50/0.70  # Initial clauses in saturation        : 27
% 0.50/0.70  # Processed clauses                    : 4205
% 0.50/0.70  # ...of these trivial                  : 774
% 0.50/0.70  # ...subsumed                          : 2295
% 0.50/0.70  # ...remaining for further processing  : 1135
% 0.50/0.70  # Other redundant clauses eliminated   : 0
% 0.50/0.70  # Clauses deleted for lack of memory   : 0
% 0.50/0.70  # Backward-subsumed                    : 30
% 0.50/0.70  # Backward-rewritten                   : 384
% 0.50/0.70  # Generated clauses                    : 30499
% 0.50/0.70  # ...of the previous two non-trivial   : 18806
% 0.50/0.70  # Contextual simplify-reflections      : 0
% 0.50/0.70  # Paramodulations                      : 30281
% 0.50/0.70  # Factorizations                       : 4
% 0.50/0.70  # Equation resolutions                 : 214
% 0.50/0.70  # Propositional unsat checks           : 0
% 0.50/0.70  #    Propositional check models        : 0
% 0.50/0.70  #    Propositional check unsatisfiable : 0
% 0.50/0.70  #    Propositional clauses             : 0
% 0.50/0.70  #    Propositional clauses after purity: 0
% 0.50/0.70  #    Propositional unsat core size     : 0
% 0.50/0.70  #    Propositional preprocessing time  : 0.000
% 0.50/0.70  #    Propositional encoding time       : 0.000
% 0.50/0.70  #    Propositional solver time         : 0.000
% 0.50/0.70  #    Success case prop preproc time    : 0.000
% 0.50/0.70  #    Success case prop encoding time   : 0.000
% 0.50/0.70  #    Success case prop solver time     : 0.000
% 0.50/0.70  # Current number of processed clauses  : 721
% 0.50/0.70  #    Positive orientable unit clauses  : 384
% 0.50/0.70  #    Positive unorientable unit clauses: 7
% 0.50/0.70  #    Negative unit clauses             : 2
% 0.50/0.70  #    Non-unit-clauses                  : 328
% 0.50/0.70  # Current number of unprocessed clauses: 14158
% 0.50/0.70  # ...number of literals in the above   : 18096
% 0.50/0.70  # Current number of archived formulas  : 0
% 0.50/0.70  # Current number of archived clauses   : 423
% 0.50/0.70  # Clause-clause subsumption calls (NU) : 52350
% 0.50/0.70  # Rec. Clause-clause subsumption calls : 52297
% 0.50/0.70  # Non-unit clause-clause subsumptions  : 2053
% 0.50/0.70  # Unit Clause-clause subsumption calls : 1109
% 0.50/0.70  # Rewrite failures with RHS unbound    : 0
% 0.50/0.70  # BW rewrite match attempts            : 2856
% 0.50/0.70  # BW rewrite match successes           : 172
% 0.50/0.70  # Condensation attempts                : 0
% 0.50/0.70  # Condensation successes               : 0
% 0.50/0.70  # Termbank termtop insertions          : 455856
% 0.50/0.71  
% 0.50/0.71  # -------------------------------------------------
% 0.50/0.71  # User time                : 0.356 s
% 0.50/0.71  # System time              : 0.011 s
% 0.50/0.71  # Total time               : 0.367 s
% 0.50/0.71  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------
