%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:45:19 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 247 expanded)
%              Number of clauses        :   57 ( 107 expanded)
%              Number of leaves         :   27 (  67 expanded)
%              Depth                    :   12
%              Number of atoms          :  176 ( 429 expanded)
%              Number of equality atoms :   91 ( 211 expanded)
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

fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

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

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(t94_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

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

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(t5_boole,axiom,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(commutativity_k5_xboole_0,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(redefinition_k4_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => k4_subset_1(X1,X2,X3) = k2_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(t91_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(t112_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2)) = k3_xboole_0(k5_xboole_0(X1,X3),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_xboole_1)).

fof(c_0_27,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X1))
       => k4_subset_1(X1,X2,k3_subset_1(X1,X2)) = k2_subset_1(X1) ) ),
    inference(assume_negation,[status(cth)],[t25_subset_1])).

fof(c_0_28,plain,(
    ! [X62,X63,X64,X65,X66,X67] :
      ( ( ~ r2_hidden(X64,X63)
        | r1_tarski(X64,X62)
        | X63 != k1_zfmisc_1(X62) )
      & ( ~ r1_tarski(X65,X62)
        | r2_hidden(X65,X63)
        | X63 != k1_zfmisc_1(X62) )
      & ( ~ r2_hidden(esk2_2(X66,X67),X67)
        | ~ r1_tarski(esk2_2(X66,X67),X66)
        | X67 = k1_zfmisc_1(X66) )
      & ( r2_hidden(esk2_2(X66,X67),X67)
        | r1_tarski(esk2_2(X66,X67),X66)
        | X67 = k1_zfmisc_1(X66) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

fof(c_0_29,plain,(
    ! [X71,X72] :
      ( ( ~ m1_subset_1(X72,X71)
        | r2_hidden(X72,X71)
        | v1_xboole_0(X71) )
      & ( ~ r2_hidden(X72,X71)
        | m1_subset_1(X72,X71)
        | v1_xboole_0(X71) )
      & ( ~ m1_subset_1(X72,X71)
        | v1_xboole_0(X72)
        | ~ v1_xboole_0(X71) )
      & ( ~ v1_xboole_0(X72)
        | m1_subset_1(X72,X71)
        | ~ v1_xboole_0(X71) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

fof(c_0_30,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(esk3_0))
    & k4_subset_1(esk3_0,esk4_0,k3_subset_1(esk3_0,esk4_0)) != k2_subset_1(esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_27])])])).

fof(c_0_31,plain,(
    ! [X76] : ~ v1_xboole_0(k1_zfmisc_1(X76)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).

cnf(c_0_32,plain,
    ( r1_tarski(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_33,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_34,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_35,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_36,plain,(
    ! [X22,X23] :
      ( ~ r1_tarski(X22,X23)
      | k3_xboole_0(X22,X23) = X22 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_37,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(er,[status(thm)],[c_0_32])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(esk4_0,k1_zfmisc_1(esk3_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35])).

fof(c_0_39,plain,(
    ! [X25,X26] : r1_tarski(k4_xboole_0(X25,X26),X25) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

fof(c_0_40,plain,(
    ! [X17,X18] : k4_xboole_0(X17,X18) = k5_xboole_0(X17,k3_xboole_0(X17,X18)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_41,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_42,negated_conjecture,
    ( r1_tarski(esk4_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

fof(c_0_43,plain,(
    ! [X8,X9] : k3_xboole_0(X8,X9) = k3_xboole_0(X9,X8) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_44,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_45,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_46,negated_conjecture,
    ( k3_xboole_0(esk4_0,esk3_0) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_47,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

fof(c_0_48,plain,(
    ! [X69,X70] : k3_tarski(k2_tarski(X69,X70)) = k2_xboole_0(X69,X70) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_49,plain,(
    ! [X35,X36] : k1_enumset1(X35,X35,X36) = k2_tarski(X35,X36) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_50,plain,(
    ! [X27,X28] : k4_xboole_0(X27,k4_xboole_0(X27,X28)) = k3_xboole_0(X27,X28) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_51,plain,(
    ! [X12,X13,X14] :
      ( ( ~ v1_xboole_0(X12)
        | ~ r2_hidden(X13,X12) )
      & ( r2_hidden(esk1_1(X14),X14)
        | v1_xboole_0(X14) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_52,plain,
    ( r2_hidden(X1,X3)
    | ~ r1_tarski(X1,X2)
    | X3 != k1_zfmisc_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_53,plain,
    ( r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X1) ),
    inference(rw,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_54,negated_conjecture,
    ( k3_xboole_0(esk3_0,esk4_0) = esk4_0 ),
    inference(rw,[status(thm)],[c_0_46,c_0_47])).

fof(c_0_55,plain,(
    ! [X33,X34] : k2_xboole_0(X33,X34) = k5_xboole_0(k5_xboole_0(X33,X34),k3_xboole_0(X33,X34)) ),
    inference(variable_rename,[status(thm)],[t94_xboole_1])).

cnf(c_0_56,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_57,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

fof(c_0_58,plain,(
    ! [X37,X38,X39] : k2_enumset1(X37,X37,X38,X39) = k1_enumset1(X37,X38,X39) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_59,plain,(
    ! [X40,X41,X42,X43] : k3_enumset1(X40,X40,X41,X42,X43) = k2_enumset1(X40,X41,X42,X43) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_60,plain,(
    ! [X44,X45,X46,X47,X48] : k4_enumset1(X44,X44,X45,X46,X47,X48) = k3_enumset1(X44,X45,X46,X47,X48) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_61,plain,(
    ! [X49,X50,X51,X52,X53,X54] : k5_enumset1(X49,X49,X50,X51,X52,X53,X54) = k4_enumset1(X49,X50,X51,X52,X53,X54) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_62,plain,(
    ! [X55,X56,X57,X58,X59,X60,X61] : k6_enumset1(X55,X55,X56,X57,X58,X59,X60,X61) = k5_enumset1(X55,X56,X57,X58,X59,X60,X61) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

cnf(c_0_63,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

fof(c_0_64,plain,(
    ! [X24] : k3_xboole_0(X24,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

fof(c_0_65,plain,(
    ! [X29] : k5_xboole_0(X29,k1_xboole_0) = X29 ),
    inference(variable_rename,[status(thm)],[t5_boole])).

fof(c_0_66,plain,(
    ! [X16] : k3_xboole_0(X16,X16) = X16 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

fof(c_0_67,plain,(
    ! [X10,X11] : k5_xboole_0(X10,X11) = k5_xboole_0(X11,X10) ),
    inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).

fof(c_0_68,plain,(
    ! [X74,X75] :
      ( ~ m1_subset_1(X75,k1_zfmisc_1(X74))
      | k3_subset_1(X74,X75) = k4_xboole_0(X74,X75) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

fof(c_0_69,plain,(
    ! [X77,X78,X79] :
      ( ~ m1_subset_1(X78,k1_zfmisc_1(X77))
      | ~ m1_subset_1(X79,k1_zfmisc_1(X77))
      | k4_subset_1(X77,X78,X79) = k2_xboole_0(X78,X79) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).

cnf(c_0_70,plain,
    ( m1_subset_1(X1,X2)
    | v1_xboole_0(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_71,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_72,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(er,[status(thm)],[c_0_52])).

cnf(c_0_73,negated_conjecture,
    ( r1_tarski(k5_xboole_0(esk3_0,esk4_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_74,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_75,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_76,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_77,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_78,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_79,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_80,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

fof(c_0_81,plain,(
    ! [X30,X31,X32] : k5_xboole_0(k5_xboole_0(X30,X31),X32) = k5_xboole_0(X30,k5_xboole_0(X31,X32)) ),
    inference(variable_rename,[status(thm)],[t91_xboole_1])).

cnf(c_0_82,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_63,c_0_45]),c_0_45])).

cnf(c_0_83,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_84,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_85,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_86,plain,
    ( k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

fof(c_0_87,plain,(
    ! [X73] : k2_subset_1(X73) = X73 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

cnf(c_0_88,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_89,plain,
    ( k4_subset_1(X2,X1,X3) = k2_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_90,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(csr,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_91,negated_conjecture,
    ( r2_hidden(k5_xboole_0(esk3_0,esk4_0),k1_zfmisc_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_92,plain,
    ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) = k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_74,c_0_75]),c_0_76]),c_0_77]),c_0_78]),c_0_79]),c_0_80])).

cnf(c_0_93,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_81])).

fof(c_0_94,plain,(
    ! [X19,X20,X21] : k5_xboole_0(k3_xboole_0(X19,X20),k3_xboole_0(X21,X20)) = k3_xboole_0(k5_xboole_0(X19,X21),X20) ),
    inference(variable_rename,[status(thm)],[t112_xboole_1])).

cnf(c_0_95,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_84]),c_0_85])).

cnf(c_0_96,plain,
    ( k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_84,c_0_86])).

cnf(c_0_97,negated_conjecture,
    ( k4_subset_1(esk3_0,esk4_0,k3_subset_1(esk3_0,esk4_0)) != k2_subset_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_98,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_87])).

cnf(c_0_99,plain,
    ( k3_subset_1(X2,X1) = k5_xboole_0(X2,k3_xboole_0(X2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_88,c_0_45])).

cnf(c_0_100,plain,
    ( k4_subset_1(X2,X1,X3) = k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_89,c_0_75]),c_0_76]),c_0_77]),c_0_78]),c_0_79]),c_0_80])).

cnf(c_0_101,negated_conjecture,
    ( m1_subset_1(k5_xboole_0(esk3_0,esk4_0),k1_zfmisc_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_90,c_0_91])).

cnf(c_0_102,plain,
    ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_92,c_0_93])).

cnf(c_0_103,plain,
    ( k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2)) = k3_xboole_0(k5_xboole_0(X1,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_94])).

cnf(c_0_104,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,X2)) = X2 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_95]),c_0_96])).

cnf(c_0_105,negated_conjecture,
    ( k4_subset_1(esk3_0,esk4_0,k3_subset_1(esk3_0,esk4_0)) != esk3_0 ),
    inference(rw,[status(thm)],[c_0_97,c_0_98])).

cnf(c_0_106,negated_conjecture,
    ( k3_subset_1(esk3_0,esk4_0) = k5_xboole_0(esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_34]),c_0_54])).

cnf(c_0_107,negated_conjecture,
    ( k4_subset_1(esk3_0,X1,k5_xboole_0(esk3_0,esk4_0)) = k5_xboole_0(X1,k5_xboole_0(esk3_0,k5_xboole_0(esk4_0,k3_xboole_0(X1,k5_xboole_0(esk3_0,esk4_0)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk3_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_101]),c_0_102]),c_0_93])).

cnf(c_0_108,negated_conjecture,
    ( k3_xboole_0(esk4_0,k5_xboole_0(esk3_0,X1)) = k5_xboole_0(esk4_0,k3_xboole_0(X1,esk4_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_54]),c_0_47])).

cnf(c_0_109,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2 ),
    inference(spm,[status(thm)],[c_0_104,c_0_86])).

cnf(c_0_110,negated_conjecture,
    ( k4_subset_1(esk3_0,esk4_0,k5_xboole_0(esk3_0,esk4_0)) != esk3_0 ),
    inference(rw,[status(thm)],[c_0_105,c_0_106])).

cnf(c_0_111,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_34]),c_0_108]),c_0_85]),c_0_95]),c_0_84]),c_0_109]),c_0_110]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:00:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.41  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S054N
% 0.19/0.41  # and selection function GSelectMinInfpos.
% 0.19/0.41  #
% 0.19/0.41  # Preprocessing time       : 0.014 s
% 0.19/0.41  # Presaturation interreduction done
% 0.19/0.41  
% 0.19/0.41  # Proof found!
% 0.19/0.41  # SZS status Theorem
% 0.19/0.41  # SZS output start CNFRefutation
% 0.19/0.41  fof(t25_subset_1, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k4_subset_1(X1,X2,k3_subset_1(X1,X2))=k2_subset_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_subset_1)).
% 0.19/0.41  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 0.19/0.41  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 0.19/0.41  fof(fc1_subset_1, axiom, ![X1]:~(v1_xboole_0(k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 0.19/0.41  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.19/0.41  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.19/0.41  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.19/0.41  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.19/0.41  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.19/0.41  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.19/0.41  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.19/0.41  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.19/0.41  fof(t94_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_xboole_1)).
% 0.19/0.41  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.19/0.41  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.19/0.41  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 0.19/0.41  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 0.19/0.41  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 0.19/0.41  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 0.19/0.41  fof(t5_boole, axiom, ![X1]:k5_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 0.19/0.41  fof(idempotence_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 0.19/0.41  fof(commutativity_k5_xboole_0, axiom, ![X1, X2]:k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 0.19/0.41  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 0.19/0.41  fof(redefinition_k4_subset_1, axiom, ![X1, X2, X3]:((m1_subset_1(X2,k1_zfmisc_1(X1))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>k4_subset_1(X1,X2,X3)=k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 0.19/0.41  fof(t91_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 0.19/0.41  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 0.19/0.41  fof(t112_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2))=k3_xboole_0(k5_xboole_0(X1,X3),X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t112_xboole_1)).
% 0.19/0.41  fof(c_0_27, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k4_subset_1(X1,X2,k3_subset_1(X1,X2))=k2_subset_1(X1))), inference(assume_negation,[status(cth)],[t25_subset_1])).
% 0.19/0.41  fof(c_0_28, plain, ![X62, X63, X64, X65, X66, X67]:(((~r2_hidden(X64,X63)|r1_tarski(X64,X62)|X63!=k1_zfmisc_1(X62))&(~r1_tarski(X65,X62)|r2_hidden(X65,X63)|X63!=k1_zfmisc_1(X62)))&((~r2_hidden(esk2_2(X66,X67),X67)|~r1_tarski(esk2_2(X66,X67),X66)|X67=k1_zfmisc_1(X66))&(r2_hidden(esk2_2(X66,X67),X67)|r1_tarski(esk2_2(X66,X67),X66)|X67=k1_zfmisc_1(X66)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 0.19/0.41  fof(c_0_29, plain, ![X71, X72]:(((~m1_subset_1(X72,X71)|r2_hidden(X72,X71)|v1_xboole_0(X71))&(~r2_hidden(X72,X71)|m1_subset_1(X72,X71)|v1_xboole_0(X71)))&((~m1_subset_1(X72,X71)|v1_xboole_0(X72)|~v1_xboole_0(X71))&(~v1_xboole_0(X72)|m1_subset_1(X72,X71)|~v1_xboole_0(X71)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 0.19/0.41  fof(c_0_30, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(esk3_0))&k4_subset_1(esk3_0,esk4_0,k3_subset_1(esk3_0,esk4_0))!=k2_subset_1(esk3_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_27])])])).
% 0.19/0.41  fof(c_0_31, plain, ![X76]:~v1_xboole_0(k1_zfmisc_1(X76)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).
% 0.19/0.41  cnf(c_0_32, plain, (r1_tarski(X1,X3)|~r2_hidden(X1,X2)|X2!=k1_zfmisc_1(X3)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.41  cnf(c_0_33, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.41  cnf(c_0_34, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.41  cnf(c_0_35, plain, (~v1_xboole_0(k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.41  fof(c_0_36, plain, ![X22, X23]:(~r1_tarski(X22,X23)|k3_xboole_0(X22,X23)=X22), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.19/0.41  cnf(c_0_37, plain, (r1_tarski(X1,X2)|~r2_hidden(X1,k1_zfmisc_1(X2))), inference(er,[status(thm)],[c_0_32])).
% 0.19/0.41  cnf(c_0_38, negated_conjecture, (r2_hidden(esk4_0,k1_zfmisc_1(esk3_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35])).
% 0.19/0.41  fof(c_0_39, plain, ![X25, X26]:r1_tarski(k4_xboole_0(X25,X26),X25), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.19/0.41  fof(c_0_40, plain, ![X17, X18]:k4_xboole_0(X17,X18)=k5_xboole_0(X17,k3_xboole_0(X17,X18)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.19/0.41  cnf(c_0_41, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.19/0.41  cnf(c_0_42, negated_conjecture, (r1_tarski(esk4_0,esk3_0)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.19/0.41  fof(c_0_43, plain, ![X8, X9]:k3_xboole_0(X8,X9)=k3_xboole_0(X9,X8), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.19/0.41  cnf(c_0_44, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.19/0.41  cnf(c_0_45, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.19/0.41  cnf(c_0_46, negated_conjecture, (k3_xboole_0(esk4_0,esk3_0)=esk4_0), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.19/0.41  cnf(c_0_47, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.19/0.41  fof(c_0_48, plain, ![X69, X70]:k3_tarski(k2_tarski(X69,X70))=k2_xboole_0(X69,X70), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.19/0.41  fof(c_0_49, plain, ![X35, X36]:k1_enumset1(X35,X35,X36)=k2_tarski(X35,X36), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.19/0.41  fof(c_0_50, plain, ![X27, X28]:k4_xboole_0(X27,k4_xboole_0(X27,X28))=k3_xboole_0(X27,X28), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.19/0.41  fof(c_0_51, plain, ![X12, X13, X14]:((~v1_xboole_0(X12)|~r2_hidden(X13,X12))&(r2_hidden(esk1_1(X14),X14)|v1_xboole_0(X14))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.19/0.41  cnf(c_0_52, plain, (r2_hidden(X1,X3)|~r1_tarski(X1,X2)|X3!=k1_zfmisc_1(X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.41  cnf(c_0_53, plain, (r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X1)), inference(rw,[status(thm)],[c_0_44, c_0_45])).
% 0.19/0.41  cnf(c_0_54, negated_conjecture, (k3_xboole_0(esk3_0,esk4_0)=esk4_0), inference(rw,[status(thm)],[c_0_46, c_0_47])).
% 0.19/0.41  fof(c_0_55, plain, ![X33, X34]:k2_xboole_0(X33,X34)=k5_xboole_0(k5_xboole_0(X33,X34),k3_xboole_0(X33,X34)), inference(variable_rename,[status(thm)],[t94_xboole_1])).
% 0.19/0.41  cnf(c_0_56, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.19/0.41  cnf(c_0_57, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.19/0.41  fof(c_0_58, plain, ![X37, X38, X39]:k2_enumset1(X37,X37,X38,X39)=k1_enumset1(X37,X38,X39), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.19/0.41  fof(c_0_59, plain, ![X40, X41, X42, X43]:k3_enumset1(X40,X40,X41,X42,X43)=k2_enumset1(X40,X41,X42,X43), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.19/0.41  fof(c_0_60, plain, ![X44, X45, X46, X47, X48]:k4_enumset1(X44,X44,X45,X46,X47,X48)=k3_enumset1(X44,X45,X46,X47,X48), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.19/0.41  fof(c_0_61, plain, ![X49, X50, X51, X52, X53, X54]:k5_enumset1(X49,X49,X50,X51,X52,X53,X54)=k4_enumset1(X49,X50,X51,X52,X53,X54), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.19/0.41  fof(c_0_62, plain, ![X55, X56, X57, X58, X59, X60, X61]:k6_enumset1(X55,X55,X56,X57,X58,X59,X60,X61)=k5_enumset1(X55,X56,X57,X58,X59,X60,X61), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.19/0.41  cnf(c_0_63, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.19/0.41  fof(c_0_64, plain, ![X24]:k3_xboole_0(X24,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 0.19/0.41  fof(c_0_65, plain, ![X29]:k5_xboole_0(X29,k1_xboole_0)=X29, inference(variable_rename,[status(thm)],[t5_boole])).
% 0.19/0.41  fof(c_0_66, plain, ![X16]:k3_xboole_0(X16,X16)=X16, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).
% 0.19/0.41  fof(c_0_67, plain, ![X10, X11]:k5_xboole_0(X10,X11)=k5_xboole_0(X11,X10), inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).
% 0.19/0.41  fof(c_0_68, plain, ![X74, X75]:(~m1_subset_1(X75,k1_zfmisc_1(X74))|k3_subset_1(X74,X75)=k4_xboole_0(X74,X75)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 0.19/0.41  fof(c_0_69, plain, ![X77, X78, X79]:(~m1_subset_1(X78,k1_zfmisc_1(X77))|~m1_subset_1(X79,k1_zfmisc_1(X77))|k4_subset_1(X77,X78,X79)=k2_xboole_0(X78,X79)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).
% 0.19/0.41  cnf(c_0_70, plain, (m1_subset_1(X1,X2)|v1_xboole_0(X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.41  cnf(c_0_71, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.19/0.41  cnf(c_0_72, plain, (r2_hidden(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(er,[status(thm)],[c_0_52])).
% 0.19/0.41  cnf(c_0_73, negated_conjecture, (r1_tarski(k5_xboole_0(esk3_0,esk4_0),esk3_0)), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.19/0.41  cnf(c_0_74, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.19/0.41  cnf(c_0_75, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_56, c_0_57])).
% 0.19/0.41  cnf(c_0_76, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.19/0.41  cnf(c_0_77, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.19/0.41  cnf(c_0_78, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.19/0.41  cnf(c_0_79, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.19/0.41  cnf(c_0_80, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.19/0.41  fof(c_0_81, plain, ![X30, X31, X32]:k5_xboole_0(k5_xboole_0(X30,X31),X32)=k5_xboole_0(X30,k5_xboole_0(X31,X32)), inference(variable_rename,[status(thm)],[t91_xboole_1])).
% 0.19/0.41  cnf(c_0_82, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_63, c_0_45]), c_0_45])).
% 0.19/0.41  cnf(c_0_83, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.19/0.41  cnf(c_0_84, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.19/0.41  cnf(c_0_85, plain, (k3_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_66])).
% 0.19/0.41  cnf(c_0_86, plain, (k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.19/0.41  fof(c_0_87, plain, ![X73]:k2_subset_1(X73)=X73, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 0.19/0.41  cnf(c_0_88, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.19/0.41  cnf(c_0_89, plain, (k4_subset_1(X2,X1,X3)=k2_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_69])).
% 0.19/0.41  cnf(c_0_90, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(csr,[status(thm)],[c_0_70, c_0_71])).
% 0.19/0.41  cnf(c_0_91, negated_conjecture, (r2_hidden(k5_xboole_0(esk3_0,esk4_0),k1_zfmisc_1(esk3_0))), inference(spm,[status(thm)],[c_0_72, c_0_73])).
% 0.19/0.41  cnf(c_0_92, plain, (k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))=k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_74, c_0_75]), c_0_76]), c_0_77]), c_0_78]), c_0_79]), c_0_80])).
% 0.19/0.41  cnf(c_0_93, plain, (k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_81])).
% 0.19/0.41  fof(c_0_94, plain, ![X19, X20, X21]:k5_xboole_0(k3_xboole_0(X19,X20),k3_xboole_0(X21,X20))=k3_xboole_0(k5_xboole_0(X19,X21),X20), inference(variable_rename,[status(thm)],[t112_xboole_1])).
% 0.19/0.41  cnf(c_0_95, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_83]), c_0_84]), c_0_85])).
% 0.19/0.41  cnf(c_0_96, plain, (k5_xboole_0(k1_xboole_0,X1)=X1), inference(spm,[status(thm)],[c_0_84, c_0_86])).
% 0.19/0.41  cnf(c_0_97, negated_conjecture, (k4_subset_1(esk3_0,esk4_0,k3_subset_1(esk3_0,esk4_0))!=k2_subset_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.41  cnf(c_0_98, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_87])).
% 0.19/0.41  cnf(c_0_99, plain, (k3_subset_1(X2,X1)=k5_xboole_0(X2,k3_xboole_0(X2,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_88, c_0_45])).
% 0.19/0.41  cnf(c_0_100, plain, (k4_subset_1(X2,X1,X3)=k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X3))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_89, c_0_75]), c_0_76]), c_0_77]), c_0_78]), c_0_79]), c_0_80])).
% 0.19/0.41  cnf(c_0_101, negated_conjecture, (m1_subset_1(k5_xboole_0(esk3_0,esk4_0),k1_zfmisc_1(esk3_0))), inference(spm,[status(thm)],[c_0_90, c_0_91])).
% 0.19/0.41  cnf(c_0_102, plain, (k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))=k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2)))), inference(rw,[status(thm)],[c_0_92, c_0_93])).
% 0.19/0.41  cnf(c_0_103, plain, (k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2))=k3_xboole_0(k5_xboole_0(X1,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_94])).
% 0.19/0.41  cnf(c_0_104, plain, (k5_xboole_0(X1,k5_xboole_0(X1,X2))=X2), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_95]), c_0_96])).
% 0.19/0.41  cnf(c_0_105, negated_conjecture, (k4_subset_1(esk3_0,esk4_0,k3_subset_1(esk3_0,esk4_0))!=esk3_0), inference(rw,[status(thm)],[c_0_97, c_0_98])).
% 0.19/0.41  cnf(c_0_106, negated_conjecture, (k3_subset_1(esk3_0,esk4_0)=k5_xboole_0(esk3_0,esk4_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_34]), c_0_54])).
% 0.19/0.41  cnf(c_0_107, negated_conjecture, (k4_subset_1(esk3_0,X1,k5_xboole_0(esk3_0,esk4_0))=k5_xboole_0(X1,k5_xboole_0(esk3_0,k5_xboole_0(esk4_0,k3_xboole_0(X1,k5_xboole_0(esk3_0,esk4_0)))))|~m1_subset_1(X1,k1_zfmisc_1(esk3_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_101]), c_0_102]), c_0_93])).
% 0.19/0.41  cnf(c_0_108, negated_conjecture, (k3_xboole_0(esk4_0,k5_xboole_0(esk3_0,X1))=k5_xboole_0(esk4_0,k3_xboole_0(X1,esk4_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103, c_0_54]), c_0_47])).
% 0.19/0.41  cnf(c_0_109, plain, (k5_xboole_0(X1,k5_xboole_0(X2,X1))=X2), inference(spm,[status(thm)],[c_0_104, c_0_86])).
% 0.19/0.41  cnf(c_0_110, negated_conjecture, (k4_subset_1(esk3_0,esk4_0,k5_xboole_0(esk3_0,esk4_0))!=esk3_0), inference(rw,[status(thm)],[c_0_105, c_0_106])).
% 0.19/0.41  cnf(c_0_111, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107, c_0_34]), c_0_108]), c_0_85]), c_0_95]), c_0_84]), c_0_109]), c_0_110]), ['proof']).
% 0.19/0.41  # SZS output end CNFRefutation
% 0.19/0.41  # Proof object total steps             : 112
% 0.19/0.41  # Proof object clause steps            : 57
% 0.19/0.41  # Proof object formula steps           : 55
% 0.19/0.41  # Proof object conjectures             : 18
% 0.19/0.41  # Proof object clause conjectures      : 15
% 0.19/0.41  # Proof object formula conjectures     : 3
% 0.19/0.41  # Proof object initial clauses used    : 30
% 0.19/0.41  # Proof object initial formulas used   : 27
% 0.19/0.41  # Proof object generating inferences   : 14
% 0.19/0.41  # Proof object simplifying inferences  : 38
% 0.19/0.41  # Training examples: 0 positive, 0 negative
% 0.19/0.41  # Parsed axioms                        : 27
% 0.19/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.41  # Initial clauses                      : 35
% 0.19/0.41  # Removed in clause preprocessing      : 9
% 0.19/0.41  # Initial clauses in saturation        : 26
% 0.19/0.41  # Processed clauses                    : 688
% 0.19/0.41  # ...of these trivial                  : 295
% 0.19/0.41  # ...subsumed                          : 39
% 0.19/0.41  # ...remaining for further processing  : 354
% 0.19/0.41  # Other redundant clauses eliminated   : 2
% 0.19/0.41  # Clauses deleted for lack of memory   : 0
% 0.19/0.41  # Backward-subsumed                    : 0
% 0.19/0.41  # Backward-rewritten                   : 60
% 0.19/0.41  # Generated clauses                    : 6875
% 0.19/0.41  # ...of the previous two non-trivial   : 4155
% 0.19/0.41  # Contextual simplify-reflections      : 1
% 0.19/0.41  # Paramodulations                      : 6869
% 0.19/0.41  # Factorizations                       : 4
% 0.19/0.41  # Equation resolutions                 : 2
% 0.19/0.41  # Propositional unsat checks           : 0
% 0.19/0.41  #    Propositional check models        : 0
% 0.19/0.41  #    Propositional check unsatisfiable : 0
% 0.19/0.41  #    Propositional clauses             : 0
% 0.19/0.41  #    Propositional clauses after purity: 0
% 0.19/0.41  #    Propositional unsat core size     : 0
% 0.19/0.41  #    Propositional preprocessing time  : 0.000
% 0.19/0.41  #    Propositional encoding time       : 0.000
% 0.19/0.41  #    Propositional solver time         : 0.000
% 0.19/0.41  #    Success case prop preproc time    : 0.000
% 0.19/0.41  #    Success case prop encoding time   : 0.000
% 0.19/0.41  #    Success case prop solver time     : 0.000
% 0.19/0.41  # Current number of processed clauses  : 266
% 0.19/0.41  #    Positive orientable unit clauses  : 230
% 0.19/0.41  #    Positive unorientable unit clauses: 12
% 0.19/0.41  #    Negative unit clauses             : 2
% 0.19/0.41  #    Non-unit-clauses                  : 22
% 0.19/0.41  # Current number of unprocessed clauses: 3427
% 0.19/0.41  # ...number of literals in the above   : 3592
% 0.19/0.41  # Current number of archived formulas  : 0
% 0.19/0.41  # Current number of archived clauses   : 95
% 0.19/0.41  # Clause-clause subsumption calls (NU) : 21
% 0.19/0.41  # Rec. Clause-clause subsumption calls : 20
% 0.19/0.41  # Non-unit clause-clause subsumptions  : 4
% 0.19/0.41  # Unit Clause-clause subsumption calls : 158
% 0.19/0.41  # Rewrite failures with RHS unbound    : 0
% 0.19/0.41  # BW rewrite match attempts            : 609
% 0.19/0.41  # BW rewrite match successes           : 165
% 0.19/0.41  # Condensation attempts                : 0
% 0.19/0.41  # Condensation successes               : 0
% 0.19/0.41  # Termbank termtop insertions          : 90037
% 0.19/0.41  
% 0.19/0.41  # -------------------------------------------------
% 0.19/0.41  # User time                : 0.066 s
% 0.19/0.41  # System time              : 0.007 s
% 0.19/0.41  # Total time               : 0.073 s
% 0.19/0.41  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
