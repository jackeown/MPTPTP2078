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
% DateTime   : Thu Dec  3 10:45:20 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 341 expanded)
%              Number of clauses        :   57 ( 145 expanded)
%              Number of leaves         :   25 (  95 expanded)
%              Depth                    :   14
%              Number of atoms          :  172 ( 523 expanded)
%              Number of equality atoms :   87 ( 305 expanded)
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

fof(t5_boole,axiom,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(commutativity_k5_xboole_0,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(t93_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t93_xboole_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(t92_xboole_1,axiom,(
    ! [X1] : k5_xboole_0(X1,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(c_0_25,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X1))
       => k4_subset_1(X1,X2,k3_subset_1(X1,X2)) = k2_subset_1(X1) ) ),
    inference(assume_negation,[status(cth)],[t25_subset_1])).

fof(c_0_26,plain,(
    ! [X58,X59,X60,X61,X62,X63] :
      ( ( ~ r2_hidden(X60,X59)
        | r1_tarski(X60,X58)
        | X59 != k1_zfmisc_1(X58) )
      & ( ~ r1_tarski(X61,X58)
        | r2_hidden(X61,X59)
        | X59 != k1_zfmisc_1(X58) )
      & ( ~ r2_hidden(esk2_2(X62,X63),X63)
        | ~ r1_tarski(esk2_2(X62,X63),X62)
        | X63 = k1_zfmisc_1(X62) )
      & ( r2_hidden(esk2_2(X62,X63),X63)
        | r1_tarski(esk2_2(X62,X63),X62)
        | X63 = k1_zfmisc_1(X62) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

fof(c_0_27,plain,(
    ! [X67,X68] :
      ( ( ~ m1_subset_1(X68,X67)
        | r2_hidden(X68,X67)
        | v1_xboole_0(X67) )
      & ( ~ r2_hidden(X68,X67)
        | m1_subset_1(X68,X67)
        | v1_xboole_0(X67) )
      & ( ~ m1_subset_1(X68,X67)
        | v1_xboole_0(X68)
        | ~ v1_xboole_0(X67) )
      & ( ~ v1_xboole_0(X68)
        | m1_subset_1(X68,X67)
        | ~ v1_xboole_0(X67) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

fof(c_0_28,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(esk3_0))
    & k4_subset_1(esk3_0,esk4_0,k3_subset_1(esk3_0,esk4_0)) != k2_subset_1(esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_25])])])).

fof(c_0_29,plain,(
    ! [X72] : ~ v1_xboole_0(k1_zfmisc_1(X72)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).

cnf(c_0_30,plain,
    ( r1_tarski(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_31,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_32,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_33,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_34,plain,(
    ! [X18,X19] :
      ( ~ r1_tarski(X18,X19)
      | k3_xboole_0(X18,X19) = X18 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_35,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(er,[status(thm)],[c_0_30])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(esk4_0,k1_zfmisc_1(esk3_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33])).

fof(c_0_37,plain,(
    ! [X20,X21] : r1_tarski(k4_xboole_0(X20,X21),X20) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

fof(c_0_38,plain,(
    ! [X16,X17] : k4_xboole_0(X16,X17) = k5_xboole_0(X16,k3_xboole_0(X16,X17)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_39,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_40,negated_conjecture,
    ( r1_tarski(esk4_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

fof(c_0_41,plain,(
    ! [X8,X9] : k3_xboole_0(X8,X9) = k3_xboole_0(X9,X8) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_42,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_43,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_44,negated_conjecture,
    ( k3_xboole_0(esk4_0,esk3_0) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_45,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

fof(c_0_46,plain,(
    ! [X65,X66] : k3_tarski(k2_tarski(X65,X66)) = k2_xboole_0(X65,X66) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_47,plain,(
    ! [X31,X32] : k1_enumset1(X31,X31,X32) = k2_tarski(X31,X32) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_48,plain,(
    ! [X12,X13,X14] :
      ( ( ~ v1_xboole_0(X12)
        | ~ r2_hidden(X13,X12) )
      & ( r2_hidden(esk1_1(X14),X14)
        | v1_xboole_0(X14) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_49,plain,
    ( r2_hidden(X1,X3)
    | ~ r1_tarski(X1,X2)
    | X3 != k1_zfmisc_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_50,plain,
    ( r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X1) ),
    inference(rw,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_51,negated_conjecture,
    ( k3_xboole_0(esk3_0,esk4_0) = esk4_0 ),
    inference(rw,[status(thm)],[c_0_44,c_0_45])).

fof(c_0_52,plain,(
    ! [X29,X30] : k2_xboole_0(X29,X30) = k5_xboole_0(k5_xboole_0(X29,X30),k3_xboole_0(X29,X30)) ),
    inference(variable_rename,[status(thm)],[t94_xboole_1])).

cnf(c_0_53,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_54,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

fof(c_0_55,plain,(
    ! [X33,X34,X35] : k2_enumset1(X33,X33,X34,X35) = k1_enumset1(X33,X34,X35) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_56,plain,(
    ! [X36,X37,X38,X39] : k3_enumset1(X36,X36,X37,X38,X39) = k2_enumset1(X36,X37,X38,X39) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_57,plain,(
    ! [X40,X41,X42,X43,X44] : k4_enumset1(X40,X40,X41,X42,X43,X44) = k3_enumset1(X40,X41,X42,X43,X44) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_58,plain,(
    ! [X45,X46,X47,X48,X49,X50] : k5_enumset1(X45,X45,X46,X47,X48,X49,X50) = k4_enumset1(X45,X46,X47,X48,X49,X50) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_59,plain,(
    ! [X51,X52,X53,X54,X55,X56,X57] : k6_enumset1(X51,X51,X52,X53,X54,X55,X56,X57) = k5_enumset1(X51,X52,X53,X54,X55,X56,X57) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_60,plain,(
    ! [X70,X71] :
      ( ~ m1_subset_1(X71,k1_zfmisc_1(X70))
      | k3_subset_1(X70,X71) = k4_xboole_0(X70,X71) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

fof(c_0_61,plain,(
    ! [X73,X74,X75] :
      ( ~ m1_subset_1(X74,k1_zfmisc_1(X73))
      | ~ m1_subset_1(X75,k1_zfmisc_1(X73))
      | k4_subset_1(X73,X74,X75) = k2_xboole_0(X74,X75) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).

cnf(c_0_62,plain,
    ( m1_subset_1(X1,X2)
    | v1_xboole_0(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_63,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_64,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(er,[status(thm)],[c_0_49])).

cnf(c_0_65,negated_conjecture,
    ( r1_tarski(k5_xboole_0(esk3_0,esk4_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_66,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_67,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_68,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_69,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_70,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_71,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_72,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

fof(c_0_73,plain,(
    ! [X23,X24,X25] : k5_xboole_0(k5_xboole_0(X23,X24),X25) = k5_xboole_0(X23,k5_xboole_0(X24,X25)) ),
    inference(variable_rename,[status(thm)],[t91_xboole_1])).

fof(c_0_74,plain,(
    ! [X22] : k5_xboole_0(X22,k1_xboole_0) = X22 ),
    inference(variable_rename,[status(thm)],[t5_boole])).

fof(c_0_75,plain,(
    ! [X10,X11] : k5_xboole_0(X10,X11) = k5_xboole_0(X11,X10) ),
    inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).

fof(c_0_76,plain,(
    ! [X27,X28] : k2_xboole_0(X27,X28) = k2_xboole_0(k5_xboole_0(X27,X28),k3_xboole_0(X27,X28)) ),
    inference(variable_rename,[status(thm)],[t93_xboole_1])).

fof(c_0_77,plain,(
    ! [X69] : k2_subset_1(X69) = X69 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

cnf(c_0_78,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_79,plain,
    ( k4_subset_1(X2,X1,X3) = k2_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_80,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(csr,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_81,negated_conjecture,
    ( r2_hidden(k5_xboole_0(esk3_0,esk4_0),k1_zfmisc_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_82,plain,
    ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) = k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66,c_0_67]),c_0_68]),c_0_69]),c_0_70]),c_0_71]),c_0_72])).

cnf(c_0_83,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

fof(c_0_84,plain,(
    ! [X26] : k5_xboole_0(X26,X26) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t92_xboole_1])).

cnf(c_0_85,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

cnf(c_0_86,plain,
    ( k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_87,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_76])).

cnf(c_0_88,negated_conjecture,
    ( k4_subset_1(esk3_0,esk4_0,k3_subset_1(esk3_0,esk4_0)) != k2_subset_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_89,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_77])).

cnf(c_0_90,plain,
    ( k3_subset_1(X2,X1) = k5_xboole_0(X2,k3_xboole_0(X2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_78,c_0_43])).

cnf(c_0_91,plain,
    ( k4_subset_1(X2,X1,X3) = k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_79,c_0_67]),c_0_68]),c_0_69]),c_0_70]),c_0_71]),c_0_72])).

cnf(c_0_92,negated_conjecture,
    ( m1_subset_1(k5_xboole_0(esk3_0,esk4_0),k1_zfmisc_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_80,c_0_81])).

cnf(c_0_93,plain,
    ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_82,c_0_83])).

cnf(c_0_94,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_84])).

cnf(c_0_95,plain,
    ( k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_85,c_0_86])).

cnf(c_0_96,plain,
    ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) = k3_tarski(k6_enumset1(k5_xboole_0(X1,X2),k5_xboole_0(X1,X2),k5_xboole_0(X1,X2),k5_xboole_0(X1,X2),k5_xboole_0(X1,X2),k5_xboole_0(X1,X2),k5_xboole_0(X1,X2),k3_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_87,c_0_67]),c_0_67]),c_0_68]),c_0_68]),c_0_69]),c_0_69]),c_0_70]),c_0_70]),c_0_71]),c_0_71]),c_0_72]),c_0_72])).

cnf(c_0_97,negated_conjecture,
    ( k4_subset_1(esk3_0,esk4_0,k3_subset_1(esk3_0,esk4_0)) != esk3_0 ),
    inference(rw,[status(thm)],[c_0_88,c_0_89])).

cnf(c_0_98,negated_conjecture,
    ( k3_subset_1(esk3_0,esk4_0) = k5_xboole_0(esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_32]),c_0_51])).

cnf(c_0_99,negated_conjecture,
    ( k5_xboole_0(X1,k5_xboole_0(esk3_0,k5_xboole_0(esk4_0,k3_xboole_0(X1,k5_xboole_0(esk3_0,esk4_0))))) = k4_subset_1(esk3_0,X1,k5_xboole_0(esk3_0,esk4_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk3_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_92]),c_0_93]),c_0_83])).

cnf(c_0_100,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,X3)) = k5_xboole_0(X2,k5_xboole_0(X1,X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_86]),c_0_83])).

cnf(c_0_101,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,X2)) = X2 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_94]),c_0_95])).

cnf(c_0_102,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2))))) = k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_96,c_0_93]),c_0_83])).

cnf(c_0_103,negated_conjecture,
    ( k4_subset_1(esk3_0,esk4_0,k5_xboole_0(esk3_0,esk4_0)) != esk3_0 ),
    inference(rw,[status(thm)],[c_0_97,c_0_98])).

cnf(c_0_104,negated_conjecture,
    ( k4_subset_1(esk3_0,esk4_0,k5_xboole_0(esk3_0,esk4_0)) = k5_xboole_0(esk3_0,k3_xboole_0(esk4_0,k5_xboole_0(esk3_0,esk4_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_32]),c_0_100]),c_0_101])).

cnf(c_0_105,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2))))) = k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_93,c_0_102])).

cnf(c_0_106,negated_conjecture,
    ( k5_xboole_0(esk3_0,k3_xboole_0(esk4_0,k5_xboole_0(esk3_0,esk4_0))) != esk3_0 ),
    inference(rw,[status(thm)],[c_0_103,c_0_104])).

cnf(c_0_107,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_51]),c_0_45]),c_0_101]),c_0_94]),c_0_85]),c_0_106]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:28:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.19/0.41  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S054N
% 0.19/0.41  # and selection function GSelectMinInfpos.
% 0.19/0.41  #
% 0.19/0.41  # Preprocessing time       : 0.027 s
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
% 0.19/0.41  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.19/0.41  fof(t94_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_xboole_1)).
% 0.19/0.41  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.19/0.41  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.19/0.41  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 0.19/0.41  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 0.19/0.41  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 0.19/0.41  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 0.19/0.41  fof(redefinition_k4_subset_1, axiom, ![X1, X2, X3]:((m1_subset_1(X2,k1_zfmisc_1(X1))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>k4_subset_1(X1,X2,X3)=k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 0.19/0.41  fof(t91_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 0.19/0.41  fof(t5_boole, axiom, ![X1]:k5_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 0.19/0.41  fof(commutativity_k5_xboole_0, axiom, ![X1, X2]:k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 0.19/0.41  fof(t93_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t93_xboole_1)).
% 0.19/0.41  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 0.19/0.41  fof(t92_xboole_1, axiom, ![X1]:k5_xboole_0(X1,X1)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 0.19/0.41  fof(c_0_25, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k4_subset_1(X1,X2,k3_subset_1(X1,X2))=k2_subset_1(X1))), inference(assume_negation,[status(cth)],[t25_subset_1])).
% 0.19/0.41  fof(c_0_26, plain, ![X58, X59, X60, X61, X62, X63]:(((~r2_hidden(X60,X59)|r1_tarski(X60,X58)|X59!=k1_zfmisc_1(X58))&(~r1_tarski(X61,X58)|r2_hidden(X61,X59)|X59!=k1_zfmisc_1(X58)))&((~r2_hidden(esk2_2(X62,X63),X63)|~r1_tarski(esk2_2(X62,X63),X62)|X63=k1_zfmisc_1(X62))&(r2_hidden(esk2_2(X62,X63),X63)|r1_tarski(esk2_2(X62,X63),X62)|X63=k1_zfmisc_1(X62)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 0.19/0.41  fof(c_0_27, plain, ![X67, X68]:(((~m1_subset_1(X68,X67)|r2_hidden(X68,X67)|v1_xboole_0(X67))&(~r2_hidden(X68,X67)|m1_subset_1(X68,X67)|v1_xboole_0(X67)))&((~m1_subset_1(X68,X67)|v1_xboole_0(X68)|~v1_xboole_0(X67))&(~v1_xboole_0(X68)|m1_subset_1(X68,X67)|~v1_xboole_0(X67)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 0.19/0.41  fof(c_0_28, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(esk3_0))&k4_subset_1(esk3_0,esk4_0,k3_subset_1(esk3_0,esk4_0))!=k2_subset_1(esk3_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_25])])])).
% 0.19/0.41  fof(c_0_29, plain, ![X72]:~v1_xboole_0(k1_zfmisc_1(X72)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).
% 0.19/0.41  cnf(c_0_30, plain, (r1_tarski(X1,X3)|~r2_hidden(X1,X2)|X2!=k1_zfmisc_1(X3)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.41  cnf(c_0_31, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.41  cnf(c_0_32, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.41  cnf(c_0_33, plain, (~v1_xboole_0(k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.41  fof(c_0_34, plain, ![X18, X19]:(~r1_tarski(X18,X19)|k3_xboole_0(X18,X19)=X18), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.19/0.41  cnf(c_0_35, plain, (r1_tarski(X1,X2)|~r2_hidden(X1,k1_zfmisc_1(X2))), inference(er,[status(thm)],[c_0_30])).
% 0.19/0.41  cnf(c_0_36, negated_conjecture, (r2_hidden(esk4_0,k1_zfmisc_1(esk3_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_33])).
% 0.19/0.41  fof(c_0_37, plain, ![X20, X21]:r1_tarski(k4_xboole_0(X20,X21),X20), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.19/0.41  fof(c_0_38, plain, ![X16, X17]:k4_xboole_0(X16,X17)=k5_xboole_0(X16,k3_xboole_0(X16,X17)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.19/0.41  cnf(c_0_39, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.19/0.41  cnf(c_0_40, negated_conjecture, (r1_tarski(esk4_0,esk3_0)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.19/0.41  fof(c_0_41, plain, ![X8, X9]:k3_xboole_0(X8,X9)=k3_xboole_0(X9,X8), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.19/0.41  cnf(c_0_42, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.19/0.41  cnf(c_0_43, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.19/0.41  cnf(c_0_44, negated_conjecture, (k3_xboole_0(esk4_0,esk3_0)=esk4_0), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.19/0.41  cnf(c_0_45, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.19/0.41  fof(c_0_46, plain, ![X65, X66]:k3_tarski(k2_tarski(X65,X66))=k2_xboole_0(X65,X66), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.19/0.41  fof(c_0_47, plain, ![X31, X32]:k1_enumset1(X31,X31,X32)=k2_tarski(X31,X32), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.19/0.41  fof(c_0_48, plain, ![X12, X13, X14]:((~v1_xboole_0(X12)|~r2_hidden(X13,X12))&(r2_hidden(esk1_1(X14),X14)|v1_xboole_0(X14))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.19/0.41  cnf(c_0_49, plain, (r2_hidden(X1,X3)|~r1_tarski(X1,X2)|X3!=k1_zfmisc_1(X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.41  cnf(c_0_50, plain, (r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X1)), inference(rw,[status(thm)],[c_0_42, c_0_43])).
% 0.19/0.41  cnf(c_0_51, negated_conjecture, (k3_xboole_0(esk3_0,esk4_0)=esk4_0), inference(rw,[status(thm)],[c_0_44, c_0_45])).
% 0.19/0.41  fof(c_0_52, plain, ![X29, X30]:k2_xboole_0(X29,X30)=k5_xboole_0(k5_xboole_0(X29,X30),k3_xboole_0(X29,X30)), inference(variable_rename,[status(thm)],[t94_xboole_1])).
% 0.19/0.41  cnf(c_0_53, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.19/0.41  cnf(c_0_54, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.19/0.41  fof(c_0_55, plain, ![X33, X34, X35]:k2_enumset1(X33,X33,X34,X35)=k1_enumset1(X33,X34,X35), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.19/0.41  fof(c_0_56, plain, ![X36, X37, X38, X39]:k3_enumset1(X36,X36,X37,X38,X39)=k2_enumset1(X36,X37,X38,X39), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.19/0.41  fof(c_0_57, plain, ![X40, X41, X42, X43, X44]:k4_enumset1(X40,X40,X41,X42,X43,X44)=k3_enumset1(X40,X41,X42,X43,X44), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.19/0.41  fof(c_0_58, plain, ![X45, X46, X47, X48, X49, X50]:k5_enumset1(X45,X45,X46,X47,X48,X49,X50)=k4_enumset1(X45,X46,X47,X48,X49,X50), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.19/0.41  fof(c_0_59, plain, ![X51, X52, X53, X54, X55, X56, X57]:k6_enumset1(X51,X51,X52,X53,X54,X55,X56,X57)=k5_enumset1(X51,X52,X53,X54,X55,X56,X57), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.19/0.41  fof(c_0_60, plain, ![X70, X71]:(~m1_subset_1(X71,k1_zfmisc_1(X70))|k3_subset_1(X70,X71)=k4_xboole_0(X70,X71)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 0.19/0.41  fof(c_0_61, plain, ![X73, X74, X75]:(~m1_subset_1(X74,k1_zfmisc_1(X73))|~m1_subset_1(X75,k1_zfmisc_1(X73))|k4_subset_1(X73,X74,X75)=k2_xboole_0(X74,X75)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).
% 0.19/0.41  cnf(c_0_62, plain, (m1_subset_1(X1,X2)|v1_xboole_0(X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.41  cnf(c_0_63, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.19/0.41  cnf(c_0_64, plain, (r2_hidden(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(er,[status(thm)],[c_0_49])).
% 0.19/0.41  cnf(c_0_65, negated_conjecture, (r1_tarski(k5_xboole_0(esk3_0,esk4_0),esk3_0)), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.19/0.41  cnf(c_0_66, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.19/0.41  cnf(c_0_67, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_53, c_0_54])).
% 0.19/0.41  cnf(c_0_68, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.19/0.41  cnf(c_0_69, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.19/0.41  cnf(c_0_70, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.19/0.41  cnf(c_0_71, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.19/0.41  cnf(c_0_72, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.19/0.41  fof(c_0_73, plain, ![X23, X24, X25]:k5_xboole_0(k5_xboole_0(X23,X24),X25)=k5_xboole_0(X23,k5_xboole_0(X24,X25)), inference(variable_rename,[status(thm)],[t91_xboole_1])).
% 0.19/0.41  fof(c_0_74, plain, ![X22]:k5_xboole_0(X22,k1_xboole_0)=X22, inference(variable_rename,[status(thm)],[t5_boole])).
% 0.19/0.41  fof(c_0_75, plain, ![X10, X11]:k5_xboole_0(X10,X11)=k5_xboole_0(X11,X10), inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).
% 0.19/0.41  fof(c_0_76, plain, ![X27, X28]:k2_xboole_0(X27,X28)=k2_xboole_0(k5_xboole_0(X27,X28),k3_xboole_0(X27,X28)), inference(variable_rename,[status(thm)],[t93_xboole_1])).
% 0.19/0.41  fof(c_0_77, plain, ![X69]:k2_subset_1(X69)=X69, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 0.19/0.41  cnf(c_0_78, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.19/0.41  cnf(c_0_79, plain, (k4_subset_1(X2,X1,X3)=k2_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.19/0.41  cnf(c_0_80, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(csr,[status(thm)],[c_0_62, c_0_63])).
% 0.19/0.41  cnf(c_0_81, negated_conjecture, (r2_hidden(k5_xboole_0(esk3_0,esk4_0),k1_zfmisc_1(esk3_0))), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 0.19/0.41  cnf(c_0_82, plain, (k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))=k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66, c_0_67]), c_0_68]), c_0_69]), c_0_70]), c_0_71]), c_0_72])).
% 0.19/0.41  cnf(c_0_83, plain, (k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_73])).
% 0.19/0.41  fof(c_0_84, plain, ![X26]:k5_xboole_0(X26,X26)=k1_xboole_0, inference(variable_rename,[status(thm)],[t92_xboole_1])).
% 0.19/0.41  cnf(c_0_85, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_74])).
% 0.19/0.41  cnf(c_0_86, plain, (k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_75])).
% 0.19/0.41  cnf(c_0_87, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_76])).
% 0.19/0.41  cnf(c_0_88, negated_conjecture, (k4_subset_1(esk3_0,esk4_0,k3_subset_1(esk3_0,esk4_0))!=k2_subset_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.41  cnf(c_0_89, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_77])).
% 0.19/0.41  cnf(c_0_90, plain, (k3_subset_1(X2,X1)=k5_xboole_0(X2,k3_xboole_0(X2,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_78, c_0_43])).
% 0.19/0.41  cnf(c_0_91, plain, (k4_subset_1(X2,X1,X3)=k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X3))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_79, c_0_67]), c_0_68]), c_0_69]), c_0_70]), c_0_71]), c_0_72])).
% 0.19/0.41  cnf(c_0_92, negated_conjecture, (m1_subset_1(k5_xboole_0(esk3_0,esk4_0),k1_zfmisc_1(esk3_0))), inference(spm,[status(thm)],[c_0_80, c_0_81])).
% 0.19/0.41  cnf(c_0_93, plain, (k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))=k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2)))), inference(rw,[status(thm)],[c_0_82, c_0_83])).
% 0.19/0.41  cnf(c_0_94, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_84])).
% 0.19/0.41  cnf(c_0_95, plain, (k5_xboole_0(k1_xboole_0,X1)=X1), inference(spm,[status(thm)],[c_0_85, c_0_86])).
% 0.19/0.41  cnf(c_0_96, plain, (k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))=k3_tarski(k6_enumset1(k5_xboole_0(X1,X2),k5_xboole_0(X1,X2),k5_xboole_0(X1,X2),k5_xboole_0(X1,X2),k5_xboole_0(X1,X2),k5_xboole_0(X1,X2),k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_87, c_0_67]), c_0_67]), c_0_68]), c_0_68]), c_0_69]), c_0_69]), c_0_70]), c_0_70]), c_0_71]), c_0_71]), c_0_72]), c_0_72])).
% 0.19/0.41  cnf(c_0_97, negated_conjecture, (k4_subset_1(esk3_0,esk4_0,k3_subset_1(esk3_0,esk4_0))!=esk3_0), inference(rw,[status(thm)],[c_0_88, c_0_89])).
% 0.19/0.41  cnf(c_0_98, negated_conjecture, (k3_subset_1(esk3_0,esk4_0)=k5_xboole_0(esk3_0,esk4_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_32]), c_0_51])).
% 0.19/0.41  cnf(c_0_99, negated_conjecture, (k5_xboole_0(X1,k5_xboole_0(esk3_0,k5_xboole_0(esk4_0,k3_xboole_0(X1,k5_xboole_0(esk3_0,esk4_0)))))=k4_subset_1(esk3_0,X1,k5_xboole_0(esk3_0,esk4_0))|~m1_subset_1(X1,k1_zfmisc_1(esk3_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_92]), c_0_93]), c_0_83])).
% 0.19/0.41  cnf(c_0_100, plain, (k5_xboole_0(X1,k5_xboole_0(X2,X3))=k5_xboole_0(X2,k5_xboole_0(X1,X3))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_86]), c_0_83])).
% 0.19/0.41  cnf(c_0_101, plain, (k5_xboole_0(X1,k5_xboole_0(X1,X2))=X2), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_94]), c_0_95])).
% 0.19/0.41  cnf(c_0_102, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)))))=k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_96, c_0_93]), c_0_83])).
% 0.19/0.41  cnf(c_0_103, negated_conjecture, (k4_subset_1(esk3_0,esk4_0,k5_xboole_0(esk3_0,esk4_0))!=esk3_0), inference(rw,[status(thm)],[c_0_97, c_0_98])).
% 0.19/0.41  cnf(c_0_104, negated_conjecture, (k4_subset_1(esk3_0,esk4_0,k5_xboole_0(esk3_0,esk4_0))=k5_xboole_0(esk3_0,k3_xboole_0(esk4_0,k5_xboole_0(esk3_0,esk4_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_32]), c_0_100]), c_0_101])).
% 0.19/0.41  cnf(c_0_105, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)))))=k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2)))), inference(spm,[status(thm)],[c_0_93, c_0_102])).
% 0.19/0.41  cnf(c_0_106, negated_conjecture, (k5_xboole_0(esk3_0,k3_xboole_0(esk4_0,k5_xboole_0(esk3_0,esk4_0)))!=esk3_0), inference(rw,[status(thm)],[c_0_103, c_0_104])).
% 0.19/0.41  cnf(c_0_107, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105, c_0_51]), c_0_45]), c_0_101]), c_0_94]), c_0_85]), c_0_106]), ['proof']).
% 0.19/0.41  # SZS output end CNFRefutation
% 0.19/0.41  # Proof object total steps             : 108
% 0.19/0.41  # Proof object clause steps            : 57
% 0.19/0.41  # Proof object formula steps           : 51
% 0.19/0.41  # Proof object conjectures             : 19
% 0.19/0.41  # Proof object clause conjectures      : 16
% 0.19/0.41  # Proof object formula conjectures     : 3
% 0.19/0.41  # Proof object initial clauses used    : 28
% 0.19/0.41  # Proof object initial formulas used   : 25
% 0.19/0.41  # Proof object generating inferences   : 14
% 0.19/0.41  # Proof object simplifying inferences  : 50
% 0.19/0.41  # Training examples: 0 positive, 0 negative
% 0.19/0.41  # Parsed axioms                        : 25
% 0.19/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.41  # Initial clauses                      : 33
% 0.19/0.41  # Removed in clause preprocessing      : 9
% 0.19/0.41  # Initial clauses in saturation        : 24
% 0.19/0.41  # Processed clauses                    : 347
% 0.19/0.41  # ...of these trivial                  : 98
% 0.19/0.41  # ...subsumed                          : 13
% 0.19/0.41  # ...remaining for further processing  : 236
% 0.19/0.41  # Other redundant clauses eliminated   : 2
% 0.19/0.41  # Clauses deleted for lack of memory   : 0
% 0.19/0.41  # Backward-subsumed                    : 2
% 0.19/0.41  # Backward-rewritten                   : 81
% 0.19/0.41  # Generated clauses                    : 1855
% 0.19/0.41  # ...of the previous two non-trivial   : 1099
% 0.19/0.41  # Contextual simplify-reflections      : 1
% 0.19/0.41  # Paramodulations                      : 1853
% 0.19/0.41  # Factorizations                       : 0
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
% 0.19/0.41  # Current number of processed clauses  : 127
% 0.19/0.41  #    Positive orientable unit clauses  : 97
% 0.19/0.41  #    Positive unorientable unit clauses: 9
% 0.19/0.41  #    Negative unit clauses             : 2
% 0.19/0.41  #    Non-unit-clauses                  : 19
% 0.19/0.41  # Current number of unprocessed clauses: 734
% 0.19/0.41  # ...number of literals in the above   : 760
% 0.19/0.41  # Current number of archived formulas  : 0
% 0.19/0.41  # Current number of archived clauses   : 116
% 0.19/0.41  # Clause-clause subsumption calls (NU) : 23
% 0.19/0.41  # Rec. Clause-clause subsumption calls : 22
% 0.19/0.41  # Non-unit clause-clause subsumptions  : 4
% 0.19/0.41  # Unit Clause-clause subsumption calls : 523
% 0.19/0.41  # Rewrite failures with RHS unbound    : 0
% 0.19/0.41  # BW rewrite match attempts            : 352
% 0.19/0.41  # BW rewrite match successes           : 148
% 0.19/0.41  # Condensation attempts                : 0
% 0.19/0.41  # Condensation successes               : 0
% 0.19/0.41  # Termbank termtop insertions          : 23796
% 0.19/0.41  
% 0.19/0.41  # -------------------------------------------------
% 0.19/0.41  # User time                : 0.065 s
% 0.19/0.41  # System time              : 0.006 s
% 0.19/0.41  # Total time               : 0.072 s
% 0.19/0.41  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
