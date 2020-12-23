%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:45:19 EST 2020

% Result     : Theorem 0.76s
% Output     : CNFRefutation 0.76s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 791 expanded)
%              Number of clauses        :   77 ( 355 expanded)
%              Number of leaves         :   29 ( 215 expanded)
%              Depth                    :   14
%              Number of atoms          :  237 (1283 expanded)
%              Number of equality atoms :  115 ( 760 expanded)
%              Maximal formula depth    :   16 (   3 average)
%              Maximal clause size      :   20 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t25_subset_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k4_subset_1(X1,X2,k3_subset_1(X1,X2)) = k2_subset_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_subset_1)).

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

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

fof(t47_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(t5_boole,axiom,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(commutativity_k5_xboole_0,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

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

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t93_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t93_xboole_1)).

fof(t91_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

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

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(c_0_29,plain,(
    ! [X16,X17,X18,X19,X20,X21,X22,X23] :
      ( ( r2_hidden(X19,X16)
        | ~ r2_hidden(X19,X18)
        | X18 != k4_xboole_0(X16,X17) )
      & ( ~ r2_hidden(X19,X17)
        | ~ r2_hidden(X19,X18)
        | X18 != k4_xboole_0(X16,X17) )
      & ( ~ r2_hidden(X20,X16)
        | r2_hidden(X20,X17)
        | r2_hidden(X20,X18)
        | X18 != k4_xboole_0(X16,X17) )
      & ( ~ r2_hidden(esk2_3(X21,X22,X23),X23)
        | ~ r2_hidden(esk2_3(X21,X22,X23),X21)
        | r2_hidden(esk2_3(X21,X22,X23),X22)
        | X23 = k4_xboole_0(X21,X22) )
      & ( r2_hidden(esk2_3(X21,X22,X23),X21)
        | r2_hidden(esk2_3(X21,X22,X23),X23)
        | X23 = k4_xboole_0(X21,X22) )
      & ( ~ r2_hidden(esk2_3(X21,X22,X23),X22)
        | r2_hidden(esk2_3(X21,X22,X23),X23)
        | X23 = k4_xboole_0(X21,X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

fof(c_0_30,plain,(
    ! [X28,X29] : k4_xboole_0(X28,X29) = k5_xboole_0(X28,k3_xboole_0(X28,X29)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_31,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_32,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_33,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X1))
       => k4_subset_1(X1,X2,k3_subset_1(X1,X2)) = k2_subset_1(X1) ) ),
    inference(assume_negation,[status(cth)],[t25_subset_1])).

cnf(c_0_34,plain,
    ( X3 != k5_xboole_0(X4,k3_xboole_0(X4,X2))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_31,c_0_32])).

fof(c_0_35,plain,(
    ! [X25] : k3_xboole_0(X25,X25) = X25 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

fof(c_0_36,plain,(
    ! [X73,X74,X75,X76,X77,X78] :
      ( ( ~ r2_hidden(X75,X74)
        | r1_tarski(X75,X73)
        | X74 != k1_zfmisc_1(X73) )
      & ( ~ r1_tarski(X76,X73)
        | r2_hidden(X76,X74)
        | X74 != k1_zfmisc_1(X73) )
      & ( ~ r2_hidden(esk4_2(X77,X78),X78)
        | ~ r1_tarski(esk4_2(X77,X78),X77)
        | X78 = k1_zfmisc_1(X77) )
      & ( r2_hidden(esk4_2(X77,X78),X78)
        | r1_tarski(esk4_2(X77,X78),X77)
        | X78 = k1_zfmisc_1(X77) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

fof(c_0_37,plain,(
    ! [X82,X83] :
      ( ( ~ m1_subset_1(X83,X82)
        | r2_hidden(X83,X82)
        | v1_xboole_0(X82) )
      & ( ~ r2_hidden(X83,X82)
        | m1_subset_1(X83,X82)
        | v1_xboole_0(X82) )
      & ( ~ m1_subset_1(X83,X82)
        | v1_xboole_0(X83)
        | ~ v1_xboole_0(X82) )
      & ( ~ v1_xboole_0(X83)
        | m1_subset_1(X83,X82)
        | ~ v1_xboole_0(X82) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

fof(c_0_38,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(esk5_0))
    & k4_subset_1(esk5_0,esk6_0,k3_subset_1(esk5_0,esk6_0)) != k2_subset_1(esk5_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_33])])])).

fof(c_0_39,plain,(
    ! [X87] : ~ v1_xboole_0(k1_zfmisc_1(X87)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).

fof(c_0_40,plain,(
    ! [X34,X35] : k4_xboole_0(X34,k3_xboole_0(X34,X35)) = k4_xboole_0(X34,X35) ),
    inference(variable_rename,[status(thm)],[t47_xboole_1])).

cnf(c_0_41,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_42,plain,(
    ! [X38] : k5_xboole_0(X38,k1_xboole_0) = X38 ),
    inference(variable_rename,[status(thm)],[t5_boole])).

fof(c_0_43,plain,(
    ! [X10,X11] : k5_xboole_0(X10,X11) = k5_xboole_0(X11,X10) ),
    inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).

cnf(c_0_44,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_34])).

cnf(c_0_45,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_46,plain,
    ( r1_tarski(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_47,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_48,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_49,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

fof(c_0_50,plain,(
    ! [X80,X81] : k3_tarski(k2_tarski(X80,X81)) = k2_xboole_0(X80,X81) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_51,plain,(
    ! [X46,X47] : k1_enumset1(X46,X46,X47) = k2_tarski(X46,X47) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_52,plain,(
    ! [X32,X33] : r1_tarski(k4_xboole_0(X32,X33),X32) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

cnf(c_0_53,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

fof(c_0_54,plain,(
    ! [X26] :
      ( X26 = k1_xboole_0
      | r2_hidden(esk3_1(X26),X26) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

cnf(c_0_55,plain,
    ( r2_hidden(X1,X2)
    | X3 != k5_xboole_0(X2,k3_xboole_0(X2,X4))
    | ~ r2_hidden(X1,X3) ),
    inference(rw,[status(thm)],[c_0_41,c_0_32])).

cnf(c_0_56,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_57,plain,
    ( k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_58,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,X2))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

fof(c_0_59,plain,(
    ! [X30,X31] :
      ( ~ r1_tarski(X30,X31)
      | k3_xboole_0(X30,X31) = X30 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_60,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(er,[status(thm)],[c_0_46])).

cnf(c_0_61,negated_conjecture,
    ( r2_hidden(esk6_0,k1_zfmisc_1(esk5_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_49])).

fof(c_0_62,plain,(
    ! [X44,X45] : k2_xboole_0(X44,X45) = k5_xboole_0(k5_xboole_0(X44,X45),k3_xboole_0(X44,X45)) ),
    inference(variable_rename,[status(thm)],[t94_xboole_1])).

cnf(c_0_63,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_64,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

fof(c_0_65,plain,(
    ! [X48,X49,X50] : k2_enumset1(X48,X48,X49,X50) = k1_enumset1(X48,X49,X50) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_66,plain,(
    ! [X51,X52,X53,X54] : k3_enumset1(X51,X51,X52,X53,X54) = k2_enumset1(X51,X52,X53,X54) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_67,plain,(
    ! [X55,X56,X57,X58,X59] : k4_enumset1(X55,X55,X56,X57,X58,X59) = k3_enumset1(X55,X56,X57,X58,X59) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_68,plain,(
    ! [X60,X61,X62,X63,X64,X65] : k5_enumset1(X60,X60,X61,X62,X63,X64,X65) = k4_enumset1(X60,X61,X62,X63,X64,X65) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_69,plain,(
    ! [X66,X67,X68,X69,X70,X71,X72] : k6_enumset1(X66,X66,X67,X68,X69,X70,X71,X72) = k5_enumset1(X66,X67,X68,X69,X70,X71,X72) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_70,plain,(
    ! [X36,X37] : k4_xboole_0(X36,k4_xboole_0(X36,X37)) = k3_xboole_0(X36,X37) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

cnf(c_0_71,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

fof(c_0_72,plain,(
    ! [X8,X9] : k3_xboole_0(X8,X9) = k3_xboole_0(X9,X8) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_73,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53,c_0_32]),c_0_32])).

cnf(c_0_74,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk3_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_75,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))) ),
    inference(er,[status(thm)],[c_0_55])).

cnf(c_0_76,plain,
    ( k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_77,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_58,c_0_56])).

cnf(c_0_78,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_79,negated_conjecture,
    ( r1_tarski(esk6_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

fof(c_0_80,plain,(
    ! [X42,X43] : k2_xboole_0(X42,X43) = k2_xboole_0(k5_xboole_0(X42,X43),k3_xboole_0(X42,X43)) ),
    inference(variable_rename,[status(thm)],[t93_xboole_1])).

cnf(c_0_81,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_82,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_83,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_84,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_85,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_86,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_87,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

fof(c_0_88,plain,(
    ! [X39,X40,X41] : k5_xboole_0(k5_xboole_0(X39,X40),X41) = k5_xboole_0(X39,k5_xboole_0(X40,X41)) ),
    inference(variable_rename,[status(thm)],[t91_xboole_1])).

cnf(c_0_89,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_90,plain,
    ( r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X1) ),
    inference(rw,[status(thm)],[c_0_71,c_0_32])).

cnf(c_0_91,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_92,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = X1
    | r2_hidden(esk3_1(k3_xboole_0(X1,k3_xboole_0(X1,X2))),k3_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_56])).

cnf(c_0_93,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(k1_xboole_0,X2)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_77])).

cnf(c_0_94,negated_conjecture,
    ( k3_xboole_0(esk6_0,esk5_0) = esk6_0 ),
    inference(spm,[status(thm)],[c_0_78,c_0_79])).

cnf(c_0_95,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_80])).

cnf(c_0_96,plain,
    ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) = k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_81,c_0_82]),c_0_83]),c_0_84]),c_0_85]),c_0_86]),c_0_87])).

cnf(c_0_97,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_88])).

cnf(c_0_98,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_89,c_0_32]),c_0_32])).

cnf(c_0_99,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_90]),c_0_91])).

cnf(c_0_100,plain,
    ( k3_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_92]),c_0_93])).

fof(c_0_101,plain,(
    ! [X12,X13,X14] :
      ( ( ~ v1_xboole_0(X12)
        | ~ r2_hidden(X13,X12) )
      & ( r2_hidden(esk1_1(X14),X14)
        | v1_xboole_0(X14) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_102,plain,
    ( r2_hidden(X1,X3)
    | ~ r1_tarski(X1,X2)
    | X3 != k1_zfmisc_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_103,negated_conjecture,
    ( k3_xboole_0(esk5_0,esk6_0) = esk6_0 ),
    inference(rw,[status(thm)],[c_0_94,c_0_91])).

cnf(c_0_104,plain,
    ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) = k3_tarski(k6_enumset1(k5_xboole_0(X1,X2),k5_xboole_0(X1,X2),k5_xboole_0(X1,X2),k5_xboole_0(X1,X2),k5_xboole_0(X1,X2),k5_xboole_0(X1,X2),k5_xboole_0(X1,X2),k3_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_95,c_0_82]),c_0_82]),c_0_83]),c_0_83]),c_0_84]),c_0_84]),c_0_85]),c_0_85]),c_0_86]),c_0_86]),c_0_87]),c_0_87])).

cnf(c_0_105,plain,
    ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_96,c_0_97])).

cnf(c_0_106,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_98,c_0_99])).

cnf(c_0_107,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_91,c_0_100])).

fof(c_0_108,plain,(
    ! [X85,X86] :
      ( ~ m1_subset_1(X86,k1_zfmisc_1(X85))
      | k3_subset_1(X85,X86) = k4_xboole_0(X85,X86) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

fof(c_0_109,plain,(
    ! [X88,X89,X90] :
      ( ~ m1_subset_1(X89,k1_zfmisc_1(X88))
      | ~ m1_subset_1(X90,k1_zfmisc_1(X88))
      | k4_subset_1(X88,X89,X90) = k2_xboole_0(X89,X90) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).

cnf(c_0_110,plain,
    ( m1_subset_1(X1,X2)
    | v1_xboole_0(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_111,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_101])).

cnf(c_0_112,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(er,[status(thm)],[c_0_102])).

cnf(c_0_113,negated_conjecture,
    ( r1_tarski(k5_xboole_0(esk5_0,esk6_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_90,c_0_103])).

cnf(c_0_114,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2))))) = k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_104,c_0_105]),c_0_97])).

cnf(c_0_115,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_107]),c_0_56])).

fof(c_0_116,plain,(
    ! [X84] : k2_subset_1(X84) = X84 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

cnf(c_0_117,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_108])).

cnf(c_0_118,plain,
    ( k4_subset_1(X2,X1,X3) = k2_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_109])).

cnf(c_0_119,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(csr,[status(thm)],[c_0_110,c_0_111])).

cnf(c_0_120,negated_conjecture,
    ( r2_hidden(k5_xboole_0(esk5_0,esk6_0),k1_zfmisc_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_112,c_0_113])).

cnf(c_0_121,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2))))) = k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_105,c_0_114])).

cnf(c_0_122,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,X2)) = X2 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_115]),c_0_76])).

cnf(c_0_123,negated_conjecture,
    ( k4_subset_1(esk5_0,esk6_0,k3_subset_1(esk5_0,esk6_0)) != k2_subset_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_124,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_116])).

cnf(c_0_125,plain,
    ( k3_subset_1(X2,X1) = k5_xboole_0(X2,k3_xboole_0(X2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_117,c_0_32])).

cnf(c_0_126,plain,
    ( k4_subset_1(X2,X1,X3) = k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_118,c_0_82]),c_0_83]),c_0_84]),c_0_85]),c_0_86]),c_0_87])).

cnf(c_0_127,negated_conjecture,
    ( m1_subset_1(k5_xboole_0(esk5_0,esk6_0),k1_zfmisc_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_119,c_0_120])).

cnf(c_0_128,negated_conjecture,
    ( k5_xboole_0(esk5_0,k3_xboole_0(esk6_0,k5_xboole_0(esk5_0,esk6_0))) = esk5_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_121,c_0_103]),c_0_91]),c_0_122]),c_0_115]),c_0_56])).

cnf(c_0_129,negated_conjecture,
    ( k4_subset_1(esk5_0,esk6_0,k3_subset_1(esk5_0,esk6_0)) != esk5_0 ),
    inference(rw,[status(thm)],[c_0_123,c_0_124])).

cnf(c_0_130,negated_conjecture,
    ( k3_subset_1(esk5_0,esk6_0) = k5_xboole_0(esk5_0,esk6_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_125,c_0_48]),c_0_103])).

cnf(c_0_131,negated_conjecture,
    ( k5_xboole_0(X1,k5_xboole_0(esk5_0,k5_xboole_0(esk6_0,k3_xboole_0(X1,k5_xboole_0(esk5_0,esk6_0))))) = k4_subset_1(esk5_0,X1,k5_xboole_0(esk5_0,esk6_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk5_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_126,c_0_127]),c_0_105]),c_0_97])).

cnf(c_0_132,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,X3)) = k5_xboole_0(X2,k5_xboole_0(X3,X1)) ),
    inference(spm,[status(thm)],[c_0_97,c_0_57])).

cnf(c_0_133,negated_conjecture,
    ( k3_xboole_0(esk6_0,k5_xboole_0(esk5_0,esk6_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_122,c_0_128]),c_0_115])).

cnf(c_0_134,negated_conjecture,
    ( k4_subset_1(esk5_0,esk6_0,k5_xboole_0(esk5_0,esk6_0)) != esk5_0 ),
    inference(rw,[status(thm)],[c_0_129,c_0_130])).

cnf(c_0_135,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_131,c_0_48]),c_0_132]),c_0_97]),c_0_57]),c_0_133]),c_0_56]),c_0_115]),c_0_56]),c_0_134]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n015.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 15:02:08 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.76/0.97  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.76/0.97  # and selection function SelectNegativeLiterals.
% 0.76/0.97  #
% 0.76/0.97  # Preprocessing time       : 0.027 s
% 0.76/0.97  # Presaturation interreduction done
% 0.76/0.97  
% 0.76/0.97  # Proof found!
% 0.76/0.97  # SZS status Theorem
% 0.76/0.97  # SZS output start CNFRefutation
% 0.76/0.97  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.76/0.97  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.76/0.97  fof(t25_subset_1, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k4_subset_1(X1,X2,k3_subset_1(X1,X2))=k2_subset_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_subset_1)).
% 0.76/0.97  fof(idempotence_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 0.76/0.97  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 0.76/0.97  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 0.76/0.97  fof(fc1_subset_1, axiom, ![X1]:~(v1_xboole_0(k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 0.76/0.97  fof(t47_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 0.76/0.97  fof(t5_boole, axiom, ![X1]:k5_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 0.76/0.97  fof(commutativity_k5_xboole_0, axiom, ![X1, X2]:k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 0.76/0.97  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.76/0.97  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.76/0.97  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.76/0.97  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 0.76/0.97  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.76/0.97  fof(t94_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_xboole_1)).
% 0.76/0.97  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.76/0.97  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.76/0.97  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 0.76/0.97  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 0.76/0.97  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 0.76/0.97  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.76/0.97  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.76/0.97  fof(t93_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t93_xboole_1)).
% 0.76/0.97  fof(t91_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 0.76/0.97  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.76/0.97  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 0.76/0.97  fof(redefinition_k4_subset_1, axiom, ![X1, X2, X3]:((m1_subset_1(X2,k1_zfmisc_1(X1))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>k4_subset_1(X1,X2,X3)=k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 0.76/0.97  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 0.76/0.97  fof(c_0_29, plain, ![X16, X17, X18, X19, X20, X21, X22, X23]:((((r2_hidden(X19,X16)|~r2_hidden(X19,X18)|X18!=k4_xboole_0(X16,X17))&(~r2_hidden(X19,X17)|~r2_hidden(X19,X18)|X18!=k4_xboole_0(X16,X17)))&(~r2_hidden(X20,X16)|r2_hidden(X20,X17)|r2_hidden(X20,X18)|X18!=k4_xboole_0(X16,X17)))&((~r2_hidden(esk2_3(X21,X22,X23),X23)|(~r2_hidden(esk2_3(X21,X22,X23),X21)|r2_hidden(esk2_3(X21,X22,X23),X22))|X23=k4_xboole_0(X21,X22))&((r2_hidden(esk2_3(X21,X22,X23),X21)|r2_hidden(esk2_3(X21,X22,X23),X23)|X23=k4_xboole_0(X21,X22))&(~r2_hidden(esk2_3(X21,X22,X23),X22)|r2_hidden(esk2_3(X21,X22,X23),X23)|X23=k4_xboole_0(X21,X22))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.76/0.97  fof(c_0_30, plain, ![X28, X29]:k4_xboole_0(X28,X29)=k5_xboole_0(X28,k3_xboole_0(X28,X29)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.76/0.97  cnf(c_0_31, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.76/0.97  cnf(c_0_32, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.76/0.97  fof(c_0_33, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k4_subset_1(X1,X2,k3_subset_1(X1,X2))=k2_subset_1(X1))), inference(assume_negation,[status(cth)],[t25_subset_1])).
% 0.76/0.97  cnf(c_0_34, plain, (X3!=k5_xboole_0(X4,k3_xboole_0(X4,X2))|~r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_31, c_0_32])).
% 0.76/0.97  fof(c_0_35, plain, ![X25]:k3_xboole_0(X25,X25)=X25, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).
% 0.76/0.97  fof(c_0_36, plain, ![X73, X74, X75, X76, X77, X78]:(((~r2_hidden(X75,X74)|r1_tarski(X75,X73)|X74!=k1_zfmisc_1(X73))&(~r1_tarski(X76,X73)|r2_hidden(X76,X74)|X74!=k1_zfmisc_1(X73)))&((~r2_hidden(esk4_2(X77,X78),X78)|~r1_tarski(esk4_2(X77,X78),X77)|X78=k1_zfmisc_1(X77))&(r2_hidden(esk4_2(X77,X78),X78)|r1_tarski(esk4_2(X77,X78),X77)|X78=k1_zfmisc_1(X77)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 0.76/0.97  fof(c_0_37, plain, ![X82, X83]:(((~m1_subset_1(X83,X82)|r2_hidden(X83,X82)|v1_xboole_0(X82))&(~r2_hidden(X83,X82)|m1_subset_1(X83,X82)|v1_xboole_0(X82)))&((~m1_subset_1(X83,X82)|v1_xboole_0(X83)|~v1_xboole_0(X82))&(~v1_xboole_0(X83)|m1_subset_1(X83,X82)|~v1_xboole_0(X82)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 0.76/0.97  fof(c_0_38, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(esk5_0))&k4_subset_1(esk5_0,esk6_0,k3_subset_1(esk5_0,esk6_0))!=k2_subset_1(esk5_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_33])])])).
% 0.76/0.97  fof(c_0_39, plain, ![X87]:~v1_xboole_0(k1_zfmisc_1(X87)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).
% 0.76/0.97  fof(c_0_40, plain, ![X34, X35]:k4_xboole_0(X34,k3_xboole_0(X34,X35))=k4_xboole_0(X34,X35), inference(variable_rename,[status(thm)],[t47_xboole_1])).
% 0.76/0.97  cnf(c_0_41, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.76/0.97  fof(c_0_42, plain, ![X38]:k5_xboole_0(X38,k1_xboole_0)=X38, inference(variable_rename,[status(thm)],[t5_boole])).
% 0.76/0.97  fof(c_0_43, plain, ![X10, X11]:k5_xboole_0(X10,X11)=k5_xboole_0(X11,X10), inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).
% 0.76/0.97  cnf(c_0_44, plain, (~r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_34])).
% 0.76/0.97  cnf(c_0_45, plain, (k3_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.76/0.97  cnf(c_0_46, plain, (r1_tarski(X1,X3)|~r2_hidden(X1,X2)|X2!=k1_zfmisc_1(X3)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.76/0.97  cnf(c_0_47, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.76/0.97  cnf(c_0_48, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.76/0.97  cnf(c_0_49, plain, (~v1_xboole_0(k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.76/0.97  fof(c_0_50, plain, ![X80, X81]:k3_tarski(k2_tarski(X80,X81))=k2_xboole_0(X80,X81), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.76/0.97  fof(c_0_51, plain, ![X46, X47]:k1_enumset1(X46,X46,X47)=k2_tarski(X46,X47), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.76/0.97  fof(c_0_52, plain, ![X32, X33]:r1_tarski(k4_xboole_0(X32,X33),X32), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.76/0.97  cnf(c_0_53, plain, (k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.76/0.97  fof(c_0_54, plain, ![X26]:(X26=k1_xboole_0|r2_hidden(esk3_1(X26),X26)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 0.76/0.97  cnf(c_0_55, plain, (r2_hidden(X1,X2)|X3!=k5_xboole_0(X2,k3_xboole_0(X2,X4))|~r2_hidden(X1,X3)), inference(rw,[status(thm)],[c_0_41, c_0_32])).
% 0.76/0.97  cnf(c_0_56, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.76/0.97  cnf(c_0_57, plain, (k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.76/0.97  cnf(c_0_58, plain, (~r2_hidden(X1,k5_xboole_0(X2,X2))|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.76/0.97  fof(c_0_59, plain, ![X30, X31]:(~r1_tarski(X30,X31)|k3_xboole_0(X30,X31)=X30), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.76/0.97  cnf(c_0_60, plain, (r1_tarski(X1,X2)|~r2_hidden(X1,k1_zfmisc_1(X2))), inference(er,[status(thm)],[c_0_46])).
% 0.76/0.97  cnf(c_0_61, negated_conjecture, (r2_hidden(esk6_0,k1_zfmisc_1(esk5_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_49])).
% 0.76/0.97  fof(c_0_62, plain, ![X44, X45]:k2_xboole_0(X44,X45)=k5_xboole_0(k5_xboole_0(X44,X45),k3_xboole_0(X44,X45)), inference(variable_rename,[status(thm)],[t94_xboole_1])).
% 0.76/0.97  cnf(c_0_63, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.76/0.97  cnf(c_0_64, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.76/0.97  fof(c_0_65, plain, ![X48, X49, X50]:k2_enumset1(X48,X48,X49,X50)=k1_enumset1(X48,X49,X50), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.76/0.97  fof(c_0_66, plain, ![X51, X52, X53, X54]:k3_enumset1(X51,X51,X52,X53,X54)=k2_enumset1(X51,X52,X53,X54), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.76/0.97  fof(c_0_67, plain, ![X55, X56, X57, X58, X59]:k4_enumset1(X55,X55,X56,X57,X58,X59)=k3_enumset1(X55,X56,X57,X58,X59), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.76/0.97  fof(c_0_68, plain, ![X60, X61, X62, X63, X64, X65]:k5_enumset1(X60,X60,X61,X62,X63,X64,X65)=k4_enumset1(X60,X61,X62,X63,X64,X65), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.76/0.97  fof(c_0_69, plain, ![X66, X67, X68, X69, X70, X71, X72]:k6_enumset1(X66,X66,X67,X68,X69,X70,X71,X72)=k5_enumset1(X66,X67,X68,X69,X70,X71,X72), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.76/0.97  fof(c_0_70, plain, ![X36, X37]:k4_xboole_0(X36,k4_xboole_0(X36,X37))=k3_xboole_0(X36,X37), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.76/0.97  cnf(c_0_71, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.76/0.97  fof(c_0_72, plain, ![X8, X9]:k3_xboole_0(X8,X9)=k3_xboole_0(X9,X8), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.76/0.97  cnf(c_0_73, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X1,X2)))=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53, c_0_32]), c_0_32])).
% 0.76/0.97  cnf(c_0_74, plain, (X1=k1_xboole_0|r2_hidden(esk3_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.76/0.97  cnf(c_0_75, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))), inference(er,[status(thm)],[c_0_55])).
% 0.76/0.97  cnf(c_0_76, plain, (k5_xboole_0(k1_xboole_0,X1)=X1), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.76/0.97  cnf(c_0_77, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_58, c_0_56])).
% 0.76/0.97  cnf(c_0_78, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.76/0.97  cnf(c_0_79, negated_conjecture, (r1_tarski(esk6_0,esk5_0)), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.76/0.97  fof(c_0_80, plain, ![X42, X43]:k2_xboole_0(X42,X43)=k2_xboole_0(k5_xboole_0(X42,X43),k3_xboole_0(X42,X43)), inference(variable_rename,[status(thm)],[t93_xboole_1])).
% 0.76/0.97  cnf(c_0_81, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.76/0.97  cnf(c_0_82, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_63, c_0_64])).
% 0.76/0.97  cnf(c_0_83, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.76/0.97  cnf(c_0_84, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_66])).
% 0.76/0.97  cnf(c_0_85, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.76/0.97  cnf(c_0_86, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.76/0.97  cnf(c_0_87, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_69])).
% 0.76/0.97  fof(c_0_88, plain, ![X39, X40, X41]:k5_xboole_0(k5_xboole_0(X39,X40),X41)=k5_xboole_0(X39,k5_xboole_0(X40,X41)), inference(variable_rename,[status(thm)],[t91_xboole_1])).
% 0.76/0.97  cnf(c_0_89, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_70])).
% 0.76/0.97  cnf(c_0_90, plain, (r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X1)), inference(rw,[status(thm)],[c_0_71, c_0_32])).
% 0.76/0.97  cnf(c_0_91, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_72])).
% 0.76/0.97  cnf(c_0_92, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X2))=X1|r2_hidden(esk3_1(k3_xboole_0(X1,k3_xboole_0(X1,X2))),k3_xboole_0(X1,k3_xboole_0(X1,X2)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_56])).
% 0.76/0.97  cnf(c_0_93, plain, (~r2_hidden(X1,k3_xboole_0(k1_xboole_0,X2))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_76]), c_0_77])).
% 0.76/0.97  cnf(c_0_94, negated_conjecture, (k3_xboole_0(esk6_0,esk5_0)=esk6_0), inference(spm,[status(thm)],[c_0_78, c_0_79])).
% 0.76/0.97  cnf(c_0_95, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_80])).
% 0.76/0.97  cnf(c_0_96, plain, (k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))=k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_81, c_0_82]), c_0_83]), c_0_84]), c_0_85]), c_0_86]), c_0_87])).
% 0.76/0.97  cnf(c_0_97, plain, (k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_88])).
% 0.76/0.97  cnf(c_0_98, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_89, c_0_32]), c_0_32])).
% 0.76/0.97  cnf(c_0_99, plain, (k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_90]), c_0_91])).
% 0.76/0.97  cnf(c_0_100, plain, (k3_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_92]), c_0_93])).
% 0.76/0.97  fof(c_0_101, plain, ![X12, X13, X14]:((~v1_xboole_0(X12)|~r2_hidden(X13,X12))&(r2_hidden(esk1_1(X14),X14)|v1_xboole_0(X14))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.76/0.97  cnf(c_0_102, plain, (r2_hidden(X1,X3)|~r1_tarski(X1,X2)|X3!=k1_zfmisc_1(X2)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.76/0.97  cnf(c_0_103, negated_conjecture, (k3_xboole_0(esk5_0,esk6_0)=esk6_0), inference(rw,[status(thm)],[c_0_94, c_0_91])).
% 0.76/0.97  cnf(c_0_104, plain, (k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))=k3_tarski(k6_enumset1(k5_xboole_0(X1,X2),k5_xboole_0(X1,X2),k5_xboole_0(X1,X2),k5_xboole_0(X1,X2),k5_xboole_0(X1,X2),k5_xboole_0(X1,X2),k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_95, c_0_82]), c_0_82]), c_0_83]), c_0_83]), c_0_84]), c_0_84]), c_0_85]), c_0_85]), c_0_86]), c_0_86]), c_0_87]), c_0_87])).
% 0.76/0.97  cnf(c_0_105, plain, (k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))=k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2)))), inference(rw,[status(thm)],[c_0_96, c_0_97])).
% 0.76/0.97  cnf(c_0_106, plain, (k5_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_98, c_0_99])).
% 0.76/0.97  cnf(c_0_107, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_91, c_0_100])).
% 0.76/0.97  fof(c_0_108, plain, ![X85, X86]:(~m1_subset_1(X86,k1_zfmisc_1(X85))|k3_subset_1(X85,X86)=k4_xboole_0(X85,X86)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 0.76/0.97  fof(c_0_109, plain, ![X88, X89, X90]:(~m1_subset_1(X89,k1_zfmisc_1(X88))|~m1_subset_1(X90,k1_zfmisc_1(X88))|k4_subset_1(X88,X89,X90)=k2_xboole_0(X89,X90)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).
% 0.76/0.97  cnf(c_0_110, plain, (m1_subset_1(X1,X2)|v1_xboole_0(X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.76/0.97  cnf(c_0_111, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_101])).
% 0.76/0.97  cnf(c_0_112, plain, (r2_hidden(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(er,[status(thm)],[c_0_102])).
% 0.76/0.97  cnf(c_0_113, negated_conjecture, (r1_tarski(k5_xboole_0(esk5_0,esk6_0),esk5_0)), inference(spm,[status(thm)],[c_0_90, c_0_103])).
% 0.76/0.97  cnf(c_0_114, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)))))=k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_104, c_0_105]), c_0_97])).
% 0.76/0.97  cnf(c_0_115, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106, c_0_107]), c_0_56])).
% 0.76/0.97  fof(c_0_116, plain, ![X84]:k2_subset_1(X84)=X84, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 0.76/0.97  cnf(c_0_117, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_108])).
% 0.76/0.97  cnf(c_0_118, plain, (k4_subset_1(X2,X1,X3)=k2_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_109])).
% 0.76/0.97  cnf(c_0_119, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(csr,[status(thm)],[c_0_110, c_0_111])).
% 0.76/0.97  cnf(c_0_120, negated_conjecture, (r2_hidden(k5_xboole_0(esk5_0,esk6_0),k1_zfmisc_1(esk5_0))), inference(spm,[status(thm)],[c_0_112, c_0_113])).
% 0.76/0.97  cnf(c_0_121, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)))))=k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2)))), inference(spm,[status(thm)],[c_0_105, c_0_114])).
% 0.76/0.97  cnf(c_0_122, plain, (k5_xboole_0(X1,k5_xboole_0(X1,X2))=X2), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97, c_0_115]), c_0_76])).
% 0.76/0.97  cnf(c_0_123, negated_conjecture, (k4_subset_1(esk5_0,esk6_0,k3_subset_1(esk5_0,esk6_0))!=k2_subset_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.76/0.97  cnf(c_0_124, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_116])).
% 0.76/0.97  cnf(c_0_125, plain, (k3_subset_1(X2,X1)=k5_xboole_0(X2,k3_xboole_0(X2,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_117, c_0_32])).
% 0.76/0.97  cnf(c_0_126, plain, (k4_subset_1(X2,X1,X3)=k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X3))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_118, c_0_82]), c_0_83]), c_0_84]), c_0_85]), c_0_86]), c_0_87])).
% 0.76/0.97  cnf(c_0_127, negated_conjecture, (m1_subset_1(k5_xboole_0(esk5_0,esk6_0),k1_zfmisc_1(esk5_0))), inference(spm,[status(thm)],[c_0_119, c_0_120])).
% 0.76/0.97  cnf(c_0_128, negated_conjecture, (k5_xboole_0(esk5_0,k3_xboole_0(esk6_0,k5_xboole_0(esk5_0,esk6_0)))=esk5_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_121, c_0_103]), c_0_91]), c_0_122]), c_0_115]), c_0_56])).
% 0.76/0.97  cnf(c_0_129, negated_conjecture, (k4_subset_1(esk5_0,esk6_0,k3_subset_1(esk5_0,esk6_0))!=esk5_0), inference(rw,[status(thm)],[c_0_123, c_0_124])).
% 0.76/0.97  cnf(c_0_130, negated_conjecture, (k3_subset_1(esk5_0,esk6_0)=k5_xboole_0(esk5_0,esk6_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_125, c_0_48]), c_0_103])).
% 0.76/0.97  cnf(c_0_131, negated_conjecture, (k5_xboole_0(X1,k5_xboole_0(esk5_0,k5_xboole_0(esk6_0,k3_xboole_0(X1,k5_xboole_0(esk5_0,esk6_0)))))=k4_subset_1(esk5_0,X1,k5_xboole_0(esk5_0,esk6_0))|~m1_subset_1(X1,k1_zfmisc_1(esk5_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_126, c_0_127]), c_0_105]), c_0_97])).
% 0.76/0.97  cnf(c_0_132, plain, (k5_xboole_0(X1,k5_xboole_0(X2,X3))=k5_xboole_0(X2,k5_xboole_0(X3,X1))), inference(spm,[status(thm)],[c_0_97, c_0_57])).
% 0.76/0.97  cnf(c_0_133, negated_conjecture, (k3_xboole_0(esk6_0,k5_xboole_0(esk5_0,esk6_0))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_122, c_0_128]), c_0_115])).
% 0.76/0.97  cnf(c_0_134, negated_conjecture, (k4_subset_1(esk5_0,esk6_0,k5_xboole_0(esk5_0,esk6_0))!=esk5_0), inference(rw,[status(thm)],[c_0_129, c_0_130])).
% 0.76/0.97  cnf(c_0_135, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_131, c_0_48]), c_0_132]), c_0_97]), c_0_57]), c_0_133]), c_0_56]), c_0_115]), c_0_56]), c_0_134]), ['proof']).
% 0.76/0.97  # SZS output end CNFRefutation
% 0.76/0.97  # Proof object total steps             : 136
% 0.76/0.97  # Proof object clause steps            : 77
% 0.76/0.97  # Proof object formula steps           : 59
% 0.76/0.97  # Proof object conjectures             : 19
% 0.76/0.97  # Proof object clause conjectures      : 16
% 0.76/0.97  # Proof object formula conjectures     : 3
% 0.76/0.97  # Proof object initial clauses used    : 33
% 0.76/0.97  # Proof object initial formulas used   : 29
% 0.76/0.97  # Proof object generating inferences   : 23
% 0.76/0.97  # Proof object simplifying inferences  : 68
% 0.76/0.97  # Training examples: 0 positive, 0 negative
% 0.76/0.97  # Parsed axioms                        : 29
% 0.76/0.97  # Removed by relevancy pruning/SinE    : 0
% 0.76/0.97  # Initial clauses                      : 42
% 0.76/0.97  # Removed in clause preprocessing      : 9
% 0.76/0.97  # Initial clauses in saturation        : 33
% 0.76/0.97  # Processed clauses                    : 2635
% 0.76/0.97  # ...of these trivial                  : 244
% 0.76/0.97  # ...subsumed                          : 1531
% 0.76/0.97  # ...remaining for further processing  : 860
% 0.76/0.97  # Other redundant clauses eliminated   : 75
% 0.76/0.97  # Clauses deleted for lack of memory   : 0
% 0.76/0.97  # Backward-subsumed                    : 31
% 0.76/0.97  # Backward-rewritten                   : 172
% 0.76/0.97  # Generated clauses                    : 54705
% 0.76/0.97  # ...of the previous two non-trivial   : 44971
% 0.76/0.97  # Contextual simplify-reflections      : 6
% 0.76/0.97  # Paramodulations                      : 54630
% 0.76/0.97  # Factorizations                       : 0
% 0.76/0.97  # Equation resolutions                 : 75
% 0.76/0.97  # Propositional unsat checks           : 0
% 0.76/0.97  #    Propositional check models        : 0
% 0.76/0.97  #    Propositional check unsatisfiable : 0
% 0.76/0.97  #    Propositional clauses             : 0
% 0.76/0.97  #    Propositional clauses after purity: 0
% 0.76/0.97  #    Propositional unsat core size     : 0
% 0.76/0.97  #    Propositional preprocessing time  : 0.000
% 0.76/0.97  #    Propositional encoding time       : 0.000
% 0.76/0.97  #    Propositional solver time         : 0.000
% 0.76/0.97  #    Success case prop preproc time    : 0.000
% 0.76/0.97  #    Success case prop encoding time   : 0.000
% 0.76/0.97  #    Success case prop solver time     : 0.000
% 0.76/0.97  # Current number of processed clauses  : 619
% 0.76/0.97  #    Positive orientable unit clauses  : 223
% 0.76/0.97  #    Positive unorientable unit clauses: 9
% 0.76/0.97  #    Negative unit clauses             : 6
% 0.76/0.97  #    Non-unit-clauses                  : 381
% 0.76/0.97  # Current number of unprocessed clauses: 41637
% 0.76/0.97  # ...number of literals in the above   : 179281
% 0.76/0.97  # Current number of archived formulas  : 0
% 0.76/0.97  # Current number of archived clauses   : 245
% 0.76/0.97  # Clause-clause subsumption calls (NU) : 40013
% 0.76/0.97  # Rec. Clause-clause subsumption calls : 23935
% 0.76/0.97  # Non-unit clause-clause subsumptions  : 1084
% 0.76/0.97  # Unit Clause-clause subsumption calls : 11291
% 0.76/0.97  # Rewrite failures with RHS unbound    : 0
% 0.76/0.97  # BW rewrite match attempts            : 498
% 0.76/0.97  # BW rewrite match successes           : 208
% 0.76/0.97  # Condensation attempts                : 0
% 0.76/0.97  # Condensation successes               : 0
% 0.76/0.97  # Termbank termtop insertions          : 894833
% 0.76/0.97  
% 0.76/0.97  # -------------------------------------------------
% 0.76/0.97  # User time                : 0.602 s
% 0.76/0.97  # System time              : 0.028 s
% 0.76/0.97  # Total time               : 0.630 s
% 0.76/0.97  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------
