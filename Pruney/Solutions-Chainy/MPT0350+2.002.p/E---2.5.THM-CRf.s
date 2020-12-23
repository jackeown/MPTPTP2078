%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:45:14 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 596 expanded)
%              Number of clauses        :   61 ( 260 expanded)
%              Number of leaves         :   23 ( 163 expanded)
%              Depth                    :    9
%              Number of atoms          :  173 ( 883 expanded)
%              Number of equality atoms :   90 ( 529 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal clause size      :   12 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t25_subset_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k4_subset_1(X1,X2,k3_subset_1(X1,X2)) = k2_subset_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_subset_1)).

fof(redefinition_k4_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => k4_subset_1(X1,X2,X3) = k2_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t94_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

fof(d6_xboole_0,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(fc1_subset_1,axiom,(
    ! [X1] : ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(t22_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k3_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(dt_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t112_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2)) = k3_xboole_0(k5_xboole_0(X1,X3),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_xboole_1)).

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(t5_boole,axiom,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(c_0_23,plain,(
    ! [X38,X39] : k3_tarski(k2_tarski(X38,X39)) = k2_xboole_0(X38,X39) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_24,plain,(
    ! [X26,X27] : k1_enumset1(X26,X26,X27) = k2_tarski(X26,X27) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_25,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X1))
       => k4_subset_1(X1,X2,k3_subset_1(X1,X2)) = k2_subset_1(X1) ) ),
    inference(assume_negation,[status(cth)],[t25_subset_1])).

fof(c_0_26,plain,(
    ! [X48,X49,X50] :
      ( ~ m1_subset_1(X49,k1_zfmisc_1(X48))
      | ~ m1_subset_1(X50,k1_zfmisc_1(X48))
      | k4_subset_1(X48,X49,X50) = k2_xboole_0(X49,X50) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).

cnf(c_0_27,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_28,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_29,plain,(
    ! [X28,X29,X30] : k2_enumset1(X28,X28,X29,X30) = k1_enumset1(X28,X29,X30) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_30,plain,(
    ! [X22,X23] : k2_xboole_0(X22,X23) = k5_xboole_0(k5_xboole_0(X22,X23),k3_xboole_0(X22,X23)) ),
    inference(variable_rename,[status(thm)],[t94_xboole_1])).

fof(c_0_31,plain,(
    ! [X6,X7] : k5_xboole_0(X6,X7) = k2_xboole_0(k4_xboole_0(X6,X7),k4_xboole_0(X7,X6)) ),
    inference(variable_rename,[status(thm)],[d6_xboole_0])).

fof(c_0_32,plain,(
    ! [X9,X10] : k4_xboole_0(X9,X10) = k5_xboole_0(X9,k3_xboole_0(X9,X10)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_33,plain,(
    ! [X24,X25] : k2_tarski(X24,X25) = k2_tarski(X25,X24) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

fof(c_0_34,plain,(
    ! [X31,X32,X33,X34,X35,X36] :
      ( ( ~ r2_hidden(X33,X32)
        | r1_tarski(X33,X31)
        | X32 != k1_zfmisc_1(X31) )
      & ( ~ r1_tarski(X34,X31)
        | r2_hidden(X34,X32)
        | X32 != k1_zfmisc_1(X31) )
      & ( ~ r2_hidden(esk1_2(X35,X36),X36)
        | ~ r1_tarski(esk1_2(X35,X36),X35)
        | X36 = k1_zfmisc_1(X35) )
      & ( r2_hidden(esk1_2(X35,X36),X36)
        | r1_tarski(esk1_2(X35,X36),X35)
        | X36 = k1_zfmisc_1(X35) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

fof(c_0_35,plain,(
    ! [X40,X41] :
      ( ( ~ m1_subset_1(X41,X40)
        | r2_hidden(X41,X40)
        | v1_xboole_0(X40) )
      & ( ~ r2_hidden(X41,X40)
        | m1_subset_1(X41,X40)
        | v1_xboole_0(X40) )
      & ( ~ m1_subset_1(X41,X40)
        | v1_xboole_0(X41)
        | ~ v1_xboole_0(X40) )
      & ( ~ v1_xboole_0(X41)
        | m1_subset_1(X41,X40)
        | ~ v1_xboole_0(X40) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

fof(c_0_36,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))
    & k4_subset_1(esk2_0,esk3_0,k3_subset_1(esk2_0,esk3_0)) != k2_subset_1(esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_25])])])).

fof(c_0_37,plain,(
    ! [X47] : ~ v1_xboole_0(k1_zfmisc_1(X47)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).

cnf(c_0_38,plain,
    ( k4_subset_1(X2,X1,X3) = k2_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_39,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_40,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_41,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_42,plain,
    ( k5_xboole_0(X1,X2) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_43,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_44,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_45,plain,
    ( r1_tarski(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_46,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_47,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_48,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

fof(c_0_49,plain,(
    ! [X14,X15] : k2_xboole_0(X14,k3_xboole_0(X14,X15)) = X14 ),
    inference(variable_rename,[status(thm)],[t22_xboole_1])).

fof(c_0_50,plain,(
    ! [X16,X17] :
      ( ~ r1_tarski(X16,X17)
      | k3_xboole_0(X16,X17) = X16 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

fof(c_0_51,plain,(
    ! [X18] : r1_tarski(k1_xboole_0,X18) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_52,plain,
    ( k4_subset_1(X2,X1,X3) = k3_tarski(k2_enumset1(X1,X1,X1,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_39]),c_0_40])).

cnf(c_0_53,plain,
    ( k3_tarski(k2_enumset1(X1,X1,X1,X2)) = k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_39]),c_0_40])).

cnf(c_0_54,plain,
    ( k5_xboole_0(X1,X2) = k3_tarski(k2_enumset1(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k5_xboole_0(X1,k3_xboole_0(X1,X2)),k5_xboole_0(X1,k3_xboole_0(X1,X2)),k5_xboole_0(X2,k3_xboole_0(X2,X1)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_39]),c_0_43]),c_0_43]),c_0_43]),c_0_40])).

cnf(c_0_55,plain,
    ( k2_enumset1(X1,X1,X1,X2) = k2_enumset1(X2,X2,X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44,c_0_28]),c_0_28]),c_0_40]),c_0_40])).

fof(c_0_56,plain,(
    ! [X45,X46] :
      ( ~ m1_subset_1(X46,k1_zfmisc_1(X45))
      | m1_subset_1(k3_subset_1(X45,X46),k1_zfmisc_1(X45)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).

fof(c_0_57,plain,(
    ! [X43,X44] :
      ( ~ m1_subset_1(X44,k1_zfmisc_1(X43))
      | k3_subset_1(X43,X44) = k4_xboole_0(X43,X44) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

cnf(c_0_58,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(er,[status(thm)],[c_0_45])).

cnf(c_0_59,negated_conjecture,
    ( r2_hidden(esk3_0,k1_zfmisc_1(esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_48])).

fof(c_0_60,plain,(
    ! [X4,X5] : k3_xboole_0(X4,X5) = k3_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_61,plain,
    ( k2_xboole_0(X1,k3_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

fof(c_0_62,plain,(
    ! [X19,X20] : k4_xboole_0(X19,k4_xboole_0(X19,X20)) = k3_xboole_0(X19,X20) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

cnf(c_0_63,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_64,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_65,plain,
    ( k4_subset_1(X1,X2,X3) = k5_xboole_0(k5_xboole_0(X2,X3),k3_xboole_0(X2,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_66,plain,
    ( m1_subset_1(X1,X2)
    | v1_xboole_0(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_67,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k5_xboole_0(X2,k3_xboole_0(X2,X1))),k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k5_xboole_0(X2,k3_xboole_0(X2,X1)))) = k5_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_54,c_0_53])).

cnf(c_0_68,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X2,X1),k3_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_55]),c_0_53])).

cnf(c_0_69,plain,
    ( m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_70,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_71,negated_conjecture,
    ( r1_tarski(esk3_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_72,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

fof(c_0_73,plain,(
    ! [X11,X12,X13] : k5_xboole_0(k3_xboole_0(X11,X12),k3_xboole_0(X13,X12)) = k3_xboole_0(k5_xboole_0(X11,X13),X12) ),
    inference(variable_rename,[status(thm)],[t112_xboole_1])).

fof(c_0_74,plain,(
    ! [X8] : k3_xboole_0(X8,X8) = X8 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

cnf(c_0_75,plain,
    ( k3_tarski(k2_enumset1(X1,X1,X1,k3_xboole_0(X1,X2))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_39]),c_0_40])).

cnf(c_0_76,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_77,plain,
    ( k3_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

fof(c_0_78,plain,(
    ! [X21] : k5_xboole_0(X21,k1_xboole_0) = X21 ),
    inference(variable_rename,[status(thm)],[t5_boole])).

fof(c_0_79,plain,(
    ! [X42] : k2_subset_1(X42) = X42 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

cnf(c_0_80,plain,
    ( k4_subset_1(X1,X2,X3) = k5_xboole_0(k5_xboole_0(X2,X3),k3_xboole_0(X2,X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X3,k1_zfmisc_1(X1)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_48])).

cnf(c_0_81,plain,
    ( k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_67])).

cnf(c_0_82,plain,
    ( r2_hidden(k3_subset_1(X1,X2),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_69]),c_0_48])).

cnf(c_0_83,plain,
    ( k3_subset_1(X2,X1) = k5_xboole_0(X2,k3_xboole_0(X2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_70,c_0_43])).

cnf(c_0_84,negated_conjecture,
    ( k3_xboole_0(esk2_0,esk3_0) = esk3_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_71]),c_0_72])).

cnf(c_0_85,plain,
    ( k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2)) = k3_xboole_0(k5_xboole_0(X1,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_86,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

cnf(c_0_87,plain,
    ( k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k3_xboole_0(X1,k3_xboole_0(X1,X2))) = X1 ),
    inference(rw,[status(thm)],[c_0_75,c_0_53])).

cnf(c_0_88,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_76,c_0_43]),c_0_43])).

cnf(c_0_89,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_72,c_0_77])).

cnf(c_0_90,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_78])).

cnf(c_0_91,negated_conjecture,
    ( k4_subset_1(esk2_0,esk3_0,k3_subset_1(esk2_0,esk3_0)) != k2_subset_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_92,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_79])).

cnf(c_0_93,plain,
    ( k4_subset_1(X1,X2,X3) = k5_xboole_0(k3_xboole_0(X2,X3),k5_xboole_0(X2,X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X3,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_80,c_0_81])).

cnf(c_0_94,negated_conjecture,
    ( r2_hidden(k3_subset_1(esk2_0,esk3_0),k1_zfmisc_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_82,c_0_47])).

cnf(c_0_95,negated_conjecture,
    ( k3_subset_1(esk2_0,esk3_0) = k5_xboole_0(esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_47]),c_0_84])).

cnf(c_0_96,plain,
    ( k5_xboole_0(k3_xboole_0(X1,X2),X2) = k3_xboole_0(X2,k5_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_86]),c_0_72])).

cnf(c_0_97,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(esk2_0,esk3_0),esk3_0) = esk2_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_84]),c_0_84])).

cnf(c_0_98,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X1),X1) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_86]),c_0_86])).

cnf(c_0_99,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_89]),c_0_90]),c_0_86])).

cnf(c_0_100,negated_conjecture,
    ( k4_subset_1(esk2_0,esk3_0,k3_subset_1(esk2_0,esk3_0)) != esk2_0 ),
    inference(rw,[status(thm)],[c_0_91,c_0_92])).

cnf(c_0_101,negated_conjecture,
    ( k4_subset_1(esk2_0,esk3_0,X1) = k5_xboole_0(k3_xboole_0(esk3_0,X1),k5_xboole_0(esk3_0,X1))
    | ~ r2_hidden(X1,k1_zfmisc_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_93,c_0_47])).

cnf(c_0_102,negated_conjecture,
    ( r2_hidden(k5_xboole_0(esk2_0,esk3_0),k1_zfmisc_1(esk2_0)) ),
    inference(rw,[status(thm)],[c_0_94,c_0_95])).

cnf(c_0_103,negated_conjecture,
    ( k3_xboole_0(esk3_0,k5_xboole_0(X1,esk3_0)) = k3_xboole_0(k5_xboole_0(X1,esk2_0),esk3_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_84]),c_0_96])).

cnf(c_0_104,negated_conjecture,
    ( k5_xboole_0(esk3_0,k5_xboole_0(esk2_0,esk3_0)) = esk2_0 ),
    inference(rw,[status(thm)],[c_0_97,c_0_81])).

cnf(c_0_105,plain,
    ( k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_98,c_0_99])).

cnf(c_0_106,negated_conjecture,
    ( k4_subset_1(esk2_0,esk3_0,k5_xboole_0(esk2_0,esk3_0)) != esk2_0 ),
    inference(rw,[status(thm)],[c_0_100,c_0_95])).

cnf(c_0_107,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_102]),c_0_103]),c_0_99]),c_0_77]),c_0_104]),c_0_105]),c_0_106]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:07:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.40  # AutoSched0-Mode selected heuristic G_E___107_B42_F1_PI_SE_Q4_CS_SP_PS_S0YI
% 0.13/0.40  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.13/0.40  #
% 0.13/0.40  # Preprocessing time       : 0.028 s
% 0.13/0.40  # Presaturation interreduction done
% 0.13/0.40  
% 0.13/0.40  # Proof found!
% 0.13/0.40  # SZS status Theorem
% 0.13/0.40  # SZS output start CNFRefutation
% 0.13/0.40  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.13/0.40  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.13/0.40  fof(t25_subset_1, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k4_subset_1(X1,X2,k3_subset_1(X1,X2))=k2_subset_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_subset_1)).
% 0.13/0.40  fof(redefinition_k4_subset_1, axiom, ![X1, X2, X3]:((m1_subset_1(X2,k1_zfmisc_1(X1))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>k4_subset_1(X1,X2,X3)=k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 0.13/0.40  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.13/0.40  fof(t94_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_xboole_1)).
% 0.13/0.40  fof(d6_xboole_0, axiom, ![X1, X2]:k5_xboole_0(X1,X2)=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_xboole_0)).
% 0.13/0.40  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.13/0.40  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 0.13/0.40  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 0.13/0.40  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 0.13/0.40  fof(fc1_subset_1, axiom, ![X1]:~(v1_xboole_0(k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 0.13/0.40  fof(t22_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k3_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_xboole_1)).
% 0.13/0.40  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.13/0.40  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.13/0.40  fof(dt_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 0.13/0.40  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 0.13/0.40  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.13/0.40  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.13/0.40  fof(t112_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2))=k3_xboole_0(k5_xboole_0(X1,X3),X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t112_xboole_1)).
% 0.13/0.40  fof(idempotence_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 0.13/0.40  fof(t5_boole, axiom, ![X1]:k5_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 0.13/0.40  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 0.13/0.40  fof(c_0_23, plain, ![X38, X39]:k3_tarski(k2_tarski(X38,X39))=k2_xboole_0(X38,X39), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.13/0.40  fof(c_0_24, plain, ![X26, X27]:k1_enumset1(X26,X26,X27)=k2_tarski(X26,X27), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.13/0.40  fof(c_0_25, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k4_subset_1(X1,X2,k3_subset_1(X1,X2))=k2_subset_1(X1))), inference(assume_negation,[status(cth)],[t25_subset_1])).
% 0.13/0.40  fof(c_0_26, plain, ![X48, X49, X50]:(~m1_subset_1(X49,k1_zfmisc_1(X48))|~m1_subset_1(X50,k1_zfmisc_1(X48))|k4_subset_1(X48,X49,X50)=k2_xboole_0(X49,X50)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).
% 0.13/0.40  cnf(c_0_27, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.40  cnf(c_0_28, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.13/0.40  fof(c_0_29, plain, ![X28, X29, X30]:k2_enumset1(X28,X28,X29,X30)=k1_enumset1(X28,X29,X30), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.13/0.40  fof(c_0_30, plain, ![X22, X23]:k2_xboole_0(X22,X23)=k5_xboole_0(k5_xboole_0(X22,X23),k3_xboole_0(X22,X23)), inference(variable_rename,[status(thm)],[t94_xboole_1])).
% 0.13/0.40  fof(c_0_31, plain, ![X6, X7]:k5_xboole_0(X6,X7)=k2_xboole_0(k4_xboole_0(X6,X7),k4_xboole_0(X7,X6)), inference(variable_rename,[status(thm)],[d6_xboole_0])).
% 0.13/0.40  fof(c_0_32, plain, ![X9, X10]:k4_xboole_0(X9,X10)=k5_xboole_0(X9,k3_xboole_0(X9,X10)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.13/0.40  fof(c_0_33, plain, ![X24, X25]:k2_tarski(X24,X25)=k2_tarski(X25,X24), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 0.13/0.40  fof(c_0_34, plain, ![X31, X32, X33, X34, X35, X36]:(((~r2_hidden(X33,X32)|r1_tarski(X33,X31)|X32!=k1_zfmisc_1(X31))&(~r1_tarski(X34,X31)|r2_hidden(X34,X32)|X32!=k1_zfmisc_1(X31)))&((~r2_hidden(esk1_2(X35,X36),X36)|~r1_tarski(esk1_2(X35,X36),X35)|X36=k1_zfmisc_1(X35))&(r2_hidden(esk1_2(X35,X36),X36)|r1_tarski(esk1_2(X35,X36),X35)|X36=k1_zfmisc_1(X35)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 0.13/0.40  fof(c_0_35, plain, ![X40, X41]:(((~m1_subset_1(X41,X40)|r2_hidden(X41,X40)|v1_xboole_0(X40))&(~r2_hidden(X41,X40)|m1_subset_1(X41,X40)|v1_xboole_0(X40)))&((~m1_subset_1(X41,X40)|v1_xboole_0(X41)|~v1_xboole_0(X40))&(~v1_xboole_0(X41)|m1_subset_1(X41,X40)|~v1_xboole_0(X40)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 0.13/0.40  fof(c_0_36, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))&k4_subset_1(esk2_0,esk3_0,k3_subset_1(esk2_0,esk3_0))!=k2_subset_1(esk2_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_25])])])).
% 0.13/0.40  fof(c_0_37, plain, ![X47]:~v1_xboole_0(k1_zfmisc_1(X47)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).
% 0.13/0.40  cnf(c_0_38, plain, (k4_subset_1(X2,X1,X3)=k2_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.13/0.40  cnf(c_0_39, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_27, c_0_28])).
% 0.13/0.40  cnf(c_0_40, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.13/0.40  cnf(c_0_41, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.13/0.40  cnf(c_0_42, plain, (k5_xboole_0(X1,X2)=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.13/0.40  cnf(c_0_43, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.13/0.40  cnf(c_0_44, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.13/0.40  cnf(c_0_45, plain, (r1_tarski(X1,X3)|~r2_hidden(X1,X2)|X2!=k1_zfmisc_1(X3)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.13/0.40  cnf(c_0_46, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.13/0.40  cnf(c_0_47, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.13/0.40  cnf(c_0_48, plain, (~v1_xboole_0(k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.13/0.40  fof(c_0_49, plain, ![X14, X15]:k2_xboole_0(X14,k3_xboole_0(X14,X15))=X14, inference(variable_rename,[status(thm)],[t22_xboole_1])).
% 0.13/0.40  fof(c_0_50, plain, ![X16, X17]:(~r1_tarski(X16,X17)|k3_xboole_0(X16,X17)=X16), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.13/0.40  fof(c_0_51, plain, ![X18]:r1_tarski(k1_xboole_0,X18), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.13/0.40  cnf(c_0_52, plain, (k4_subset_1(X2,X1,X3)=k3_tarski(k2_enumset1(X1,X1,X1,X3))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_39]), c_0_40])).
% 0.13/0.40  cnf(c_0_53, plain, (k3_tarski(k2_enumset1(X1,X1,X1,X2))=k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_39]), c_0_40])).
% 0.13/0.40  cnf(c_0_54, plain, (k5_xboole_0(X1,X2)=k3_tarski(k2_enumset1(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k5_xboole_0(X1,k3_xboole_0(X1,X2)),k5_xboole_0(X1,k3_xboole_0(X1,X2)),k5_xboole_0(X2,k3_xboole_0(X2,X1))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42, c_0_39]), c_0_43]), c_0_43]), c_0_43]), c_0_40])).
% 0.13/0.40  cnf(c_0_55, plain, (k2_enumset1(X1,X1,X1,X2)=k2_enumset1(X2,X2,X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44, c_0_28]), c_0_28]), c_0_40]), c_0_40])).
% 0.13/0.40  fof(c_0_56, plain, ![X45, X46]:(~m1_subset_1(X46,k1_zfmisc_1(X45))|m1_subset_1(k3_subset_1(X45,X46),k1_zfmisc_1(X45))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).
% 0.13/0.40  fof(c_0_57, plain, ![X43, X44]:(~m1_subset_1(X44,k1_zfmisc_1(X43))|k3_subset_1(X43,X44)=k4_xboole_0(X43,X44)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 0.13/0.40  cnf(c_0_58, plain, (r1_tarski(X1,X2)|~r2_hidden(X1,k1_zfmisc_1(X2))), inference(er,[status(thm)],[c_0_45])).
% 0.13/0.40  cnf(c_0_59, negated_conjecture, (r2_hidden(esk3_0,k1_zfmisc_1(esk2_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_48])).
% 0.13/0.40  fof(c_0_60, plain, ![X4, X5]:k3_xboole_0(X4,X5)=k3_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.13/0.40  cnf(c_0_61, plain, (k2_xboole_0(X1,k3_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.13/0.40  fof(c_0_62, plain, ![X19, X20]:k4_xboole_0(X19,k4_xboole_0(X19,X20))=k3_xboole_0(X19,X20), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.13/0.40  cnf(c_0_63, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.13/0.40  cnf(c_0_64, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.13/0.40  cnf(c_0_65, plain, (k4_subset_1(X1,X2,X3)=k5_xboole_0(k5_xboole_0(X2,X3),k3_xboole_0(X2,X3))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_52, c_0_53])).
% 0.13/0.40  cnf(c_0_66, plain, (m1_subset_1(X1,X2)|v1_xboole_0(X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.13/0.40  cnf(c_0_67, plain, (k5_xboole_0(k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k5_xboole_0(X2,k3_xboole_0(X2,X1))),k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k5_xboole_0(X2,k3_xboole_0(X2,X1))))=k5_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_54, c_0_53])).
% 0.13/0.40  cnf(c_0_68, plain, (k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2))=k5_xboole_0(k5_xboole_0(X2,X1),k3_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_55]), c_0_53])).
% 0.13/0.40  cnf(c_0_69, plain, (m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.13/0.40  cnf(c_0_70, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.13/0.40  cnf(c_0_71, negated_conjecture, (r1_tarski(esk3_0,esk2_0)), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.13/0.40  cnf(c_0_72, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.13/0.40  fof(c_0_73, plain, ![X11, X12, X13]:k5_xboole_0(k3_xboole_0(X11,X12),k3_xboole_0(X13,X12))=k3_xboole_0(k5_xboole_0(X11,X13),X12), inference(variable_rename,[status(thm)],[t112_xboole_1])).
% 0.13/0.40  fof(c_0_74, plain, ![X8]:k3_xboole_0(X8,X8)=X8, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).
% 0.13/0.40  cnf(c_0_75, plain, (k3_tarski(k2_enumset1(X1,X1,X1,k3_xboole_0(X1,X2)))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61, c_0_39]), c_0_40])).
% 0.13/0.40  cnf(c_0_76, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.13/0.40  cnf(c_0_77, plain, (k3_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_63, c_0_64])).
% 0.13/0.40  fof(c_0_78, plain, ![X21]:k5_xboole_0(X21,k1_xboole_0)=X21, inference(variable_rename,[status(thm)],[t5_boole])).
% 0.13/0.40  fof(c_0_79, plain, ![X42]:k2_subset_1(X42)=X42, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 0.13/0.40  cnf(c_0_80, plain, (k4_subset_1(X1,X2,X3)=k5_xboole_0(k5_xboole_0(X2,X3),k3_xboole_0(X2,X3))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r2_hidden(X3,k1_zfmisc_1(X1))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_48])).
% 0.13/0.40  cnf(c_0_81, plain, (k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_67])).
% 0.13/0.40  cnf(c_0_82, plain, (r2_hidden(k3_subset_1(X1,X2),k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_69]), c_0_48])).
% 0.13/0.40  cnf(c_0_83, plain, (k3_subset_1(X2,X1)=k5_xboole_0(X2,k3_xboole_0(X2,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_70, c_0_43])).
% 0.13/0.40  cnf(c_0_84, negated_conjecture, (k3_xboole_0(esk2_0,esk3_0)=esk3_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_71]), c_0_72])).
% 0.13/0.40  cnf(c_0_85, plain, (k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2))=k3_xboole_0(k5_xboole_0(X1,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_73])).
% 0.13/0.40  cnf(c_0_86, plain, (k3_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_74])).
% 0.13/0.40  cnf(c_0_87, plain, (k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k3_xboole_0(X1,k3_xboole_0(X1,X2)))=X1), inference(rw,[status(thm)],[c_0_75, c_0_53])).
% 0.13/0.40  cnf(c_0_88, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_76, c_0_43]), c_0_43])).
% 0.13/0.40  cnf(c_0_89, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_72, c_0_77])).
% 0.13/0.40  cnf(c_0_90, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_78])).
% 0.13/0.40  cnf(c_0_91, negated_conjecture, (k4_subset_1(esk2_0,esk3_0,k3_subset_1(esk2_0,esk3_0))!=k2_subset_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.13/0.40  cnf(c_0_92, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_79])).
% 0.13/0.40  cnf(c_0_93, plain, (k4_subset_1(X1,X2,X3)=k5_xboole_0(k3_xboole_0(X2,X3),k5_xboole_0(X2,X3))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r2_hidden(X3,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_80, c_0_81])).
% 0.13/0.40  cnf(c_0_94, negated_conjecture, (r2_hidden(k3_subset_1(esk2_0,esk3_0),k1_zfmisc_1(esk2_0))), inference(spm,[status(thm)],[c_0_82, c_0_47])).
% 0.13/0.40  cnf(c_0_95, negated_conjecture, (k3_subset_1(esk2_0,esk3_0)=k5_xboole_0(esk2_0,esk3_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_47]), c_0_84])).
% 0.13/0.40  cnf(c_0_96, plain, (k5_xboole_0(k3_xboole_0(X1,X2),X2)=k3_xboole_0(X2,k5_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_86]), c_0_72])).
% 0.13/0.40  cnf(c_0_97, negated_conjecture, (k5_xboole_0(k5_xboole_0(esk2_0,esk3_0),esk3_0)=esk2_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_84]), c_0_84])).
% 0.13/0.40  cnf(c_0_98, plain, (k5_xboole_0(k5_xboole_0(X1,X1),X1)=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_86]), c_0_86])).
% 0.13/0.40  cnf(c_0_99, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_89]), c_0_90]), c_0_86])).
% 0.13/0.40  cnf(c_0_100, negated_conjecture, (k4_subset_1(esk2_0,esk3_0,k3_subset_1(esk2_0,esk3_0))!=esk2_0), inference(rw,[status(thm)],[c_0_91, c_0_92])).
% 0.13/0.40  cnf(c_0_101, negated_conjecture, (k4_subset_1(esk2_0,esk3_0,X1)=k5_xboole_0(k3_xboole_0(esk3_0,X1),k5_xboole_0(esk3_0,X1))|~r2_hidden(X1,k1_zfmisc_1(esk2_0))), inference(spm,[status(thm)],[c_0_93, c_0_47])).
% 0.13/0.40  cnf(c_0_102, negated_conjecture, (r2_hidden(k5_xboole_0(esk2_0,esk3_0),k1_zfmisc_1(esk2_0))), inference(rw,[status(thm)],[c_0_94, c_0_95])).
% 0.13/0.40  cnf(c_0_103, negated_conjecture, (k3_xboole_0(esk3_0,k5_xboole_0(X1,esk3_0))=k3_xboole_0(k5_xboole_0(X1,esk2_0),esk3_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_84]), c_0_96])).
% 0.13/0.40  cnf(c_0_104, negated_conjecture, (k5_xboole_0(esk3_0,k5_xboole_0(esk2_0,esk3_0))=esk2_0), inference(rw,[status(thm)],[c_0_97, c_0_81])).
% 0.13/0.40  cnf(c_0_105, plain, (k5_xboole_0(k1_xboole_0,X1)=X1), inference(spm,[status(thm)],[c_0_98, c_0_99])).
% 0.13/0.40  cnf(c_0_106, negated_conjecture, (k4_subset_1(esk2_0,esk3_0,k5_xboole_0(esk2_0,esk3_0))!=esk2_0), inference(rw,[status(thm)],[c_0_100, c_0_95])).
% 0.13/0.40  cnf(c_0_107, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101, c_0_102]), c_0_103]), c_0_99]), c_0_77]), c_0_104]), c_0_105]), c_0_106]), ['proof']).
% 0.13/0.40  # SZS output end CNFRefutation
% 0.13/0.40  # Proof object total steps             : 108
% 0.13/0.40  # Proof object clause steps            : 61
% 0.13/0.40  # Proof object formula steps           : 47
% 0.13/0.40  # Proof object conjectures             : 18
% 0.13/0.40  # Proof object clause conjectures      : 15
% 0.13/0.40  # Proof object formula conjectures     : 3
% 0.13/0.40  # Proof object initial clauses used    : 25
% 0.13/0.40  # Proof object initial formulas used   : 23
% 0.13/0.40  # Proof object generating inferences   : 19
% 0.13/0.40  # Proof object simplifying inferences  : 47
% 0.13/0.40  # Training examples: 0 positive, 0 negative
% 0.13/0.40  # Parsed axioms                        : 23
% 0.13/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.40  # Initial clauses                      : 30
% 0.13/0.40  # Removed in clause preprocessing      : 5
% 0.13/0.40  # Initial clauses in saturation        : 25
% 0.13/0.40  # Processed clauses                    : 372
% 0.13/0.40  # ...of these trivial                  : 62
% 0.13/0.40  # ...subsumed                          : 104
% 0.13/0.40  # ...remaining for further processing  : 206
% 0.13/0.40  # Other redundant clauses eliminated   : 2
% 0.13/0.40  # Clauses deleted for lack of memory   : 0
% 0.13/0.40  # Backward-subsumed                    : 4
% 0.13/0.40  # Backward-rewritten                   : 37
% 0.13/0.40  # Generated clauses                    : 1656
% 0.13/0.40  # ...of the previous two non-trivial   : 981
% 0.13/0.40  # Contextual simplify-reflections      : 0
% 0.13/0.40  # Paramodulations                      : 1652
% 0.13/0.40  # Factorizations                       : 2
% 0.13/0.40  # Equation resolutions                 : 2
% 0.13/0.40  # Propositional unsat checks           : 0
% 0.13/0.40  #    Propositional check models        : 0
% 0.13/0.40  #    Propositional check unsatisfiable : 0
% 0.13/0.40  #    Propositional clauses             : 0
% 0.13/0.40  #    Propositional clauses after purity: 0
% 0.13/0.40  #    Propositional unsat core size     : 0
% 0.13/0.40  #    Propositional preprocessing time  : 0.000
% 0.13/0.40  #    Propositional encoding time       : 0.000
% 0.13/0.40  #    Propositional solver time         : 0.000
% 0.13/0.40  #    Success case prop preproc time    : 0.000
% 0.13/0.40  #    Success case prop encoding time   : 0.000
% 0.13/0.40  #    Success case prop solver time     : 0.000
% 0.13/0.40  # Current number of processed clauses  : 138
% 0.13/0.40  #    Positive orientable unit clauses  : 75
% 0.13/0.40  #    Positive unorientable unit clauses: 5
% 0.13/0.40  #    Negative unit clauses             : 2
% 0.13/0.40  #    Non-unit-clauses                  : 56
% 0.13/0.40  # Current number of unprocessed clauses: 553
% 0.13/0.40  # ...number of literals in the above   : 788
% 0.13/0.40  # Current number of archived formulas  : 0
% 0.13/0.40  # Current number of archived clauses   : 71
% 0.13/0.40  # Clause-clause subsumption calls (NU) : 1235
% 0.13/0.40  # Rec. Clause-clause subsumption calls : 1027
% 0.13/0.40  # Non-unit clause-clause subsumptions  : 25
% 0.13/0.40  # Unit Clause-clause subsumption calls : 533
% 0.13/0.40  # Rewrite failures with RHS unbound    : 24
% 0.13/0.40  # BW rewrite match attempts            : 359
% 0.13/0.40  # BW rewrite match successes           : 122
% 0.13/0.40  # Condensation attempts                : 0
% 0.13/0.40  # Condensation successes               : 0
% 0.13/0.40  # Termbank termtop insertions          : 20694
% 0.13/0.40  
% 0.13/0.40  # -------------------------------------------------
% 0.13/0.40  # User time                : 0.048 s
% 0.13/0.40  # System time              : 0.008 s
% 0.13/0.40  # Total time               : 0.056 s
% 0.13/0.40  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
