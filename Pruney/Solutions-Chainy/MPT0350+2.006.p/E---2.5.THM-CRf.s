%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:45:14 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 248 expanded)
%              Number of clauses        :   51 ( 114 expanded)
%              Number of leaves         :   18 (  64 expanded)
%              Depth                    :   18
%              Number of atoms          :  166 ( 395 expanded)
%              Number of equality atoms :   74 ( 226 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t22_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k3_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

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

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(t46_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(t51_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

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

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(dt_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(c_0_18,plain,(
    ! [X27,X28] : k3_tarski(k2_tarski(X27,X28)) = k2_xboole_0(X27,X28) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_19,plain,(
    ! [X18,X19] : k1_enumset1(X18,X18,X19) = k2_tarski(X18,X19) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_20,plain,(
    ! [X10,X11] : k2_xboole_0(X10,k3_xboole_0(X10,X11)) = X10 ),
    inference(variable_rename,[status(thm)],[t22_xboole_1])).

cnf(c_0_21,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_22,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_23,plain,(
    ! [X8,X9] :
      ( ~ r1_tarski(X8,X9)
      | k2_xboole_0(X8,X9) = X9 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_24,plain,
    ( k2_xboole_0(X1,k3_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_25,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_26,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_27,plain,(
    ! [X20,X21,X22,X23,X24,X25] :
      ( ( ~ r2_hidden(X22,X21)
        | r1_tarski(X22,X20)
        | X21 != k1_zfmisc_1(X20) )
      & ( ~ r1_tarski(X23,X20)
        | r2_hidden(X23,X21)
        | X21 != k1_zfmisc_1(X20) )
      & ( ~ r2_hidden(esk1_2(X24,X25),X25)
        | ~ r1_tarski(esk1_2(X24,X25),X24)
        | X25 = k1_zfmisc_1(X24) )
      & ( r2_hidden(esk1_2(X24,X25),X25)
        | r1_tarski(esk1_2(X24,X25),X24)
        | X25 = k1_zfmisc_1(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

cnf(c_0_28,plain,
    ( k3_tarski(k1_enumset1(X1,X1,k3_xboole_0(X1,X2))) = X1 ),
    inference(rw,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_29,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_26,c_0_25])).

cnf(c_0_30,plain,
    ( r1_tarski(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_31,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,k3_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_32,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(er,[status(thm)],[c_0_30])).

fof(c_0_33,plain,(
    ! [X29,X30] :
      ( ( ~ m1_subset_1(X30,X29)
        | r2_hidden(X30,X29)
        | v1_xboole_0(X29) )
      & ( ~ r2_hidden(X30,X29)
        | m1_subset_1(X30,X29)
        | v1_xboole_0(X29) )
      & ( ~ m1_subset_1(X30,X29)
        | v1_xboole_0(X30)
        | ~ v1_xboole_0(X29) )
      & ( ~ v1_xboole_0(X30)
        | m1_subset_1(X30,X29)
        | ~ v1_xboole_0(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

fof(c_0_34,plain,(
    ! [X36] : ~ v1_xboole_0(k1_zfmisc_1(X36)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).

fof(c_0_35,plain,(
    ! [X4,X5] : k3_xboole_0(X4,X5) = k3_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_36,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r2_hidden(X1,k1_zfmisc_1(k3_xboole_0(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_37,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_38,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

fof(c_0_39,plain,(
    ! [X40] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X40)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

fof(c_0_40,plain,(
    ! [X12,X13] : k4_xboole_0(X12,k2_xboole_0(X12,X13)) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t46_xboole_1])).

fof(c_0_41,plain,(
    ! [X6,X7] : k4_xboole_0(X6,X7) = k5_xboole_0(X6,k3_xboole_0(X6,X7)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_42,plain,(
    ! [X16,X17] : k2_tarski(X16,X17) = k2_tarski(X17,X16) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

cnf(c_0_43,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_44,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(k3_xboole_0(X1,X2))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_38])).

cnf(c_0_45,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

fof(c_0_46,plain,(
    ! [X14,X15] : k2_xboole_0(k3_xboole_0(X14,X15),k4_xboole_0(X14,X15)) = X14 ),
    inference(variable_rename,[status(thm)],[t51_xboole_1])).

cnf(c_0_47,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_48,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_49,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_50,plain,
    ( k3_tarski(k1_enumset1(X1,X1,k3_xboole_0(X2,X1))) = X1 ),
    inference(spm,[status(thm)],[c_0_28,c_0_43])).

cnf(c_0_51,plain,
    ( k3_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

fof(c_0_52,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X1))
       => k4_subset_1(X1,X2,k3_subset_1(X1,X2)) = k2_subset_1(X1) ) ),
    inference(assume_negation,[status(cth)],[t25_subset_1])).

fof(c_0_53,plain,(
    ! [X37,X38,X39] :
      ( ~ m1_subset_1(X38,k1_zfmisc_1(X37))
      | ~ m1_subset_1(X39,k1_zfmisc_1(X37))
      | k4_subset_1(X37,X38,X39) = k2_xboole_0(X38,X39) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).

cnf(c_0_54,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_55,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k3_tarski(k1_enumset1(X1,X1,X2)))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_25]),c_0_48])).

cnf(c_0_56,plain,
    ( k1_enumset1(X1,X1,X2) = k1_enumset1(X2,X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_22]),c_0_22])).

cnf(c_0_57,plain,
    ( k3_tarski(k1_enumset1(X1,X1,k1_xboole_0)) = X1 ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

fof(c_0_58,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))
    & k4_subset_1(esk2_0,esk3_0,k3_subset_1(esk2_0,esk3_0)) != k2_subset_1(esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_52])])])).

fof(c_0_59,plain,(
    ! [X31] : k2_subset_1(X31) = X31 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

cnf(c_0_60,plain,
    ( k4_subset_1(X2,X1,X3) = k2_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_61,plain,
    ( k3_tarski(k1_enumset1(k3_xboole_0(X1,X2),k3_xboole_0(X1,X2),k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54,c_0_25]),c_0_48])).

cnf(c_0_62,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k3_tarski(k1_enumset1(X2,X2,X1)))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_63,plain,
    ( k3_tarski(k1_enumset1(k1_xboole_0,k1_xboole_0,X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_57,c_0_56])).

cnf(c_0_64,negated_conjecture,
    ( k4_subset_1(esk2_0,esk3_0,k3_subset_1(esk2_0,esk3_0)) != k2_subset_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_65,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_66,plain,
    ( k4_subset_1(X2,X1,X3) = k3_tarski(k1_enumset1(X1,X1,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_60,c_0_25])).

fof(c_0_67,plain,(
    ! [X32,X33] :
      ( ~ m1_subset_1(X33,k1_zfmisc_1(X32))
      | k3_subset_1(X32,X33) = k4_xboole_0(X32,X33) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

cnf(c_0_68,plain,
    ( k3_xboole_0(X1,k3_tarski(k1_enumset1(X2,X2,X1))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_56]),c_0_63])).

cnf(c_0_69,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = X1
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_56])).

cnf(c_0_70,negated_conjecture,
    ( k4_subset_1(esk2_0,esk3_0,k3_subset_1(esk2_0,esk3_0)) != esk2_0 ),
    inference(rw,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_71,plain,
    ( k4_subset_1(X1,X2,X3) = k4_subset_1(X4,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X4))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X4)) ),
    inference(spm,[status(thm)],[c_0_66,c_0_66])).

cnf(c_0_72,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_73,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_74,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_75,negated_conjecture,
    ( k4_subset_1(X1,esk3_0,k3_subset_1(esk2_0,esk3_0)) != esk2_0
    | ~ m1_subset_1(k3_subset_1(esk2_0,esk3_0),k1_zfmisc_1(esk2_0))
    | ~ m1_subset_1(k3_subset_1(esk2_0,esk3_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_72])])).

cnf(c_0_76,plain,
    ( k3_subset_1(X2,X1) = k5_xboole_0(X2,k3_xboole_0(X2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_73,c_0_48])).

cnf(c_0_77,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_74,c_0_32])).

cnf(c_0_78,negated_conjecture,
    ( k3_tarski(k1_enumset1(esk3_0,esk3_0,k3_subset_1(esk2_0,esk3_0))) != esk2_0
    | ~ m1_subset_1(k3_subset_1(esk2_0,esk3_0),k1_zfmisc_1(esk2_0))
    | ~ m1_subset_1(k3_subset_1(esk2_0,esk3_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_75,c_0_66])).

cnf(c_0_79,plain,
    ( k3_tarski(k1_enumset1(k3_xboole_0(X1,X2),k3_xboole_0(X1,X2),k3_subset_1(X1,X2))) = X1
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_61,c_0_76])).

cnf(c_0_80,plain,
    ( k3_xboole_0(X1,X2) = X2
    | ~ r2_hidden(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_77])).

cnf(c_0_81,negated_conjecture,
    ( k3_tarski(k1_enumset1(esk3_0,esk3_0,k3_subset_1(esk2_0,esk3_0))) != esk2_0
    | ~ m1_subset_1(k3_subset_1(esk2_0,esk3_0),k1_zfmisc_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_78,c_0_72])).

cnf(c_0_82,plain,
    ( k3_tarski(k1_enumset1(X1,X1,k3_subset_1(X2,X1))) = X2
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_79,c_0_80])).

fof(c_0_83,plain,(
    ! [X34,X35] :
      ( ~ m1_subset_1(X35,k1_zfmisc_1(X34))
      | m1_subset_1(k3_subset_1(X34,X35),k1_zfmisc_1(X34)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).

cnf(c_0_84,negated_conjecture,
    ( ~ m1_subset_1(k3_subset_1(esk2_0,esk3_0),k1_zfmisc_1(esk2_0))
    | ~ r2_hidden(esk3_0,k1_zfmisc_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_82]),c_0_72])])).

cnf(c_0_85,plain,
    ( m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_83])).

cnf(c_0_86,negated_conjecture,
    ( ~ r2_hidden(esk3_0,k1_zfmisc_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_85]),c_0_72])])).

cnf(c_0_87,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_37]),c_0_72])]),c_0_38]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:16:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.48  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S05BN
% 0.20/0.48  # and selection function SelectUnlessUniqMaxSmallestOrientable.
% 0.20/0.48  #
% 0.20/0.48  # Preprocessing time       : 0.027 s
% 0.20/0.48  # Presaturation interreduction done
% 0.20/0.48  
% 0.20/0.48  # Proof found!
% 0.20/0.48  # SZS status Theorem
% 0.20/0.48  # SZS output start CNFRefutation
% 0.20/0.48  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.20/0.48  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.20/0.48  fof(t22_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k3_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_xboole_1)).
% 0.20/0.48  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.20/0.48  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 0.20/0.48  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 0.20/0.48  fof(fc1_subset_1, axiom, ![X1]:~(v1_xboole_0(k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 0.20/0.48  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.20/0.48  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 0.20/0.48  fof(t46_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 0.20/0.48  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.20/0.48  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 0.20/0.48  fof(t51_xboole_1, axiom, ![X1, X2]:k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 0.20/0.48  fof(t25_subset_1, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k4_subset_1(X1,X2,k3_subset_1(X1,X2))=k2_subset_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_subset_1)).
% 0.20/0.48  fof(redefinition_k4_subset_1, axiom, ![X1, X2, X3]:((m1_subset_1(X2,k1_zfmisc_1(X1))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>k4_subset_1(X1,X2,X3)=k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 0.20/0.48  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 0.20/0.48  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 0.20/0.48  fof(dt_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 0.20/0.48  fof(c_0_18, plain, ![X27, X28]:k3_tarski(k2_tarski(X27,X28))=k2_xboole_0(X27,X28), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.20/0.48  fof(c_0_19, plain, ![X18, X19]:k1_enumset1(X18,X18,X19)=k2_tarski(X18,X19), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.20/0.48  fof(c_0_20, plain, ![X10, X11]:k2_xboole_0(X10,k3_xboole_0(X10,X11))=X10, inference(variable_rename,[status(thm)],[t22_xboole_1])).
% 0.20/0.48  cnf(c_0_21, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.48  cnf(c_0_22, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.48  fof(c_0_23, plain, ![X8, X9]:(~r1_tarski(X8,X9)|k2_xboole_0(X8,X9)=X9), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.20/0.48  cnf(c_0_24, plain, (k2_xboole_0(X1,k3_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.48  cnf(c_0_25, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_21, c_0_22])).
% 0.20/0.48  cnf(c_0_26, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.48  fof(c_0_27, plain, ![X20, X21, X22, X23, X24, X25]:(((~r2_hidden(X22,X21)|r1_tarski(X22,X20)|X21!=k1_zfmisc_1(X20))&(~r1_tarski(X23,X20)|r2_hidden(X23,X21)|X21!=k1_zfmisc_1(X20)))&((~r2_hidden(esk1_2(X24,X25),X25)|~r1_tarski(esk1_2(X24,X25),X24)|X25=k1_zfmisc_1(X24))&(r2_hidden(esk1_2(X24,X25),X25)|r1_tarski(esk1_2(X24,X25),X24)|X25=k1_zfmisc_1(X24)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 0.20/0.48  cnf(c_0_28, plain, (k3_tarski(k1_enumset1(X1,X1,k3_xboole_0(X1,X2)))=X1), inference(rw,[status(thm)],[c_0_24, c_0_25])).
% 0.20/0.48  cnf(c_0_29, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=X2|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_26, c_0_25])).
% 0.20/0.48  cnf(c_0_30, plain, (r1_tarski(X1,X3)|~r2_hidden(X1,X2)|X2!=k1_zfmisc_1(X3)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.48  cnf(c_0_31, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,k3_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.20/0.48  cnf(c_0_32, plain, (r1_tarski(X1,X2)|~r2_hidden(X1,k1_zfmisc_1(X2))), inference(er,[status(thm)],[c_0_30])).
% 0.20/0.48  fof(c_0_33, plain, ![X29, X30]:(((~m1_subset_1(X30,X29)|r2_hidden(X30,X29)|v1_xboole_0(X29))&(~r2_hidden(X30,X29)|m1_subset_1(X30,X29)|v1_xboole_0(X29)))&((~m1_subset_1(X30,X29)|v1_xboole_0(X30)|~v1_xboole_0(X29))&(~v1_xboole_0(X30)|m1_subset_1(X30,X29)|~v1_xboole_0(X29)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 0.20/0.48  fof(c_0_34, plain, ![X36]:~v1_xboole_0(k1_zfmisc_1(X36)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).
% 0.20/0.48  fof(c_0_35, plain, ![X4, X5]:k3_xboole_0(X4,X5)=k3_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.20/0.48  cnf(c_0_36, plain, (k3_xboole_0(X1,X2)=X1|~r2_hidden(X1,k1_zfmisc_1(k3_xboole_0(X1,X2)))), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.20/0.48  cnf(c_0_37, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.20/0.48  cnf(c_0_38, plain, (~v1_xboole_0(k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.20/0.48  fof(c_0_39, plain, ![X40]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X40)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.20/0.48  fof(c_0_40, plain, ![X12, X13]:k4_xboole_0(X12,k2_xboole_0(X12,X13))=k1_xboole_0, inference(variable_rename,[status(thm)],[t46_xboole_1])).
% 0.20/0.48  fof(c_0_41, plain, ![X6, X7]:k4_xboole_0(X6,X7)=k5_xboole_0(X6,k3_xboole_0(X6,X7)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.20/0.48  fof(c_0_42, plain, ![X16, X17]:k2_tarski(X16,X17)=k2_tarski(X17,X16), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 0.20/0.48  cnf(c_0_43, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.20/0.48  cnf(c_0_44, plain, (k3_xboole_0(X1,X2)=X1|~m1_subset_1(X1,k1_zfmisc_1(k3_xboole_0(X1,X2)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_38])).
% 0.20/0.48  cnf(c_0_45, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.20/0.48  fof(c_0_46, plain, ![X14, X15]:k2_xboole_0(k3_xboole_0(X14,X15),k4_xboole_0(X14,X15))=X14, inference(variable_rename,[status(thm)],[t51_xboole_1])).
% 0.20/0.48  cnf(c_0_47, plain, (k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.20/0.48  cnf(c_0_48, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.20/0.48  cnf(c_0_49, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.20/0.48  cnf(c_0_50, plain, (k3_tarski(k1_enumset1(X1,X1,k3_xboole_0(X2,X1)))=X1), inference(spm,[status(thm)],[c_0_28, c_0_43])).
% 0.20/0.48  cnf(c_0_51, plain, (k3_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.20/0.48  fof(c_0_52, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k4_subset_1(X1,X2,k3_subset_1(X1,X2))=k2_subset_1(X1))), inference(assume_negation,[status(cth)],[t25_subset_1])).
% 0.20/0.48  fof(c_0_53, plain, ![X37, X38, X39]:(~m1_subset_1(X38,k1_zfmisc_1(X37))|~m1_subset_1(X39,k1_zfmisc_1(X37))|k4_subset_1(X37,X38,X39)=k2_xboole_0(X38,X39)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).
% 0.20/0.48  cnf(c_0_54, plain, (k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.20/0.48  cnf(c_0_55, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k3_tarski(k1_enumset1(X1,X1,X2))))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47, c_0_25]), c_0_48])).
% 0.20/0.48  cnf(c_0_56, plain, (k1_enumset1(X1,X1,X2)=k1_enumset1(X2,X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49, c_0_22]), c_0_22])).
% 0.20/0.48  cnf(c_0_57, plain, (k3_tarski(k1_enumset1(X1,X1,k1_xboole_0))=X1), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.20/0.48  fof(c_0_58, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))&k4_subset_1(esk2_0,esk3_0,k3_subset_1(esk2_0,esk3_0))!=k2_subset_1(esk2_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_52])])])).
% 0.20/0.48  fof(c_0_59, plain, ![X31]:k2_subset_1(X31)=X31, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 0.20/0.48  cnf(c_0_60, plain, (k4_subset_1(X2,X1,X3)=k2_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.20/0.48  cnf(c_0_61, plain, (k3_tarski(k1_enumset1(k3_xboole_0(X1,X2),k3_xboole_0(X1,X2),k5_xboole_0(X1,k3_xboole_0(X1,X2))))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54, c_0_25]), c_0_48])).
% 0.20/0.48  cnf(c_0_62, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k3_tarski(k1_enumset1(X2,X2,X1))))=k1_xboole_0), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.20/0.48  cnf(c_0_63, plain, (k3_tarski(k1_enumset1(k1_xboole_0,k1_xboole_0,X1))=X1), inference(spm,[status(thm)],[c_0_57, c_0_56])).
% 0.20/0.48  cnf(c_0_64, negated_conjecture, (k4_subset_1(esk2_0,esk3_0,k3_subset_1(esk2_0,esk3_0))!=k2_subset_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.20/0.48  cnf(c_0_65, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.20/0.48  cnf(c_0_66, plain, (k4_subset_1(X2,X1,X3)=k3_tarski(k1_enumset1(X1,X1,X3))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_60, c_0_25])).
% 0.20/0.48  fof(c_0_67, plain, ![X32, X33]:(~m1_subset_1(X33,k1_zfmisc_1(X32))|k3_subset_1(X32,X33)=k4_xboole_0(X32,X33)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 0.20/0.48  cnf(c_0_68, plain, (k3_xboole_0(X1,k3_tarski(k1_enumset1(X2,X2,X1)))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_56]), c_0_63])).
% 0.20/0.48  cnf(c_0_69, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=X1|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_29, c_0_56])).
% 0.20/0.48  cnf(c_0_70, negated_conjecture, (k4_subset_1(esk2_0,esk3_0,k3_subset_1(esk2_0,esk3_0))!=esk2_0), inference(rw,[status(thm)],[c_0_64, c_0_65])).
% 0.20/0.48  cnf(c_0_71, plain, (k4_subset_1(X1,X2,X3)=k4_subset_1(X4,X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~m1_subset_1(X3,k1_zfmisc_1(X4))|~m1_subset_1(X2,k1_zfmisc_1(X4))), inference(spm,[status(thm)],[c_0_66, c_0_66])).
% 0.20/0.48  cnf(c_0_72, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.20/0.48  cnf(c_0_73, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.20/0.48  cnf(c_0_74, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 0.20/0.48  cnf(c_0_75, negated_conjecture, (k4_subset_1(X1,esk3_0,k3_subset_1(esk2_0,esk3_0))!=esk2_0|~m1_subset_1(k3_subset_1(esk2_0,esk3_0),k1_zfmisc_1(esk2_0))|~m1_subset_1(k3_subset_1(esk2_0,esk3_0),k1_zfmisc_1(X1))|~m1_subset_1(esk3_0,k1_zfmisc_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_71]), c_0_72])])).
% 0.20/0.48  cnf(c_0_76, plain, (k3_subset_1(X2,X1)=k5_xboole_0(X2,k3_xboole_0(X2,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_73, c_0_48])).
% 0.20/0.48  cnf(c_0_77, plain, (k3_xboole_0(X1,X2)=X1|~r2_hidden(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_74, c_0_32])).
% 0.20/0.48  cnf(c_0_78, negated_conjecture, (k3_tarski(k1_enumset1(esk3_0,esk3_0,k3_subset_1(esk2_0,esk3_0)))!=esk2_0|~m1_subset_1(k3_subset_1(esk2_0,esk3_0),k1_zfmisc_1(esk2_0))|~m1_subset_1(k3_subset_1(esk2_0,esk3_0),k1_zfmisc_1(X1))|~m1_subset_1(esk3_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_75, c_0_66])).
% 0.20/0.48  cnf(c_0_79, plain, (k3_tarski(k1_enumset1(k3_xboole_0(X1,X2),k3_xboole_0(X1,X2),k3_subset_1(X1,X2)))=X1|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_61, c_0_76])).
% 0.20/0.48  cnf(c_0_80, plain, (k3_xboole_0(X1,X2)=X2|~r2_hidden(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_43, c_0_77])).
% 0.20/0.48  cnf(c_0_81, negated_conjecture, (k3_tarski(k1_enumset1(esk3_0,esk3_0,k3_subset_1(esk2_0,esk3_0)))!=esk2_0|~m1_subset_1(k3_subset_1(esk2_0,esk3_0),k1_zfmisc_1(esk2_0))), inference(spm,[status(thm)],[c_0_78, c_0_72])).
% 0.20/0.48  cnf(c_0_82, plain, (k3_tarski(k1_enumset1(X1,X1,k3_subset_1(X2,X1)))=X2|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_79, c_0_80])).
% 0.20/0.48  fof(c_0_83, plain, ![X34, X35]:(~m1_subset_1(X35,k1_zfmisc_1(X34))|m1_subset_1(k3_subset_1(X34,X35),k1_zfmisc_1(X34))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).
% 0.20/0.48  cnf(c_0_84, negated_conjecture, (~m1_subset_1(k3_subset_1(esk2_0,esk3_0),k1_zfmisc_1(esk2_0))|~r2_hidden(esk3_0,k1_zfmisc_1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_82]), c_0_72])])).
% 0.20/0.48  cnf(c_0_85, plain, (m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_83])).
% 0.20/0.48  cnf(c_0_86, negated_conjecture, (~r2_hidden(esk3_0,k1_zfmisc_1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_85]), c_0_72])])).
% 0.20/0.48  cnf(c_0_87, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_37]), c_0_72])]), c_0_38]), ['proof']).
% 0.20/0.48  # SZS output end CNFRefutation
% 0.20/0.48  # Proof object total steps             : 88
% 0.20/0.48  # Proof object clause steps            : 51
% 0.20/0.48  # Proof object formula steps           : 37
% 0.20/0.48  # Proof object conjectures             : 12
% 0.20/0.48  # Proof object clause conjectures      : 9
% 0.20/0.48  # Proof object formula conjectures     : 3
% 0.20/0.48  # Proof object initial clauses used    : 19
% 0.20/0.48  # Proof object initial formulas used   : 18
% 0.20/0.48  # Proof object generating inferences   : 22
% 0.20/0.48  # Proof object simplifying inferences  : 25
% 0.20/0.48  # Training examples: 0 positive, 0 negative
% 0.20/0.48  # Parsed axioms                        : 18
% 0.20/0.48  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.48  # Initial clauses                      : 25
% 0.20/0.48  # Removed in clause preprocessing      : 4
% 0.20/0.48  # Initial clauses in saturation        : 21
% 0.20/0.48  # Processed clauses                    : 2011
% 0.20/0.48  # ...of these trivial                  : 33
% 0.20/0.48  # ...subsumed                          : 1603
% 0.20/0.48  # ...remaining for further processing  : 375
% 0.20/0.48  # Other redundant clauses eliminated   : 2
% 0.20/0.48  # Clauses deleted for lack of memory   : 0
% 0.20/0.48  # Backward-subsumed                    : 10
% 0.20/0.48  # Backward-rewritten                   : 8
% 0.20/0.48  # Generated clauses                    : 5450
% 0.20/0.48  # ...of the previous two non-trivial   : 4517
% 0.20/0.48  # Contextual simplify-reflections      : 2
% 0.20/0.48  # Paramodulations                      : 5446
% 0.20/0.48  # Factorizations                       : 2
% 0.20/0.48  # Equation resolutions                 : 2
% 0.20/0.48  # Propositional unsat checks           : 0
% 0.20/0.48  #    Propositional check models        : 0
% 0.20/0.48  #    Propositional check unsatisfiable : 0
% 0.20/0.48  #    Propositional clauses             : 0
% 0.20/0.48  #    Propositional clauses after purity: 0
% 0.20/0.48  #    Propositional unsat core size     : 0
% 0.20/0.48  #    Propositional preprocessing time  : 0.000
% 0.20/0.48  #    Propositional encoding time       : 0.000
% 0.20/0.48  #    Propositional solver time         : 0.000
% 0.20/0.48  #    Success case prop preproc time    : 0.000
% 0.20/0.48  #    Success case prop encoding time   : 0.000
% 0.20/0.48  #    Success case prop solver time     : 0.000
% 0.20/0.48  # Current number of processed clauses  : 334
% 0.20/0.48  #    Positive orientable unit clauses  : 30
% 0.20/0.48  #    Positive unorientable unit clauses: 2
% 0.20/0.48  #    Negative unit clauses             : 4
% 0.20/0.48  #    Non-unit-clauses                  : 298
% 0.20/0.48  # Current number of unprocessed clauses: 2529
% 0.20/0.48  # ...number of literals in the above   : 10112
% 0.20/0.48  # Current number of archived formulas  : 0
% 0.20/0.48  # Current number of archived clauses   : 43
% 0.20/0.48  # Clause-clause subsumption calls (NU) : 40917
% 0.20/0.48  # Rec. Clause-clause subsumption calls : 24929
% 0.20/0.48  # Non-unit clause-clause subsumptions  : 1592
% 0.20/0.48  # Unit Clause-clause subsumption calls : 258
% 0.20/0.48  # Rewrite failures with RHS unbound    : 0
% 0.20/0.48  # BW rewrite match attempts            : 177
% 0.20/0.48  # BW rewrite match successes           : 18
% 0.20/0.48  # Condensation attempts                : 0
% 0.20/0.48  # Condensation successes               : 0
% 0.20/0.48  # Termbank termtop insertions          : 75003
% 0.20/0.48  
% 0.20/0.48  # -------------------------------------------------
% 0.20/0.48  # User time                : 0.135 s
% 0.20/0.48  # System time              : 0.007 s
% 0.20/0.48  # Total time               : 0.142 s
% 0.20/0.48  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
