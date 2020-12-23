%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:46:11 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 267 expanded)
%              Number of clauses        :   52 ( 120 expanded)
%              Number of leaves         :   19 (  69 expanded)
%              Depth                    :   15
%              Number of atoms          :  193 ( 518 expanded)
%              Number of equality atoms :   72 ( 224 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t95_xboole_1,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

fof(t40_subset_1,conjecture,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => ( ( r1_tarski(X2,X3)
          & r1_tarski(X2,k3_subset_1(X1,X3)) )
       => X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_subset_1)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(commutativity_k5_xboole_0,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(t91_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

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

fof(t92_xboole_1,axiom,(
    ! [X1] : k5_xboole_0(X1,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(t5_boole,axiom,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(t14_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X3,X2)
        & ! [X4] :
            ( ( r1_tarski(X1,X4)
              & r1_tarski(X3,X4) )
           => r1_tarski(X2,X4) ) )
     => X2 = k2_xboole_0(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_xboole_1)).

fof(l49_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => r1_tarski(X1,k3_tarski(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).

fof(t99_zfmisc_1,axiom,(
    ! [X1] : k3_tarski(k1_zfmisc_1(X1)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t107_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k5_xboole_0(X2,X3))
    <=> ( r1_tarski(X1,k2_xboole_0(X2,X3))
        & r1_xboole_0(X1,k3_xboole_0(X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_xboole_1)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(c_0_19,plain,(
    ! [X33,X34] : k3_tarski(k2_tarski(X33,X34)) = k2_xboole_0(X33,X34) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_20,plain,(
    ! [X29,X30] : k1_enumset1(X29,X29,X30) = k2_tarski(X29,X30) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_21,plain,(
    ! [X27,X28] : k3_xboole_0(X27,X28) = k5_xboole_0(k5_xboole_0(X27,X28),k2_xboole_0(X27,X28)) ),
    inference(variable_rename,[status(thm)],[t95_xboole_1])).

cnf(c_0_22,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_23,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_24,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(X1))
       => ( ( r1_tarski(X2,X3)
            & r1_tarski(X2,k3_subset_1(X1,X3)) )
         => X2 = k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t40_subset_1])).

fof(c_0_25,plain,(
    ! [X38,X39] :
      ( ~ m1_subset_1(X39,k1_zfmisc_1(X38))
      | k3_subset_1(X38,X39) = k4_xboole_0(X38,X39) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

fof(c_0_26,plain,(
    ! [X11,X12] : k4_xboole_0(X11,X12) = k5_xboole_0(X11,k3_xboole_0(X11,X12)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_27,plain,
    ( k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_22,c_0_23])).

fof(c_0_29,plain,(
    ! [X5,X6] : k5_xboole_0(X5,X6) = k5_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).

fof(c_0_30,plain,(
    ! [X23,X24,X25] : k5_xboole_0(k5_xboole_0(X23,X24),X25) = k5_xboole_0(X23,k5_xboole_0(X24,X25)) ),
    inference(variable_rename,[status(thm)],[t91_xboole_1])).

fof(c_0_31,plain,(
    ! [X36,X37] :
      ( ( ~ m1_subset_1(X37,X36)
        | r2_hidden(X37,X36)
        | v1_xboole_0(X36) )
      & ( ~ r2_hidden(X37,X36)
        | m1_subset_1(X37,X36)
        | v1_xboole_0(X36) )
      & ( ~ m1_subset_1(X37,X36)
        | v1_xboole_0(X37)
        | ~ v1_xboole_0(X36) )
      & ( ~ v1_xboole_0(X37)
        | m1_subset_1(X37,X36)
        | ~ v1_xboole_0(X36) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

fof(c_0_32,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0))
    & r1_tarski(esk3_0,esk4_0)
    & r1_tarski(esk3_0,k3_subset_1(esk2_0,esk4_0))
    & esk3_0 != k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_24])])])).

fof(c_0_33,plain,(
    ! [X40] : ~ v1_xboole_0(k1_zfmisc_1(X40)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).

cnf(c_0_34,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_35,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_36,plain,
    ( k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k1_enumset1(X1,X1,X2))) ),
    inference(rw,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_37,plain,
    ( k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_38,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_39,plain,(
    ! [X26] : k5_xboole_0(X26,X26) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t92_xboole_1])).

fof(c_0_40,plain,(
    ! [X22] : k5_xboole_0(X22,k1_xboole_0) = X22 ),
    inference(variable_rename,[status(thm)],[t5_boole])).

fof(c_0_41,plain,(
    ! [X18,X19,X20] :
      ( ( r1_tarski(X18,esk1_3(X18,X19,X20))
        | ~ r1_tarski(X18,X19)
        | ~ r1_tarski(X20,X19)
        | X19 = k2_xboole_0(X18,X20) )
      & ( r1_tarski(X20,esk1_3(X18,X19,X20))
        | ~ r1_tarski(X18,X19)
        | ~ r1_tarski(X20,X19)
        | X19 = k2_xboole_0(X18,X20) )
      & ( ~ r1_tarski(X19,esk1_3(X18,X19,X20))
        | ~ r1_tarski(X18,X19)
        | ~ r1_tarski(X20,X19)
        | X19 = k2_xboole_0(X18,X20) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t14_xboole_1])])])])).

fof(c_0_42,plain,(
    ! [X31,X32] :
      ( ~ r2_hidden(X31,X32)
      | r1_tarski(X31,k3_tarski(X32)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l49_zfmisc_1])])).

cnf(c_0_43,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_44,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_45,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

fof(c_0_46,plain,(
    ! [X35] : k3_tarski(k1_zfmisc_1(X35)) = X35 ),
    inference(variable_rename,[status(thm)],[t99_zfmisc_1])).

cnf(c_0_47,plain,
    ( k3_subset_1(X2,X1) = k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X2,X1),k3_tarski(k1_enumset1(X2,X2,X1))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_35]),c_0_36])).

cnf(c_0_48,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,X3)) = k5_xboole_0(X3,k5_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_49,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_50,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_51,plain,
    ( r1_tarski(X1,esk1_3(X1,X2,X3))
    | X2 = k2_xboole_0(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_52,plain,
    ( r1_tarski(X1,k3_tarski(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_53,negated_conjecture,
    ( r2_hidden(esk4_0,k1_zfmisc_1(esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45])).

cnf(c_0_54,plain,
    ( k3_tarski(k1_zfmisc_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

fof(c_0_55,plain,(
    ! [X9,X10] :
      ( ( r1_tarski(X9,X10)
        | X9 != X10 )
      & ( r1_tarski(X10,X9)
        | X9 != X10 )
      & ( ~ r1_tarski(X9,X10)
        | ~ r1_tarski(X10,X9)
        | X9 = X10 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_56,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_tarski(k1_enumset1(X1,X1,X2))))) = k3_subset_1(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_47,c_0_38])).

cnf(c_0_57,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,X2)) = X2 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_50])).

cnf(c_0_58,plain,
    ( X2 = k3_tarski(k1_enumset1(X1,X1,X3))
    | r1_tarski(X1,esk1_3(X1,X2,X3))
    | ~ r1_tarski(X3,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_51,c_0_28])).

cnf(c_0_59,negated_conjecture,
    ( r1_tarski(esk4_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_54])).

cnf(c_0_60,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_61,plain,
    ( k5_xboole_0(X1,k3_tarski(k1_enumset1(X2,X2,X1))) = k3_subset_1(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_62,negated_conjecture,
    ( esk2_0 = k3_tarski(k1_enumset1(X1,X1,esk4_0))
    | r1_tarski(X1,esk1_3(X1,esk2_0,esk4_0))
    | ~ r1_tarski(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_63,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_60])).

cnf(c_0_64,negated_conjecture,
    ( k5_xboole_0(esk4_0,k3_tarski(k1_enumset1(esk2_0,esk2_0,esk4_0))) = k3_subset_1(esk2_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_61,c_0_44])).

cnf(c_0_65,negated_conjecture,
    ( k3_tarski(k1_enumset1(esk2_0,esk2_0,esk4_0)) = esk2_0
    | r1_tarski(esk2_0,esk1_3(esk2_0,esk2_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_66,plain,
    ( X1 = k2_xboole_0(X2,X3)
    | ~ r1_tarski(X1,esk1_3(X2,X1,X3))
    | ~ r1_tarski(X2,X1)
    | ~ r1_tarski(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_67,negated_conjecture,
    ( r1_tarski(esk3_0,k3_subset_1(esk2_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_68,negated_conjecture,
    ( k3_subset_1(esk2_0,esk4_0) = k5_xboole_0(esk4_0,esk2_0)
    | r1_tarski(esk2_0,esk1_3(esk2_0,esk2_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

fof(c_0_69,plain,(
    ! [X13,X14,X15] :
      ( ( r1_tarski(X13,k2_xboole_0(X14,X15))
        | ~ r1_tarski(X13,k5_xboole_0(X14,X15)) )
      & ( r1_xboole_0(X13,k3_xboole_0(X14,X15))
        | ~ r1_tarski(X13,k5_xboole_0(X14,X15)) )
      & ( ~ r1_tarski(X13,k2_xboole_0(X14,X15))
        | ~ r1_xboole_0(X13,k3_xboole_0(X14,X15))
        | r1_tarski(X13,k5_xboole_0(X14,X15)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t107_xboole_1])])])).

cnf(c_0_70,plain,
    ( X1 = k3_tarski(k1_enumset1(X2,X2,X3))
    | ~ r1_tarski(X3,X1)
    | ~ r1_tarski(X2,X1)
    | ~ r1_tarski(X1,esk1_3(X2,X1,X3)) ),
    inference(rw,[status(thm)],[c_0_66,c_0_28])).

cnf(c_0_71,negated_conjecture,
    ( r1_tarski(esk2_0,esk1_3(esk2_0,esk2_0,esk4_0))
    | r1_tarski(esk3_0,k5_xboole_0(esk4_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

fof(c_0_72,plain,(
    ! [X16,X17] :
      ( ~ r1_tarski(X16,X17)
      | k2_xboole_0(X16,X17) = X17 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

fof(c_0_73,plain,(
    ! [X7,X8] :
      ( ( ~ r1_xboole_0(X7,X8)
        | k3_xboole_0(X7,X8) = k1_xboole_0 )
      & ( k3_xboole_0(X7,X8) != k1_xboole_0
        | r1_xboole_0(X7,X8) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

cnf(c_0_74,plain,
    ( r1_xboole_0(X1,k3_xboole_0(X2,X3))
    | ~ r1_tarski(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_75,negated_conjecture,
    ( k3_tarski(k1_enumset1(esk2_0,esk2_0,esk4_0)) = esk2_0
    | r1_tarski(esk3_0,k5_xboole_0(esk4_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_59]),c_0_63])])).

cnf(c_0_76,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_77,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_78,plain,
    ( r1_xboole_0(X1,k5_xboole_0(k5_xboole_0(X2,X3),k3_tarski(k1_enumset1(X2,X2,X3))))
    | ~ r1_tarski(X1,k5_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[c_0_74,c_0_36])).

cnf(c_0_79,negated_conjecture,
    ( k3_subset_1(esk2_0,esk4_0) = k5_xboole_0(esk4_0,esk2_0)
    | r1_tarski(esk3_0,k5_xboole_0(esk4_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_64,c_0_75])).

cnf(c_0_80,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_76,c_0_28])).

cnf(c_0_81,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k1_enumset1(X1,X1,X2))) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_77,c_0_36])).

cnf(c_0_82,plain,
    ( r1_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k3_tarski(k1_enumset1(X2,X2,X3)))))
    | ~ r1_tarski(X1,k5_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[c_0_78,c_0_38])).

cnf(c_0_83,negated_conjecture,
    ( r1_tarski(esk3_0,k5_xboole_0(esk4_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_67,c_0_79])).

cnf(c_0_84,negated_conjecture,
    ( k3_tarski(k1_enumset1(esk4_0,esk4_0,esk2_0)) = esk2_0 ),
    inference(spm,[status(thm)],[c_0_80,c_0_59])).

cnf(c_0_85,negated_conjecture,
    ( r1_tarski(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_86,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k3_tarski(k1_enumset1(X1,X1,X2)))) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_81,c_0_38])).

cnf(c_0_87,negated_conjecture,
    ( r1_xboole_0(esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_84]),c_0_49]),c_0_50])).

cnf(c_0_88,negated_conjecture,
    ( k3_tarski(k1_enumset1(esk3_0,esk3_0,esk4_0)) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_80,c_0_85])).

cnf(c_0_89,negated_conjecture,
    ( esk3_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_90,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_87]),c_0_88]),c_0_49]),c_0_50]),c_0_89]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:59:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.45  # AutoSched0-Mode selected heuristic G_E___107_B00_00_F1_PI_AE_Q4_CS_SP_PS_S002A
% 0.19/0.45  # and selection function SelectNegativeLiterals.
% 0.19/0.45  #
% 0.19/0.45  # Preprocessing time       : 0.028 s
% 0.19/0.45  # Presaturation interreduction done
% 0.19/0.45  
% 0.19/0.45  # Proof found!
% 0.19/0.45  # SZS status Theorem
% 0.19/0.45  # SZS output start CNFRefutation
% 0.19/0.45  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.19/0.45  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.19/0.45  fof(t95_xboole_1, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_xboole_1)).
% 0.19/0.45  fof(t40_subset_1, conjecture, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>((r1_tarski(X2,X3)&r1_tarski(X2,k3_subset_1(X1,X3)))=>X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_subset_1)).
% 0.19/0.45  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 0.19/0.45  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.19/0.45  fof(commutativity_k5_xboole_0, axiom, ![X1, X2]:k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 0.19/0.45  fof(t91_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 0.19/0.45  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 0.19/0.45  fof(fc1_subset_1, axiom, ![X1]:~(v1_xboole_0(k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 0.19/0.45  fof(t92_xboole_1, axiom, ![X1]:k5_xboole_0(X1,X1)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 0.19/0.45  fof(t5_boole, axiom, ![X1]:k5_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 0.19/0.45  fof(t14_xboole_1, axiom, ![X1, X2, X3]:(((r1_tarski(X1,X2)&r1_tarski(X3,X2))&![X4]:((r1_tarski(X1,X4)&r1_tarski(X3,X4))=>r1_tarski(X2,X4)))=>X2=k2_xboole_0(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_xboole_1)).
% 0.19/0.45  fof(l49_zfmisc_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>r1_tarski(X1,k3_tarski(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 0.19/0.45  fof(t99_zfmisc_1, axiom, ![X1]:k3_tarski(k1_zfmisc_1(X1))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 0.19/0.45  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.19/0.45  fof(t107_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k5_xboole_0(X2,X3))<=>(r1_tarski(X1,k2_xboole_0(X2,X3))&r1_xboole_0(X1,k3_xboole_0(X2,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t107_xboole_1)).
% 0.19/0.45  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.19/0.45  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 0.19/0.45  fof(c_0_19, plain, ![X33, X34]:k3_tarski(k2_tarski(X33,X34))=k2_xboole_0(X33,X34), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.19/0.45  fof(c_0_20, plain, ![X29, X30]:k1_enumset1(X29,X29,X30)=k2_tarski(X29,X30), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.19/0.45  fof(c_0_21, plain, ![X27, X28]:k3_xboole_0(X27,X28)=k5_xboole_0(k5_xboole_0(X27,X28),k2_xboole_0(X27,X28)), inference(variable_rename,[status(thm)],[t95_xboole_1])).
% 0.19/0.45  cnf(c_0_22, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.45  cnf(c_0_23, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.45  fof(c_0_24, negated_conjecture, ~(![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>((r1_tarski(X2,X3)&r1_tarski(X2,k3_subset_1(X1,X3)))=>X2=k1_xboole_0))), inference(assume_negation,[status(cth)],[t40_subset_1])).
% 0.19/0.45  fof(c_0_25, plain, ![X38, X39]:(~m1_subset_1(X39,k1_zfmisc_1(X38))|k3_subset_1(X38,X39)=k4_xboole_0(X38,X39)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 0.19/0.45  fof(c_0_26, plain, ![X11, X12]:k4_xboole_0(X11,X12)=k5_xboole_0(X11,k3_xboole_0(X11,X12)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.19/0.45  cnf(c_0_27, plain, (k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.45  cnf(c_0_28, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_22, c_0_23])).
% 0.19/0.45  fof(c_0_29, plain, ![X5, X6]:k5_xboole_0(X5,X6)=k5_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).
% 0.19/0.45  fof(c_0_30, plain, ![X23, X24, X25]:k5_xboole_0(k5_xboole_0(X23,X24),X25)=k5_xboole_0(X23,k5_xboole_0(X24,X25)), inference(variable_rename,[status(thm)],[t91_xboole_1])).
% 0.19/0.45  fof(c_0_31, plain, ![X36, X37]:(((~m1_subset_1(X37,X36)|r2_hidden(X37,X36)|v1_xboole_0(X36))&(~r2_hidden(X37,X36)|m1_subset_1(X37,X36)|v1_xboole_0(X36)))&((~m1_subset_1(X37,X36)|v1_xboole_0(X37)|~v1_xboole_0(X36))&(~v1_xboole_0(X37)|m1_subset_1(X37,X36)|~v1_xboole_0(X36)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 0.19/0.45  fof(c_0_32, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0))&((r1_tarski(esk3_0,esk4_0)&r1_tarski(esk3_0,k3_subset_1(esk2_0,esk4_0)))&esk3_0!=k1_xboole_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_24])])])).
% 0.19/0.45  fof(c_0_33, plain, ![X40]:~v1_xboole_0(k1_zfmisc_1(X40)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).
% 0.19/0.45  cnf(c_0_34, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.45  cnf(c_0_35, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.45  cnf(c_0_36, plain, (k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k1_enumset1(X1,X1,X2)))), inference(rw,[status(thm)],[c_0_27, c_0_28])).
% 0.19/0.45  cnf(c_0_37, plain, (k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.45  cnf(c_0_38, plain, (k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.45  fof(c_0_39, plain, ![X26]:k5_xboole_0(X26,X26)=k1_xboole_0, inference(variable_rename,[status(thm)],[t92_xboole_1])).
% 0.19/0.45  fof(c_0_40, plain, ![X22]:k5_xboole_0(X22,k1_xboole_0)=X22, inference(variable_rename,[status(thm)],[t5_boole])).
% 0.19/0.45  fof(c_0_41, plain, ![X18, X19, X20]:(((r1_tarski(X18,esk1_3(X18,X19,X20))|(~r1_tarski(X18,X19)|~r1_tarski(X20,X19))|X19=k2_xboole_0(X18,X20))&(r1_tarski(X20,esk1_3(X18,X19,X20))|(~r1_tarski(X18,X19)|~r1_tarski(X20,X19))|X19=k2_xboole_0(X18,X20)))&(~r1_tarski(X19,esk1_3(X18,X19,X20))|(~r1_tarski(X18,X19)|~r1_tarski(X20,X19))|X19=k2_xboole_0(X18,X20))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t14_xboole_1])])])])).
% 0.19/0.45  fof(c_0_42, plain, ![X31, X32]:(~r2_hidden(X31,X32)|r1_tarski(X31,k3_tarski(X32))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l49_zfmisc_1])])).
% 0.19/0.45  cnf(c_0_43, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.45  cnf(c_0_44, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.45  cnf(c_0_45, plain, (~v1_xboole_0(k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.45  fof(c_0_46, plain, ![X35]:k3_tarski(k1_zfmisc_1(X35))=X35, inference(variable_rename,[status(thm)],[t99_zfmisc_1])).
% 0.19/0.45  cnf(c_0_47, plain, (k3_subset_1(X2,X1)=k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X2,X1),k3_tarski(k1_enumset1(X2,X2,X1))))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_35]), c_0_36])).
% 0.19/0.45  cnf(c_0_48, plain, (k5_xboole_0(X1,k5_xboole_0(X2,X3))=k5_xboole_0(X3,k5_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.19/0.45  cnf(c_0_49, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.19/0.45  cnf(c_0_50, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.19/0.45  cnf(c_0_51, plain, (r1_tarski(X1,esk1_3(X1,X2,X3))|X2=k2_xboole_0(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.19/0.45  cnf(c_0_52, plain, (r1_tarski(X1,k3_tarski(X2))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.19/0.45  cnf(c_0_53, negated_conjecture, (r2_hidden(esk4_0,k1_zfmisc_1(esk2_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_45])).
% 0.19/0.45  cnf(c_0_54, plain, (k3_tarski(k1_zfmisc_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.19/0.45  fof(c_0_55, plain, ![X9, X10]:(((r1_tarski(X9,X10)|X9!=X10)&(r1_tarski(X10,X9)|X9!=X10))&(~r1_tarski(X9,X10)|~r1_tarski(X10,X9)|X9=X10)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.19/0.45  cnf(c_0_56, plain, (k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_tarski(k1_enumset1(X1,X1,X2)))))=k3_subset_1(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_47, c_0_38])).
% 0.19/0.45  cnf(c_0_57, plain, (k5_xboole_0(X1,k5_xboole_0(X1,X2))=X2), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_50])).
% 0.19/0.45  cnf(c_0_58, plain, (X2=k3_tarski(k1_enumset1(X1,X1,X3))|r1_tarski(X1,esk1_3(X1,X2,X3))|~r1_tarski(X3,X2)|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_51, c_0_28])).
% 0.19/0.45  cnf(c_0_59, negated_conjecture, (r1_tarski(esk4_0,esk2_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_54])).
% 0.19/0.45  cnf(c_0_60, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.19/0.45  cnf(c_0_61, plain, (k5_xboole_0(X1,k3_tarski(k1_enumset1(X2,X2,X1)))=k3_subset_1(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_56, c_0_57])).
% 0.19/0.45  cnf(c_0_62, negated_conjecture, (esk2_0=k3_tarski(k1_enumset1(X1,X1,esk4_0))|r1_tarski(X1,esk1_3(X1,esk2_0,esk4_0))|~r1_tarski(X1,esk2_0)), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.19/0.45  cnf(c_0_63, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_60])).
% 0.19/0.45  cnf(c_0_64, negated_conjecture, (k5_xboole_0(esk4_0,k3_tarski(k1_enumset1(esk2_0,esk2_0,esk4_0)))=k3_subset_1(esk2_0,esk4_0)), inference(spm,[status(thm)],[c_0_61, c_0_44])).
% 0.19/0.45  cnf(c_0_65, negated_conjecture, (k3_tarski(k1_enumset1(esk2_0,esk2_0,esk4_0))=esk2_0|r1_tarski(esk2_0,esk1_3(esk2_0,esk2_0,esk4_0))), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 0.19/0.45  cnf(c_0_66, plain, (X1=k2_xboole_0(X2,X3)|~r1_tarski(X1,esk1_3(X2,X1,X3))|~r1_tarski(X2,X1)|~r1_tarski(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.19/0.45  cnf(c_0_67, negated_conjecture, (r1_tarski(esk3_0,k3_subset_1(esk2_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.45  cnf(c_0_68, negated_conjecture, (k3_subset_1(esk2_0,esk4_0)=k5_xboole_0(esk4_0,esk2_0)|r1_tarski(esk2_0,esk1_3(esk2_0,esk2_0,esk4_0))), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 0.19/0.45  fof(c_0_69, plain, ![X13, X14, X15]:(((r1_tarski(X13,k2_xboole_0(X14,X15))|~r1_tarski(X13,k5_xboole_0(X14,X15)))&(r1_xboole_0(X13,k3_xboole_0(X14,X15))|~r1_tarski(X13,k5_xboole_0(X14,X15))))&(~r1_tarski(X13,k2_xboole_0(X14,X15))|~r1_xboole_0(X13,k3_xboole_0(X14,X15))|r1_tarski(X13,k5_xboole_0(X14,X15)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t107_xboole_1])])])).
% 0.19/0.45  cnf(c_0_70, plain, (X1=k3_tarski(k1_enumset1(X2,X2,X3))|~r1_tarski(X3,X1)|~r1_tarski(X2,X1)|~r1_tarski(X1,esk1_3(X2,X1,X3))), inference(rw,[status(thm)],[c_0_66, c_0_28])).
% 0.19/0.45  cnf(c_0_71, negated_conjecture, (r1_tarski(esk2_0,esk1_3(esk2_0,esk2_0,esk4_0))|r1_tarski(esk3_0,k5_xboole_0(esk4_0,esk2_0))), inference(spm,[status(thm)],[c_0_67, c_0_68])).
% 0.19/0.45  fof(c_0_72, plain, ![X16, X17]:(~r1_tarski(X16,X17)|k2_xboole_0(X16,X17)=X17), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.19/0.45  fof(c_0_73, plain, ![X7, X8]:((~r1_xboole_0(X7,X8)|k3_xboole_0(X7,X8)=k1_xboole_0)&(k3_xboole_0(X7,X8)!=k1_xboole_0|r1_xboole_0(X7,X8))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 0.19/0.45  cnf(c_0_74, plain, (r1_xboole_0(X1,k3_xboole_0(X2,X3))|~r1_tarski(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_69])).
% 0.19/0.45  cnf(c_0_75, negated_conjecture, (k3_tarski(k1_enumset1(esk2_0,esk2_0,esk4_0))=esk2_0|r1_tarski(esk3_0,k5_xboole_0(esk4_0,esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_71]), c_0_59]), c_0_63])])).
% 0.19/0.45  cnf(c_0_76, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_72])).
% 0.19/0.45  cnf(c_0_77, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_73])).
% 0.19/0.45  cnf(c_0_78, plain, (r1_xboole_0(X1,k5_xboole_0(k5_xboole_0(X2,X3),k3_tarski(k1_enumset1(X2,X2,X3))))|~r1_tarski(X1,k5_xboole_0(X2,X3))), inference(rw,[status(thm)],[c_0_74, c_0_36])).
% 0.19/0.45  cnf(c_0_79, negated_conjecture, (k3_subset_1(esk2_0,esk4_0)=k5_xboole_0(esk4_0,esk2_0)|r1_tarski(esk3_0,k5_xboole_0(esk4_0,esk2_0))), inference(spm,[status(thm)],[c_0_64, c_0_75])).
% 0.19/0.45  cnf(c_0_80, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=X2|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_76, c_0_28])).
% 0.19/0.45  cnf(c_0_81, plain, (k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k1_enumset1(X1,X1,X2)))=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_77, c_0_36])).
% 0.19/0.45  cnf(c_0_82, plain, (r1_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k3_tarski(k1_enumset1(X2,X2,X3)))))|~r1_tarski(X1,k5_xboole_0(X2,X3))), inference(rw,[status(thm)],[c_0_78, c_0_38])).
% 0.19/0.45  cnf(c_0_83, negated_conjecture, (r1_tarski(esk3_0,k5_xboole_0(esk4_0,esk2_0))), inference(spm,[status(thm)],[c_0_67, c_0_79])).
% 0.19/0.45  cnf(c_0_84, negated_conjecture, (k3_tarski(k1_enumset1(esk4_0,esk4_0,esk2_0))=esk2_0), inference(spm,[status(thm)],[c_0_80, c_0_59])).
% 0.19/0.45  cnf(c_0_85, negated_conjecture, (r1_tarski(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.45  cnf(c_0_86, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k3_tarski(k1_enumset1(X1,X1,X2))))=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_81, c_0_38])).
% 0.19/0.45  cnf(c_0_87, negated_conjecture, (r1_xboole_0(esk3_0,esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_83]), c_0_84]), c_0_49]), c_0_50])).
% 0.19/0.45  cnf(c_0_88, negated_conjecture, (k3_tarski(k1_enumset1(esk3_0,esk3_0,esk4_0))=esk4_0), inference(spm,[status(thm)],[c_0_80, c_0_85])).
% 0.19/0.45  cnf(c_0_89, negated_conjecture, (esk3_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.45  cnf(c_0_90, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_87]), c_0_88]), c_0_49]), c_0_50]), c_0_89]), ['proof']).
% 0.19/0.45  # SZS output end CNFRefutation
% 0.19/0.45  # Proof object total steps             : 91
% 0.19/0.45  # Proof object clause steps            : 52
% 0.19/0.45  # Proof object formula steps           : 39
% 0.19/0.45  # Proof object conjectures             : 21
% 0.19/0.45  # Proof object clause conjectures      : 18
% 0.19/0.45  # Proof object formula conjectures     : 3
% 0.19/0.45  # Proof object initial clauses used    : 23
% 0.19/0.45  # Proof object initial formulas used   : 19
% 0.19/0.45  # Proof object generating inferences   : 16
% 0.19/0.45  # Proof object simplifying inferences  : 27
% 0.19/0.45  # Training examples: 0 positive, 0 negative
% 0.19/0.45  # Parsed axioms                        : 19
% 0.19/0.45  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.45  # Initial clauses                      : 32
% 0.19/0.45  # Removed in clause preprocessing      : 4
% 0.19/0.45  # Initial clauses in saturation        : 28
% 0.19/0.45  # Processed clauses                    : 772
% 0.19/0.45  # ...of these trivial                  : 57
% 0.19/0.45  # ...subsumed                          : 307
% 0.19/0.45  # ...remaining for further processing  : 408
% 0.19/0.45  # Other redundant clauses eliminated   : 2
% 0.19/0.45  # Clauses deleted for lack of memory   : 0
% 0.19/0.45  # Backward-subsumed                    : 43
% 0.19/0.45  # Backward-rewritten                   : 94
% 0.19/0.45  # Generated clauses                    : 4168
% 0.19/0.45  # ...of the previous two non-trivial   : 3495
% 0.19/0.45  # Contextual simplify-reflections      : 6
% 0.19/0.45  # Paramodulations                      : 4165
% 0.19/0.45  # Factorizations                       : 0
% 0.19/0.45  # Equation resolutions                 : 3
% 0.19/0.45  # Propositional unsat checks           : 0
% 0.19/0.45  #    Propositional check models        : 0
% 0.19/0.45  #    Propositional check unsatisfiable : 0
% 0.19/0.45  #    Propositional clauses             : 0
% 0.19/0.45  #    Propositional clauses after purity: 0
% 0.19/0.45  #    Propositional unsat core size     : 0
% 0.19/0.45  #    Propositional preprocessing time  : 0.000
% 0.19/0.45  #    Propositional encoding time       : 0.000
% 0.19/0.45  #    Propositional solver time         : 0.000
% 0.19/0.45  #    Success case prop preproc time    : 0.000
% 0.19/0.45  #    Success case prop encoding time   : 0.000
% 0.19/0.45  #    Success case prop solver time     : 0.000
% 0.19/0.45  # Current number of processed clauses  : 242
% 0.19/0.45  #    Positive orientable unit clauses  : 57
% 0.19/0.45  #    Positive unorientable unit clauses: 5
% 0.19/0.45  #    Negative unit clauses             : 2
% 0.19/0.45  #    Non-unit-clauses                  : 178
% 0.19/0.45  # Current number of unprocessed clauses: 2573
% 0.19/0.45  # ...number of literals in the above   : 6535
% 0.19/0.45  # Current number of archived formulas  : 0
% 0.19/0.45  # Current number of archived clauses   : 168
% 0.19/0.45  # Clause-clause subsumption calls (NU) : 11896
% 0.19/0.45  # Rec. Clause-clause subsumption calls : 7049
% 0.19/0.45  # Non-unit clause-clause subsumptions  : 255
% 0.19/0.45  # Unit Clause-clause subsumption calls : 1414
% 0.19/0.45  # Rewrite failures with RHS unbound    : 915
% 0.19/0.45  # BW rewrite match attempts            : 284
% 0.19/0.45  # BW rewrite match successes           : 146
% 0.19/0.45  # Condensation attempts                : 0
% 0.19/0.45  # Condensation successes               : 0
% 0.19/0.45  # Termbank termtop insertions          : 62042
% 0.19/0.45  
% 0.19/0.45  # -------------------------------------------------
% 0.19/0.45  # User time                : 0.104 s
% 0.19/0.45  # System time              : 0.009 s
% 0.19/0.45  # Total time               : 0.113 s
% 0.19/0.45  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
