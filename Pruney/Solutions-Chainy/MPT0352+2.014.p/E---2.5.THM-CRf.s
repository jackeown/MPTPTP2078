%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:45:38 EST 2020

% Result     : Theorem 55.17s
% Output     : CNFRefutation 55.17s
% Verified   : 
% Statistics : Number of formulae       :  189 (80954 expanded)
%              Number of clauses        :  156 (37953 expanded)
%              Number of leaves         :   16 (20788 expanded)
%              Depth                    :   31
%              Number of atoms          :  357 (161227 expanded)
%              Number of equality atoms :   74 (52698 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t31_subset_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => ( r1_tarski(X2,X3)
          <=> r1_tarski(k3_subset_1(X1,X3),k3_subset_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_subset_1)).

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

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t106_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k4_xboole_0(X2,X3))
     => ( r1_tarski(X1,X2)
        & r1_xboole_0(X1,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

fof(t73_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,k2_xboole_0(X2,X3))
        & r1_xboole_0(X1,X3) )
     => r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_xboole_1)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(c_0_16,plain,(
    ! [X19,X20] : r1_tarski(k4_xboole_0(X19,X20),X19) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

fof(c_0_17,plain,(
    ! [X10,X11] : k4_xboole_0(X10,X11) = k5_xboole_0(X10,k3_xboole_0(X10,X11)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_18,plain,(
    ! [X23,X24] : k4_xboole_0(X23,k4_xboole_0(X23,X24)) = k3_xboole_0(X23,X24) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_19,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X1))
       => ! [X3] :
            ( m1_subset_1(X3,k1_zfmisc_1(X1))
           => ( r1_tarski(X2,X3)
            <=> r1_tarski(k3_subset_1(X1,X3),k3_subset_1(X1,X2)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t31_subset_1])).

cnf(c_0_20,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_23,plain,(
    ! [X28,X29,X30,X31,X32,X33] :
      ( ( ~ r2_hidden(X30,X29)
        | r1_tarski(X30,X28)
        | X29 != k1_zfmisc_1(X28) )
      & ( ~ r1_tarski(X31,X28)
        | r2_hidden(X31,X29)
        | X29 != k1_zfmisc_1(X28) )
      & ( ~ r2_hidden(esk1_2(X32,X33),X33)
        | ~ r1_tarski(esk1_2(X32,X33),X32)
        | X33 = k1_zfmisc_1(X32) )
      & ( r2_hidden(esk1_2(X32,X33),X33)
        | r1_tarski(esk1_2(X32,X33),X32)
        | X33 = k1_zfmisc_1(X32) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

fof(c_0_24,plain,(
    ! [X35,X36] :
      ( ( ~ m1_subset_1(X36,X35)
        | r2_hidden(X36,X35)
        | v1_xboole_0(X35) )
      & ( ~ r2_hidden(X36,X35)
        | m1_subset_1(X36,X35)
        | v1_xboole_0(X35) )
      & ( ~ m1_subset_1(X36,X35)
        | v1_xboole_0(X36)
        | ~ v1_xboole_0(X35) )
      & ( ~ v1_xboole_0(X36)
        | m1_subset_1(X36,X35)
        | ~ v1_xboole_0(X35) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

fof(c_0_25,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))
    & m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0))
    & ( ~ r1_tarski(esk3_0,esk4_0)
      | ~ r1_tarski(k3_subset_1(esk2_0,esk4_0),k3_subset_1(esk2_0,esk3_0)) )
    & ( r1_tarski(esk3_0,esk4_0)
      | r1_tarski(k3_subset_1(esk2_0,esk4_0),k3_subset_1(esk2_0,esk3_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).

fof(c_0_26,plain,(
    ! [X39] : ~ v1_xboole_0(k1_zfmisc_1(X39)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).

cnf(c_0_27,plain,
    ( r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X1) ),
    inference(rw,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_28,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22,c_0_21]),c_0_21])).

fof(c_0_29,plain,(
    ! [X17,X18] :
      ( ~ r1_tarski(X17,X18)
      | k3_xboole_0(X17,X18) = X17 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_30,plain,
    ( r1_tarski(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_31,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_32,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_33,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_34,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_35,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_36,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(er,[status(thm)],[c_0_30])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(esk4_0,k1_zfmisc_1(esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33])).

cnf(c_0_38,plain,
    ( r1_tarski(X1,X1)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_39,negated_conjecture,
    ( r1_tarski(esk4_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

fof(c_0_40,plain,(
    ! [X6,X7] : k3_xboole_0(X6,X7) = k3_xboole_0(X7,X6) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_41,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,X1))) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_28,c_0_35])).

cnf(c_0_42,negated_conjecture,
    ( r1_tarski(esk4_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_43,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_44,plain,
    ( r1_tarski(k5_xboole_0(X1,X1),X1)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_27,c_0_35])).

fof(c_0_45,plain,(
    ! [X12,X13,X14] :
      ( ( r1_tarski(X12,X13)
        | ~ r1_tarski(X12,k4_xboole_0(X13,X14)) )
      & ( r1_xboole_0(X12,X14)
        | ~ r1_tarski(X12,k4_xboole_0(X13,X14)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t106_xboole_1])])])).

cnf(c_0_46,plain,
    ( k5_xboole_0(X1,X1) = k3_xboole_0(X1,X2)
    | ~ r1_tarski(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_28,c_0_35])).

cnf(c_0_47,negated_conjecture,
    ( k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,k5_xboole_0(esk4_0,esk4_0))) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_48,plain,
    ( k3_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_43])).

cnf(c_0_49,negated_conjecture,
    ( r1_tarski(k5_xboole_0(esk4_0,esk4_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_39])).

cnf(c_0_50,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_tarski(X1,k4_xboole_0(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_51,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X1,X2))) = k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_28,c_0_28])).

cnf(c_0_52,negated_conjecture,
    ( k3_xboole_0(esk4_0,k5_xboole_0(esk4_0,esk4_0)) = k5_xboole_0(esk4_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_42])])).

cnf(c_0_53,negated_conjecture,
    ( k5_xboole_0(esk4_0,k5_xboole_0(esk4_0,esk4_0)) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_49])])).

fof(c_0_54,plain,(
    ! [X25,X26,X27] :
      ( ~ r1_tarski(X25,k2_xboole_0(X26,X27))
      | ~ r1_xboole_0(X25,X27)
      | r1_tarski(X25,X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t73_xboole_1])])).

fof(c_0_55,plain,(
    ! [X15,X16] :
      ( ~ r1_tarski(X15,X16)
      | k2_xboole_0(X15,X16) = X16 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_56,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_tarski(X1,k5_xboole_0(X3,k3_xboole_0(X3,X2))) ),
    inference(rw,[status(thm)],[c_0_50,c_0_21])).

cnf(c_0_57,negated_conjecture,
    ( k3_xboole_0(esk4_0,esk4_0) = esk4_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_52]),c_0_53]),c_0_53])).

cnf(c_0_58,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_59,plain,(
    ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_60,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k4_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_61,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r1_xboole_0(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_62,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_63,negated_conjecture,
    ( r1_xboole_0(X1,esk4_0)
    | ~ r1_tarski(X1,k5_xboole_0(esk4_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_64,negated_conjecture,
    ( r1_tarski(k5_xboole_0(esk4_0,esk4_0),k5_xboole_0(esk4_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_49])).

cnf(c_0_65,negated_conjecture,
    ( r2_hidden(esk3_0,k1_zfmisc_1(esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_58]),c_0_33])).

cnf(c_0_66,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_67,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))) ),
    inference(rw,[status(thm)],[c_0_60,c_0_21])).

cnf(c_0_68,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3)
    | ~ r1_tarski(X2,X3)
    | ~ r1_xboole_0(X1,X3) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_69,negated_conjecture,
    ( r1_xboole_0(k5_xboole_0(esk4_0,esk4_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_70,negated_conjecture,
    ( r1_tarski(esk3_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_65])).

fof(c_0_71,plain,(
    ! [X21,X22] : k2_xboole_0(X21,k4_xboole_0(X22,X21)) = k2_xboole_0(X21,X22) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

cnf(c_0_72,plain,
    ( k2_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_62,c_0_66])).

cnf(c_0_73,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k3_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_67,c_0_28])).

cnf(c_0_74,negated_conjecture,
    ( r1_tarski(k5_xboole_0(esk4_0,esk4_0),X1)
    | ~ r1_tarski(X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_49]),c_0_69])])).

cnf(c_0_75,negated_conjecture,
    ( r1_tarski(esk3_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_70])).

cnf(c_0_76,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_77,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_62,c_0_72])).

cnf(c_0_78,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k3_xboole_0(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_73,c_0_43])).

cnf(c_0_79,negated_conjecture,
    ( r1_tarski(k5_xboole_0(esk4_0,esk4_0),k3_xboole_0(esk4_0,X1)) ),
    inference(spm,[status(thm)],[c_0_74,c_0_34])).

cnf(c_0_80,negated_conjecture,
    ( r1_tarski(k5_xboole_0(k5_xboole_0(esk4_0,esk4_0),k5_xboole_0(esk4_0,esk4_0)),k5_xboole_0(esk4_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_49])).

cnf(c_0_81,negated_conjecture,
    ( k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,k5_xboole_0(esk3_0,esk3_0))) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_41,c_0_75])).

cnf(c_0_82,negated_conjecture,
    ( r1_tarski(k5_xboole_0(esk3_0,esk3_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_70])).

cnf(c_0_83,plain,
    ( k2_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_76,c_0_21])).

cnf(c_0_84,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,k3_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_77,c_0_34])).

cnf(c_0_85,negated_conjecture,
    ( r1_tarski(k5_xboole_0(esk4_0,esk4_0),X1) ),
    inference(spm,[status(thm)],[c_0_78,c_0_79])).

cnf(c_0_86,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(esk4_0,esk4_0),k5_xboole_0(esk4_0,esk4_0)) = k5_xboole_0(esk4_0,esk4_0)
    | ~ r1_tarski(k5_xboole_0(esk4_0,esk4_0),k5_xboole_0(k5_xboole_0(esk4_0,esk4_0),k5_xboole_0(esk4_0,esk4_0))) ),
    inference(spm,[status(thm)],[c_0_77,c_0_80])).

cnf(c_0_87,negated_conjecture,
    ( k3_xboole_0(esk3_0,k5_xboole_0(esk3_0,esk3_0)) = k5_xboole_0(esk3_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_81]),c_0_75])])).

cnf(c_0_88,negated_conjecture,
    ( k5_xboole_0(esk3_0,k5_xboole_0(esk3_0,esk3_0)) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_48]),c_0_82])])).

cnf(c_0_89,plain,
    ( k2_xboole_0(X1,X2) = X1
    | ~ r1_tarski(k5_xboole_0(X2,k3_xboole_0(X2,X1)),X1) ),
    inference(spm,[status(thm)],[c_0_72,c_0_83])).

cnf(c_0_90,negated_conjecture,
    ( k3_xboole_0(k5_xboole_0(esk4_0,esk4_0),X1) = k5_xboole_0(esk4_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_84,c_0_85])).

cnf(c_0_91,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(esk4_0,esk4_0),k5_xboole_0(esk4_0,esk4_0)) = k5_xboole_0(esk4_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_86,c_0_85])])).

cnf(c_0_92,negated_conjecture,
    ( k3_xboole_0(esk3_0,esk3_0) = esk3_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_87]),c_0_87]),c_0_88]),c_0_88])).

cnf(c_0_93,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k2_xboole_0(X3,X2))
    | ~ r1_xboole_0(X1,X3) ),
    inference(spm,[status(thm)],[c_0_61,c_0_66])).

cnf(c_0_94,negated_conjecture,
    ( k2_xboole_0(X1,k5_xboole_0(esk4_0,esk4_0)) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_90]),c_0_91]),c_0_85])])).

cnf(c_0_95,negated_conjecture,
    ( r1_xboole_0(X1,esk3_0)
    | ~ r1_tarski(X1,k5_xboole_0(esk3_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_92])).

cnf(c_0_96,negated_conjecture,
    ( r1_tarski(k5_xboole_0(esk3_0,esk3_0),k5_xboole_0(esk3_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_82])).

fof(c_0_97,plain,(
    ! [X37,X38] :
      ( ~ m1_subset_1(X38,k1_zfmisc_1(X37))
      | k3_subset_1(X37,X38) = k4_xboole_0(X37,X38) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

cnf(c_0_98,plain,
    ( r2_hidden(X1,X3)
    | ~ r1_tarski(X1,X2)
    | X3 != k1_zfmisc_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_99,negated_conjecture,
    ( r1_tarski(X1,k5_xboole_0(esk4_0,esk4_0))
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_93,c_0_94])).

cnf(c_0_100,negated_conjecture,
    ( r1_xboole_0(k5_xboole_0(esk3_0,esk3_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_95,c_0_96])).

cnf(c_0_101,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_97])).

cnf(c_0_102,plain,
    ( m1_subset_1(X1,X2)
    | v1_xboole_0(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_103,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(er,[status(thm)],[c_0_98])).

cnf(c_0_104,negated_conjecture,
    ( r1_tarski(k5_xboole_0(esk3_0,esk3_0),k5_xboole_0(esk4_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_82]),c_0_100])])).

cnf(c_0_105,plain,
    ( k2_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2))) = k2_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_83,c_0_43])).

cnf(c_0_106,negated_conjecture,
    ( k2_xboole_0(k5_xboole_0(esk4_0,esk4_0),X1) = X1 ),
    inference(spm,[status(thm)],[c_0_66,c_0_94])).

cnf(c_0_107,plain,
    ( r1_tarski(k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k3_xboole_0(X1,X2),X3)),X1) ),
    inference(spm,[status(thm)],[c_0_73,c_0_27])).

cnf(c_0_108,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3)
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_78,c_0_35])).

fof(c_0_109,plain,(
    ! [X8,X9] :
      ( ~ r1_xboole_0(X8,X9)
      | r1_xboole_0(X9,X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

cnf(c_0_110,plain,
    ( k3_subset_1(X2,X1) = k5_xboole_0(X2,k3_xboole_0(X2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_101,c_0_21])).

cnf(c_0_111,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_103]),c_0_33])).

cnf(c_0_112,negated_conjecture,
    ( k5_xboole_0(esk4_0,esk4_0) = k5_xboole_0(esk3_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_104]),c_0_85])])).

cnf(c_0_113,negated_conjecture,
    ( k5_xboole_0(X1,k5_xboole_0(esk4_0,esk4_0)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_106]),c_0_90]),c_0_106])).

cnf(c_0_114,plain,
    ( k2_xboole_0(X1,k3_xboole_0(X1,X2)) = X1 ),
    inference(spm,[status(thm)],[c_0_89,c_0_107])).

cnf(c_0_115,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_108,c_0_34])).

cnf(c_0_116,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_109])).

cnf(c_0_117,plain,
    ( r1_xboole_0(k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3)),X2) ),
    inference(spm,[status(thm)],[c_0_56,c_0_27])).

cnf(c_0_118,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,X2))) = X2
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_48])).

cnf(c_0_119,plain,
    ( k5_xboole_0(X1,X2) = k3_subset_1(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_110,c_0_48]),c_0_111])).

cnf(c_0_120,plain,
    ( r1_tarski(k5_xboole_0(X1,k3_xboole_0(X2,X1)),X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_43])).

cnf(c_0_121,negated_conjecture,
    ( k3_xboole_0(k5_xboole_0(esk3_0,esk3_0),X1) = k5_xboole_0(esk3_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_90,c_0_112]),c_0_112])).

cnf(c_0_122,negated_conjecture,
    ( k5_xboole_0(X1,k5_xboole_0(esk3_0,esk3_0)) = X1 ),
    inference(rw,[status(thm)],[c_0_113,c_0_112])).

cnf(c_0_123,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_51]),c_0_66]),c_0_114])).

cnf(c_0_124,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_48]),c_0_34])])).

cnf(c_0_125,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k2_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_28]),c_0_66]),c_0_66])).

cnf(c_0_126,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X1,k3_xboole_0(X3,X4)) ),
    inference(spm,[status(thm)],[c_0_73,c_0_115])).

cnf(c_0_127,negated_conjecture,
    ( r1_tarski(esk4_0,X1)
    | ~ r1_tarski(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_108,c_0_39])).

cnf(c_0_128,plain,
    ( r1_xboole_0(X1,k5_xboole_0(k5_xboole_0(X2,k3_xboole_0(X2,X1)),k3_xboole_0(k5_xboole_0(X2,k3_xboole_0(X2,X1)),X3))) ),
    inference(spm,[status(thm)],[c_0_116,c_0_117])).

cnf(c_0_129,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k3_subset_1(X1,X2))) = X2
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_118,c_0_119])).

cnf(c_0_130,negated_conjecture,
    ( r1_tarski(X1,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120,c_0_121]),c_0_122])).

cnf(c_0_131,plain,
    ( k2_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_123,c_0_124]),c_0_125])).

cnf(c_0_132,negated_conjecture,
    ( r1_tarski(k3_xboole_0(esk4_0,X1),X2)
    | ~ r1_tarski(esk2_0,k3_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_126,c_0_127])).

cnf(c_0_133,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_tarski(X2,k5_xboole_0(X3,k3_xboole_0(X3,X1))) ),
    inference(spm,[status(thm)],[c_0_128,c_0_129])).

cnf(c_0_134,negated_conjecture,
    ( r1_tarski(k2_xboole_0(X1,X2),X2)
    | ~ r1_xboole_0(k2_xboole_0(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_93,c_0_130])).

cnf(c_0_135,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,k3_xboole_0(X1,X2))) = X1 ),
    inference(rw,[status(thm)],[c_0_125,c_0_131])).

cnf(c_0_136,negated_conjecture,
    ( r1_tarski(k3_xboole_0(esk4_0,X1),X2)
    | ~ r1_tarski(esk2_0,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(spm,[status(thm)],[c_0_132,c_0_35])).

cnf(c_0_137,negated_conjecture,
    ( r1_xboole_0(X1,esk4_0)
    | ~ r1_tarski(esk2_0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(spm,[status(thm)],[c_0_133,c_0_127])).

cnf(c_0_138,negated_conjecture,
    ( r1_tarski(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))
    | ~ r1_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_134,c_0_135])).

cnf(c_0_139,plain,
    ( r1_xboole_0(k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3),X2) ),
    inference(spm,[status(thm)],[c_0_56,c_0_34])).

cnf(c_0_140,negated_conjecture,
    ( r1_tarski(k3_xboole_0(esk4_0,X1),esk2_0)
    | ~ r1_tarski(esk2_0,X2) ),
    inference(spm,[status(thm)],[c_0_136,c_0_130])).

cnf(c_0_141,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k3_subset_1(X2,k3_xboole_0(X2,X3))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_119]),c_0_34])])).

cnf(c_0_142,negated_conjecture,
    ( r1_tarski(k2_xboole_0(X1,X2),X1)
    | ~ r1_xboole_0(k2_xboole_0(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_61,c_0_130])).

cnf(c_0_143,plain,
    ( k2_xboole_0(X1,k5_xboole_0(X2,X1)) = k2_xboole_0(X1,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_83,c_0_48])).

cnf(c_0_144,negated_conjecture,
    ( r1_xboole_0(X1,esk4_0)
    | ~ r1_xboole_0(esk2_0,k3_xboole_0(esk2_0,X1)) ),
    inference(spm,[status(thm)],[c_0_137,c_0_138])).

cnf(c_0_145,plain,
    ( r1_xboole_0(X1,k3_xboole_0(k5_xboole_0(X2,k3_xboole_0(X2,X1)),X3)) ),
    inference(spm,[status(thm)],[c_0_116,c_0_139])).

cnf(c_0_146,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_tarski(X1,k3_subset_1(X3,k3_xboole_0(X3,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_119]),c_0_34])])).

cnf(c_0_147,negated_conjecture,
    ( r1_tarski(k3_xboole_0(esk4_0,X1),esk2_0) ),
    inference(spm,[status(thm)],[c_0_140,c_0_130])).

cnf(c_0_148,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k3_subset_1(X2,X3))
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_141,c_0_48])).

cnf(c_0_149,negated_conjecture,
    ( r1_tarski(k2_xboole_0(X1,X2),X1)
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(k2_xboole_0(X1,X2),k5_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_142,c_0_143])).

cnf(c_0_150,negated_conjecture,
    ( r1_xboole_0(X1,esk4_0)
    | ~ r1_xboole_0(esk2_0,k3_xboole_0(X1,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_144,c_0_43])).

cnf(c_0_151,plain,
    ( r1_xboole_0(X1,k3_xboole_0(k3_subset_1(X2,k3_xboole_0(X2,X1)),X3)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_145,c_0_119]),c_0_34])])).

cnf(c_0_152,plain,
    ( r1_xboole_0(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ r1_tarski(X1,k3_subset_1(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_110])).

cnf(c_0_153,negated_conjecture,
    ( r1_tarski(esk3_0,esk4_0)
    | r1_tarski(k3_subset_1(esk2_0,esk4_0),k3_subset_1(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_154,plain,
    ( r1_tarski(k5_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(k2_xboole_0(X1,X2),X3)),X1)
    | ~ r1_xboole_0(k5_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(k2_xboole_0(X1,X2),X3)),X2) ),
    inference(spm,[status(thm)],[c_0_61,c_0_27])).

cnf(c_0_155,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_tarski(X1,k3_subset_1(X3,X2))
    | ~ r1_tarski(X2,X3) ),
    inference(spm,[status(thm)],[c_0_146,c_0_48])).

cnf(c_0_156,negated_conjecture,
    ( r1_tarski(X1,esk2_0)
    | ~ r1_tarski(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_147,c_0_48])).

cnf(c_0_157,negated_conjecture,
    ( r1_tarski(k3_subset_1(X1,X2),X1)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_148,c_0_130])).

cnf(c_0_158,negated_conjecture,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1)
    | ~ r1_xboole_0(X1,k5_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_149,c_0_62])).

cnf(c_0_159,negated_conjecture,
    ( r1_xboole_0(k3_subset_1(X1,k3_xboole_0(X1,esk2_0)),esk4_0) ),
    inference(spm,[status(thm)],[c_0_150,c_0_151])).

cnf(c_0_160,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r1_xboole_0(X1,k5_xboole_0(X3,k3_xboole_0(X3,X2))) ),
    inference(spm,[status(thm)],[c_0_61,c_0_83])).

cnf(c_0_161,negated_conjecture,
    ( r1_tarski(esk3_0,esk4_0)
    | r1_xboole_0(k3_subset_1(esk2_0,esk4_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_152,c_0_153]),c_0_58])])).

cnf(c_0_162,plain,
    ( k2_xboole_0(X1,k3_subset_1(X2,X1)) = k2_xboole_0(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_83,c_0_110])).

cnf(c_0_163,plain,
    ( r1_tarski(k3_subset_1(k2_xboole_0(X1,X2),X3),X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_xboole_0(X1,X2)))
    | ~ r1_xboole_0(k3_subset_1(k2_xboole_0(X1,X2),X3),X2) ),
    inference(spm,[status(thm)],[c_0_154,c_0_110])).

cnf(c_0_164,negated_conjecture,
    ( r1_xboole_0(k3_subset_1(X1,X2),X2)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_155,c_0_130])).

cnf(c_0_165,plain,
    ( k2_xboole_0(X1,X2) = X1
    | ~ r1_tarski(k3_subset_1(X2,k3_xboole_0(X2,X1)),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_119]),c_0_34])])).

cnf(c_0_166,negated_conjecture,
    ( r1_tarski(k3_subset_1(esk4_0,X1),esk2_0)
    | ~ r1_tarski(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_156,c_0_157])).

cnf(c_0_167,plain,
    ( r1_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))
    | ~ r1_tarski(X1,k3_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_28])).

cnf(c_0_168,negated_conjecture,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1)
    | ~ r1_xboole_0(X1,k3_subset_1(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_158,c_0_119])).

cnf(c_0_169,negated_conjecture,
    ( r1_xboole_0(esk4_0,k3_subset_1(X1,k3_xboole_0(X1,esk2_0))) ),
    inference(spm,[status(thm)],[c_0_116,c_0_159])).

cnf(c_0_170,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r1_xboole_0(X1,k3_subset_1(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_160,c_0_110])).

cnf(c_0_171,negated_conjecture,
    ( r1_tarski(esk3_0,esk4_0)
    | r1_xboole_0(esk3_0,k3_subset_1(esk2_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_116,c_0_161])).

cnf(c_0_172,plain,
    ( r1_tarski(X1,k3_subset_1(X2,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,k2_xboole_0(X3,X2))
    | ~ r1_xboole_0(X1,X3) ),
    inference(spm,[status(thm)],[c_0_93,c_0_162])).

cnf(c_0_173,negated_conjecture,
    ( r1_tarski(k3_subset_1(k2_xboole_0(X1,X2),X2),X1)
    | ~ r1_tarski(X2,k2_xboole_0(X1,X2)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_163,c_0_164]),c_0_111])).

cnf(c_0_174,negated_conjecture,
    ( k2_xboole_0(esk2_0,esk4_0) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_165,c_0_166]),c_0_34])])).

cnf(c_0_175,plain,
    ( r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3)
    | ~ r1_tarski(X3,k3_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_116,c_0_167])).

cnf(c_0_176,negated_conjecture,
    ( r1_tarski(esk4_0,k3_xboole_0(esk2_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_168,c_0_169]),c_0_43]),c_0_34])])).

cnf(c_0_177,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_34,c_0_43])).

cnf(c_0_178,negated_conjecture,
    ( r1_tarski(esk3_0,esk4_0)
    | ~ r1_tarski(esk3_0,k2_xboole_0(esk2_0,esk4_0)) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_170,c_0_171]),c_0_32])]),c_0_66])).

cnf(c_0_179,plain,
    ( r1_tarski(X1,k3_subset_1(X2,X3))
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X2)
    | ~ r1_xboole_0(X1,X3) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_172,c_0_62]),c_0_111])).

cnf(c_0_180,negated_conjecture,
    ( r1_tarski(k3_subset_1(esk2_0,esk4_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_173,c_0_174]),c_0_39])])).

cnf(c_0_181,plain,
    ( r1_xboole_0(k3_subset_1(X1,k3_xboole_0(X1,X2)),X3)
    | ~ r1_tarski(X3,k3_xboole_0(X1,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_175,c_0_119]),c_0_34])])).

cnf(c_0_182,negated_conjecture,
    ( k3_xboole_0(esk2_0,esk4_0) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_176]),c_0_177])])).

cnf(c_0_183,negated_conjecture,
    ( ~ r1_tarski(esk3_0,esk4_0)
    | ~ r1_tarski(k3_subset_1(esk2_0,esk4_0),k3_subset_1(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_184,negated_conjecture,
    ( r1_tarski(esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_178,c_0_72]),c_0_70]),c_0_39])])).

cnf(c_0_185,negated_conjecture,
    ( r1_tarski(k3_subset_1(esk2_0,esk4_0),k3_subset_1(esk2_0,X1))
    | ~ r1_tarski(X1,esk2_0)
    | ~ r1_xboole_0(k3_subset_1(esk2_0,esk4_0),X1) ),
    inference(spm,[status(thm)],[c_0_179,c_0_180])).

cnf(c_0_186,negated_conjecture,
    ( r1_xboole_0(k3_subset_1(esk2_0,esk4_0),X1)
    | ~ r1_tarski(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_181,c_0_182])).

cnf(c_0_187,negated_conjecture,
    ( ~ r1_tarski(k3_subset_1(esk2_0,esk4_0),k3_subset_1(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_183,c_0_184])])).

cnf(c_0_188,plain,
    ( $false ),
    inference(cdclpropres,[status(thm)],[c_0_185,c_0_186,c_0_187,c_0_184,c_0_70]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:13:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 55.17/55.37  # AutoSched0-Mode selected heuristic G_E___208_B07____S_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 55.17/55.37  # and selection function SelectComplexExceptUniqMaxHorn.
% 55.17/55.37  #
% 55.17/55.37  # Preprocessing time       : 0.027 s
% 55.17/55.37  # Presaturation interreduction done
% 55.17/55.37  # SatCheck found unsatisfiable ground set
% 55.17/55.37  
% 55.17/55.37  # Proof found!
% 55.17/55.37  # SZS status Theorem
% 55.17/55.37  # SZS output start CNFRefutation
% 55.17/55.37  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 55.17/55.37  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 55.17/55.37  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 55.17/55.37  fof(t31_subset_1, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(r1_tarski(X2,X3)<=>r1_tarski(k3_subset_1(X1,X3),k3_subset_1(X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_subset_1)).
% 55.17/55.37  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 55.17/55.37  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 55.17/55.37  fof(fc1_subset_1, axiom, ![X1]:~(v1_xboole_0(k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 55.17/55.37  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 55.17/55.37  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 55.17/55.37  fof(t106_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k4_xboole_0(X2,X3))=>(r1_tarski(X1,X2)&r1_xboole_0(X1,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 55.17/55.37  fof(t73_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,k2_xboole_0(X2,X3))&r1_xboole_0(X1,X3))=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_xboole_1)).
% 55.17/55.37  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 55.17/55.37  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 55.17/55.37  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 55.17/55.37  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 55.17/55.37  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 55.17/55.37  fof(c_0_16, plain, ![X19, X20]:r1_tarski(k4_xboole_0(X19,X20),X19), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 55.17/55.37  fof(c_0_17, plain, ![X10, X11]:k4_xboole_0(X10,X11)=k5_xboole_0(X10,k3_xboole_0(X10,X11)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 55.17/55.37  fof(c_0_18, plain, ![X23, X24]:k4_xboole_0(X23,k4_xboole_0(X23,X24))=k3_xboole_0(X23,X24), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 55.17/55.37  fof(c_0_19, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(r1_tarski(X2,X3)<=>r1_tarski(k3_subset_1(X1,X3),k3_subset_1(X1,X2)))))), inference(assume_negation,[status(cth)],[t31_subset_1])).
% 55.17/55.37  cnf(c_0_20, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 55.17/55.37  cnf(c_0_21, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 55.17/55.37  cnf(c_0_22, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 55.17/55.37  fof(c_0_23, plain, ![X28, X29, X30, X31, X32, X33]:(((~r2_hidden(X30,X29)|r1_tarski(X30,X28)|X29!=k1_zfmisc_1(X28))&(~r1_tarski(X31,X28)|r2_hidden(X31,X29)|X29!=k1_zfmisc_1(X28)))&((~r2_hidden(esk1_2(X32,X33),X33)|~r1_tarski(esk1_2(X32,X33),X32)|X33=k1_zfmisc_1(X32))&(r2_hidden(esk1_2(X32,X33),X33)|r1_tarski(esk1_2(X32,X33),X32)|X33=k1_zfmisc_1(X32)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 55.17/55.37  fof(c_0_24, plain, ![X35, X36]:(((~m1_subset_1(X36,X35)|r2_hidden(X36,X35)|v1_xboole_0(X35))&(~r2_hidden(X36,X35)|m1_subset_1(X36,X35)|v1_xboole_0(X35)))&((~m1_subset_1(X36,X35)|v1_xboole_0(X36)|~v1_xboole_0(X35))&(~v1_xboole_0(X36)|m1_subset_1(X36,X35)|~v1_xboole_0(X35)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 55.17/55.37  fof(c_0_25, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))&(m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0))&((~r1_tarski(esk3_0,esk4_0)|~r1_tarski(k3_subset_1(esk2_0,esk4_0),k3_subset_1(esk2_0,esk3_0)))&(r1_tarski(esk3_0,esk4_0)|r1_tarski(k3_subset_1(esk2_0,esk4_0),k3_subset_1(esk2_0,esk3_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).
% 55.17/55.37  fof(c_0_26, plain, ![X39]:~v1_xboole_0(k1_zfmisc_1(X39)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).
% 55.17/55.37  cnf(c_0_27, plain, (r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X1)), inference(rw,[status(thm)],[c_0_20, c_0_21])).
% 55.17/55.37  cnf(c_0_28, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22, c_0_21]), c_0_21])).
% 55.17/55.37  fof(c_0_29, plain, ![X17, X18]:(~r1_tarski(X17,X18)|k3_xboole_0(X17,X18)=X17), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 55.17/55.37  cnf(c_0_30, plain, (r1_tarski(X1,X3)|~r2_hidden(X1,X2)|X2!=k1_zfmisc_1(X3)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 55.17/55.37  cnf(c_0_31, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 55.17/55.37  cnf(c_0_32, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 55.17/55.37  cnf(c_0_33, plain, (~v1_xboole_0(k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 55.17/55.37  cnf(c_0_34, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 55.17/55.37  cnf(c_0_35, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 55.17/55.37  cnf(c_0_36, plain, (r1_tarski(X1,X2)|~r2_hidden(X1,k1_zfmisc_1(X2))), inference(er,[status(thm)],[c_0_30])).
% 55.17/55.37  cnf(c_0_37, negated_conjecture, (r2_hidden(esk4_0,k1_zfmisc_1(esk2_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_33])).
% 55.17/55.37  cnf(c_0_38, plain, (r1_tarski(X1,X1)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 55.17/55.37  cnf(c_0_39, negated_conjecture, (r1_tarski(esk4_0,esk2_0)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 55.17/55.37  fof(c_0_40, plain, ![X6, X7]:k3_xboole_0(X6,X7)=k3_xboole_0(X7,X6), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 55.17/55.37  cnf(c_0_41, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,X1)))=X1|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_28, c_0_35])).
% 55.17/55.37  cnf(c_0_42, negated_conjecture, (r1_tarski(esk4_0,esk4_0)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 55.17/55.37  cnf(c_0_43, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 55.17/55.37  cnf(c_0_44, plain, (r1_tarski(k5_xboole_0(X1,X1),X1)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_27, c_0_35])).
% 55.17/55.37  fof(c_0_45, plain, ![X12, X13, X14]:((r1_tarski(X12,X13)|~r1_tarski(X12,k4_xboole_0(X13,X14)))&(r1_xboole_0(X12,X14)|~r1_tarski(X12,k4_xboole_0(X13,X14)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t106_xboole_1])])])).
% 55.17/55.37  cnf(c_0_46, plain, (k5_xboole_0(X1,X1)=k3_xboole_0(X1,X2)|~r1_tarski(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))), inference(spm,[status(thm)],[c_0_28, c_0_35])).
% 55.17/55.37  cnf(c_0_47, negated_conjecture, (k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,k5_xboole_0(esk4_0,esk4_0)))=esk4_0), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 55.17/55.37  cnf(c_0_48, plain, (k3_xboole_0(X1,X2)=X2|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_35, c_0_43])).
% 55.17/55.37  cnf(c_0_49, negated_conjecture, (r1_tarski(k5_xboole_0(esk4_0,esk4_0),esk4_0)), inference(spm,[status(thm)],[c_0_44, c_0_39])).
% 55.17/55.37  cnf(c_0_50, plain, (r1_xboole_0(X1,X2)|~r1_tarski(X1,k4_xboole_0(X3,X2))), inference(split_conjunct,[status(thm)],[c_0_45])).
% 55.17/55.37  cnf(c_0_51, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X1,X2)))=k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))), inference(spm,[status(thm)],[c_0_28, c_0_28])).
% 55.17/55.37  cnf(c_0_52, negated_conjecture, (k3_xboole_0(esk4_0,k5_xboole_0(esk4_0,esk4_0))=k5_xboole_0(esk4_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_42])])).
% 55.17/55.37  cnf(c_0_53, negated_conjecture, (k5_xboole_0(esk4_0,k5_xboole_0(esk4_0,esk4_0))=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_49])])).
% 55.17/55.37  fof(c_0_54, plain, ![X25, X26, X27]:(~r1_tarski(X25,k2_xboole_0(X26,X27))|~r1_xboole_0(X25,X27)|r1_tarski(X25,X26)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t73_xboole_1])])).
% 55.17/55.37  fof(c_0_55, plain, ![X15, X16]:(~r1_tarski(X15,X16)|k2_xboole_0(X15,X16)=X16), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 55.17/55.37  cnf(c_0_56, plain, (r1_xboole_0(X1,X2)|~r1_tarski(X1,k5_xboole_0(X3,k3_xboole_0(X3,X2)))), inference(rw,[status(thm)],[c_0_50, c_0_21])).
% 55.17/55.37  cnf(c_0_57, negated_conjecture, (k3_xboole_0(esk4_0,esk4_0)=esk4_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_52]), c_0_53]), c_0_53])).
% 55.17/55.37  cnf(c_0_58, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 55.17/55.37  fof(c_0_59, plain, ![X4, X5]:k2_xboole_0(X4,X5)=k2_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 55.17/55.37  cnf(c_0_60, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k4_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_45])).
% 55.17/55.37  cnf(c_0_61, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k2_xboole_0(X2,X3))|~r1_xboole_0(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 55.17/55.37  cnf(c_0_62, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 55.17/55.37  cnf(c_0_63, negated_conjecture, (r1_xboole_0(X1,esk4_0)|~r1_tarski(X1,k5_xboole_0(esk4_0,esk4_0))), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 55.17/55.37  cnf(c_0_64, negated_conjecture, (r1_tarski(k5_xboole_0(esk4_0,esk4_0),k5_xboole_0(esk4_0,esk4_0))), inference(spm,[status(thm)],[c_0_38, c_0_49])).
% 55.17/55.37  cnf(c_0_65, negated_conjecture, (r2_hidden(esk3_0,k1_zfmisc_1(esk2_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_58]), c_0_33])).
% 55.17/55.37  cnf(c_0_66, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 55.17/55.37  cnf(c_0_67, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))), inference(rw,[status(thm)],[c_0_60, c_0_21])).
% 55.17/55.37  cnf(c_0_68, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,X3)|~r1_tarski(X2,X3)|~r1_xboole_0(X1,X3)), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 55.17/55.37  cnf(c_0_69, negated_conjecture, (r1_xboole_0(k5_xboole_0(esk4_0,esk4_0),esk4_0)), inference(spm,[status(thm)],[c_0_63, c_0_64])).
% 55.17/55.37  cnf(c_0_70, negated_conjecture, (r1_tarski(esk3_0,esk2_0)), inference(spm,[status(thm)],[c_0_36, c_0_65])).
% 55.17/55.37  fof(c_0_71, plain, ![X21, X22]:k2_xboole_0(X21,k4_xboole_0(X22,X21))=k2_xboole_0(X21,X22), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 55.17/55.37  cnf(c_0_72, plain, (k2_xboole_0(X1,X2)=X1|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_62, c_0_66])).
% 55.17/55.37  cnf(c_0_73, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k3_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_67, c_0_28])).
% 55.17/55.37  cnf(c_0_74, negated_conjecture, (r1_tarski(k5_xboole_0(esk4_0,esk4_0),X1)|~r1_tarski(X1,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_49]), c_0_69])])).
% 55.17/55.37  cnf(c_0_75, negated_conjecture, (r1_tarski(esk3_0,esk3_0)), inference(spm,[status(thm)],[c_0_38, c_0_70])).
% 55.17/55.37  cnf(c_0_76, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_71])).
% 55.17/55.37  cnf(c_0_77, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_62, c_0_72])).
% 55.17/55.37  cnf(c_0_78, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k3_xboole_0(X3,X2))), inference(spm,[status(thm)],[c_0_73, c_0_43])).
% 55.17/55.37  cnf(c_0_79, negated_conjecture, (r1_tarski(k5_xboole_0(esk4_0,esk4_0),k3_xboole_0(esk4_0,X1))), inference(spm,[status(thm)],[c_0_74, c_0_34])).
% 55.17/55.37  cnf(c_0_80, negated_conjecture, (r1_tarski(k5_xboole_0(k5_xboole_0(esk4_0,esk4_0),k5_xboole_0(esk4_0,esk4_0)),k5_xboole_0(esk4_0,esk4_0))), inference(spm,[status(thm)],[c_0_44, c_0_49])).
% 55.17/55.37  cnf(c_0_81, negated_conjecture, (k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,k5_xboole_0(esk3_0,esk3_0)))=esk3_0), inference(spm,[status(thm)],[c_0_41, c_0_75])).
% 55.17/55.37  cnf(c_0_82, negated_conjecture, (r1_tarski(k5_xboole_0(esk3_0,esk3_0),esk3_0)), inference(spm,[status(thm)],[c_0_44, c_0_70])).
% 55.17/55.37  cnf(c_0_83, plain, (k2_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_76, c_0_21])).
% 55.17/55.37  cnf(c_0_84, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,k3_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_77, c_0_34])).
% 55.17/55.37  cnf(c_0_85, negated_conjecture, (r1_tarski(k5_xboole_0(esk4_0,esk4_0),X1)), inference(spm,[status(thm)],[c_0_78, c_0_79])).
% 55.17/55.37  cnf(c_0_86, negated_conjecture, (k5_xboole_0(k5_xboole_0(esk4_0,esk4_0),k5_xboole_0(esk4_0,esk4_0))=k5_xboole_0(esk4_0,esk4_0)|~r1_tarski(k5_xboole_0(esk4_0,esk4_0),k5_xboole_0(k5_xboole_0(esk4_0,esk4_0),k5_xboole_0(esk4_0,esk4_0)))), inference(spm,[status(thm)],[c_0_77, c_0_80])).
% 55.17/55.37  cnf(c_0_87, negated_conjecture, (k3_xboole_0(esk3_0,k5_xboole_0(esk3_0,esk3_0))=k5_xboole_0(esk3_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_81]), c_0_75])])).
% 55.17/55.37  cnf(c_0_88, negated_conjecture, (k5_xboole_0(esk3_0,k5_xboole_0(esk3_0,esk3_0))=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_48]), c_0_82])])).
% 55.17/55.37  cnf(c_0_89, plain, (k2_xboole_0(X1,X2)=X1|~r1_tarski(k5_xboole_0(X2,k3_xboole_0(X2,X1)),X1)), inference(spm,[status(thm)],[c_0_72, c_0_83])).
% 55.17/55.37  cnf(c_0_90, negated_conjecture, (k3_xboole_0(k5_xboole_0(esk4_0,esk4_0),X1)=k5_xboole_0(esk4_0,esk4_0)), inference(spm,[status(thm)],[c_0_84, c_0_85])).
% 55.17/55.37  cnf(c_0_91, negated_conjecture, (k5_xboole_0(k5_xboole_0(esk4_0,esk4_0),k5_xboole_0(esk4_0,esk4_0))=k5_xboole_0(esk4_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_86, c_0_85])])).
% 55.17/55.37  cnf(c_0_92, negated_conjecture, (k3_xboole_0(esk3_0,esk3_0)=esk3_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_87]), c_0_87]), c_0_88]), c_0_88])).
% 55.17/55.37  cnf(c_0_93, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k2_xboole_0(X3,X2))|~r1_xboole_0(X1,X3)), inference(spm,[status(thm)],[c_0_61, c_0_66])).
% 55.17/55.37  cnf(c_0_94, negated_conjecture, (k2_xboole_0(X1,k5_xboole_0(esk4_0,esk4_0))=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_90]), c_0_91]), c_0_85])])).
% 55.17/55.37  cnf(c_0_95, negated_conjecture, (r1_xboole_0(X1,esk3_0)|~r1_tarski(X1,k5_xboole_0(esk3_0,esk3_0))), inference(spm,[status(thm)],[c_0_56, c_0_92])).
% 55.17/55.37  cnf(c_0_96, negated_conjecture, (r1_tarski(k5_xboole_0(esk3_0,esk3_0),k5_xboole_0(esk3_0,esk3_0))), inference(spm,[status(thm)],[c_0_38, c_0_82])).
% 55.17/55.37  fof(c_0_97, plain, ![X37, X38]:(~m1_subset_1(X38,k1_zfmisc_1(X37))|k3_subset_1(X37,X38)=k4_xboole_0(X37,X38)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 55.17/55.37  cnf(c_0_98, plain, (r2_hidden(X1,X3)|~r1_tarski(X1,X2)|X3!=k1_zfmisc_1(X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 55.17/55.37  cnf(c_0_99, negated_conjecture, (r1_tarski(X1,k5_xboole_0(esk4_0,esk4_0))|~r1_tarski(X1,X2)|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_93, c_0_94])).
% 55.17/55.37  cnf(c_0_100, negated_conjecture, (r1_xboole_0(k5_xboole_0(esk3_0,esk3_0),esk3_0)), inference(spm,[status(thm)],[c_0_95, c_0_96])).
% 55.17/55.37  cnf(c_0_101, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_97])).
% 55.17/55.37  cnf(c_0_102, plain, (m1_subset_1(X1,X2)|v1_xboole_0(X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 55.17/55.37  cnf(c_0_103, plain, (r2_hidden(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(er,[status(thm)],[c_0_98])).
% 55.17/55.37  cnf(c_0_104, negated_conjecture, (r1_tarski(k5_xboole_0(esk3_0,esk3_0),k5_xboole_0(esk4_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_82]), c_0_100])])).
% 55.17/55.37  cnf(c_0_105, plain, (k2_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2)))=k2_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_83, c_0_43])).
% 55.17/55.37  cnf(c_0_106, negated_conjecture, (k2_xboole_0(k5_xboole_0(esk4_0,esk4_0),X1)=X1), inference(spm,[status(thm)],[c_0_66, c_0_94])).
% 55.17/55.37  cnf(c_0_107, plain, (r1_tarski(k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k3_xboole_0(X1,X2),X3)),X1)), inference(spm,[status(thm)],[c_0_73, c_0_27])).
% 55.17/55.37  cnf(c_0_108, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,X3)|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_78, c_0_35])).
% 55.17/55.37  fof(c_0_109, plain, ![X8, X9]:(~r1_xboole_0(X8,X9)|r1_xboole_0(X9,X8)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 55.17/55.37  cnf(c_0_110, plain, (k3_subset_1(X2,X1)=k5_xboole_0(X2,k3_xboole_0(X2,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_101, c_0_21])).
% 55.17/55.37  cnf(c_0_111, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_102, c_0_103]), c_0_33])).
% 55.17/55.37  cnf(c_0_112, negated_conjecture, (k5_xboole_0(esk4_0,esk4_0)=k5_xboole_0(esk3_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_104]), c_0_85])])).
% 55.17/55.37  cnf(c_0_113, negated_conjecture, (k5_xboole_0(X1,k5_xboole_0(esk4_0,esk4_0))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105, c_0_106]), c_0_90]), c_0_106])).
% 55.17/55.37  cnf(c_0_114, plain, (k2_xboole_0(X1,k3_xboole_0(X1,X2))=X1), inference(spm,[status(thm)],[c_0_89, c_0_107])).
% 55.17/55.37  cnf(c_0_115, plain, (r1_tarski(k3_xboole_0(X1,X2),X3)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_108, c_0_34])).
% 55.17/55.37  cnf(c_0_116, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_109])).
% 55.17/55.37  cnf(c_0_117, plain, (r1_xboole_0(k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3)),X2)), inference(spm,[status(thm)],[c_0_56, c_0_27])).
% 55.17/55.37  cnf(c_0_118, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,X2)))=X2|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_28, c_0_48])).
% 55.17/55.37  cnf(c_0_119, plain, (k5_xboole_0(X1,X2)=k3_subset_1(X1,X2)|~r1_tarski(X2,X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_110, c_0_48]), c_0_111])).
% 55.17/55.37  cnf(c_0_120, plain, (r1_tarski(k5_xboole_0(X1,k3_xboole_0(X2,X1)),X1)), inference(spm,[status(thm)],[c_0_27, c_0_43])).
% 55.17/55.37  cnf(c_0_121, negated_conjecture, (k3_xboole_0(k5_xboole_0(esk3_0,esk3_0),X1)=k5_xboole_0(esk3_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_90, c_0_112]), c_0_112])).
% 55.17/55.37  cnf(c_0_122, negated_conjecture, (k5_xboole_0(X1,k5_xboole_0(esk3_0,esk3_0))=X1), inference(rw,[status(thm)],[c_0_113, c_0_112])).
% 55.17/55.37  cnf(c_0_123, plain, (k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_51]), c_0_66]), c_0_114])).
% 55.17/55.37  cnf(c_0_124, plain, (k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_48]), c_0_34])])).
% 55.17/55.37  cnf(c_0_125, plain, (k2_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,k3_xboole_0(X1,X2)))=k2_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_28]), c_0_66]), c_0_66])).
% 55.17/55.37  cnf(c_0_126, plain, (r1_tarski(k3_xboole_0(X1,X2),X3)|~r1_tarski(X1,k3_xboole_0(X3,X4))), inference(spm,[status(thm)],[c_0_73, c_0_115])).
% 55.17/55.37  cnf(c_0_127, negated_conjecture, (r1_tarski(esk4_0,X1)|~r1_tarski(esk2_0,X1)), inference(spm,[status(thm)],[c_0_108, c_0_39])).
% 55.17/55.37  cnf(c_0_128, plain, (r1_xboole_0(X1,k5_xboole_0(k5_xboole_0(X2,k3_xboole_0(X2,X1)),k3_xboole_0(k5_xboole_0(X2,k3_xboole_0(X2,X1)),X3)))), inference(spm,[status(thm)],[c_0_116, c_0_117])).
% 55.17/55.37  cnf(c_0_129, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k3_subset_1(X1,X2)))=X2|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_118, c_0_119])).
% 55.17/55.37  cnf(c_0_130, negated_conjecture, (r1_tarski(X1,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120, c_0_121]), c_0_122])).
% 55.17/55.37  cnf(c_0_131, plain, (k2_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_123, c_0_124]), c_0_125])).
% 55.17/55.37  cnf(c_0_132, negated_conjecture, (r1_tarski(k3_xboole_0(esk4_0,X1),X2)|~r1_tarski(esk2_0,k3_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_126, c_0_127])).
% 55.17/55.37  cnf(c_0_133, plain, (r1_xboole_0(X1,X2)|~r1_tarski(X2,k5_xboole_0(X3,k3_xboole_0(X3,X1)))), inference(spm,[status(thm)],[c_0_128, c_0_129])).
% 55.17/55.37  cnf(c_0_134, negated_conjecture, (r1_tarski(k2_xboole_0(X1,X2),X2)|~r1_xboole_0(k2_xboole_0(X1,X2),X1)), inference(spm,[status(thm)],[c_0_93, c_0_130])).
% 55.17/55.37  cnf(c_0_135, plain, (k2_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,k3_xboole_0(X1,X2)))=X1), inference(rw,[status(thm)],[c_0_125, c_0_131])).
% 55.17/55.37  cnf(c_0_136, negated_conjecture, (r1_tarski(k3_xboole_0(esk4_0,X1),X2)|~r1_tarski(esk2_0,X2)|~r1_tarski(X2,X3)), inference(spm,[status(thm)],[c_0_132, c_0_35])).
% 55.17/55.37  cnf(c_0_137, negated_conjecture, (r1_xboole_0(X1,esk4_0)|~r1_tarski(esk2_0,k5_xboole_0(X2,k3_xboole_0(X2,X1)))), inference(spm,[status(thm)],[c_0_133, c_0_127])).
% 55.17/55.37  cnf(c_0_138, negated_conjecture, (r1_tarski(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))|~r1_xboole_0(X1,k3_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_134, c_0_135])).
% 55.17/55.37  cnf(c_0_139, plain, (r1_xboole_0(k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3),X2)), inference(spm,[status(thm)],[c_0_56, c_0_34])).
% 55.17/55.37  cnf(c_0_140, negated_conjecture, (r1_tarski(k3_xboole_0(esk4_0,X1),esk2_0)|~r1_tarski(esk2_0,X2)), inference(spm,[status(thm)],[c_0_136, c_0_130])).
% 55.17/55.37  cnf(c_0_141, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k3_subset_1(X2,k3_xboole_0(X2,X3)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_119]), c_0_34])])).
% 55.17/55.37  cnf(c_0_142, negated_conjecture, (r1_tarski(k2_xboole_0(X1,X2),X1)|~r1_xboole_0(k2_xboole_0(X1,X2),X2)), inference(spm,[status(thm)],[c_0_61, c_0_130])).
% 55.17/55.37  cnf(c_0_143, plain, (k2_xboole_0(X1,k5_xboole_0(X2,X1))=k2_xboole_0(X1,X2)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_83, c_0_48])).
% 55.17/55.37  cnf(c_0_144, negated_conjecture, (r1_xboole_0(X1,esk4_0)|~r1_xboole_0(esk2_0,k3_xboole_0(esk2_0,X1))), inference(spm,[status(thm)],[c_0_137, c_0_138])).
% 55.17/55.37  cnf(c_0_145, plain, (r1_xboole_0(X1,k3_xboole_0(k5_xboole_0(X2,k3_xboole_0(X2,X1)),X3))), inference(spm,[status(thm)],[c_0_116, c_0_139])).
% 55.17/55.37  cnf(c_0_146, plain, (r1_xboole_0(X1,X2)|~r1_tarski(X1,k3_subset_1(X3,k3_xboole_0(X3,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_119]), c_0_34])])).
% 55.17/55.37  cnf(c_0_147, negated_conjecture, (r1_tarski(k3_xboole_0(esk4_0,X1),esk2_0)), inference(spm,[status(thm)],[c_0_140, c_0_130])).
% 55.17/55.37  cnf(c_0_148, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k3_subset_1(X2,X3))|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_141, c_0_48])).
% 55.17/55.37  cnf(c_0_149, negated_conjecture, (r1_tarski(k2_xboole_0(X1,X2),X1)|~r1_tarski(X1,X2)|~r1_xboole_0(k2_xboole_0(X1,X2),k5_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_142, c_0_143])).
% 55.17/55.37  cnf(c_0_150, negated_conjecture, (r1_xboole_0(X1,esk4_0)|~r1_xboole_0(esk2_0,k3_xboole_0(X1,esk2_0))), inference(spm,[status(thm)],[c_0_144, c_0_43])).
% 55.17/55.37  cnf(c_0_151, plain, (r1_xboole_0(X1,k3_xboole_0(k3_subset_1(X2,k3_xboole_0(X2,X1)),X3))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_145, c_0_119]), c_0_34])])).
% 55.17/55.37  cnf(c_0_152, plain, (r1_xboole_0(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~r1_tarski(X1,k3_subset_1(X3,X2))), inference(spm,[status(thm)],[c_0_56, c_0_110])).
% 55.17/55.37  cnf(c_0_153, negated_conjecture, (r1_tarski(esk3_0,esk4_0)|r1_tarski(k3_subset_1(esk2_0,esk4_0),k3_subset_1(esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 55.17/55.37  cnf(c_0_154, plain, (r1_tarski(k5_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(k2_xboole_0(X1,X2),X3)),X1)|~r1_xboole_0(k5_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(k2_xboole_0(X1,X2),X3)),X2)), inference(spm,[status(thm)],[c_0_61, c_0_27])).
% 55.17/55.37  cnf(c_0_155, plain, (r1_xboole_0(X1,X2)|~r1_tarski(X1,k3_subset_1(X3,X2))|~r1_tarski(X2,X3)), inference(spm,[status(thm)],[c_0_146, c_0_48])).
% 55.17/55.37  cnf(c_0_156, negated_conjecture, (r1_tarski(X1,esk2_0)|~r1_tarski(X1,esk4_0)), inference(spm,[status(thm)],[c_0_147, c_0_48])).
% 55.17/55.37  cnf(c_0_157, negated_conjecture, (r1_tarski(k3_subset_1(X1,X2),X1)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_148, c_0_130])).
% 55.17/55.37  cnf(c_0_158, negated_conjecture, (r1_tarski(X1,X2)|~r1_tarski(X2,X1)|~r1_xboole_0(X1,k5_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_149, c_0_62])).
% 55.17/55.37  cnf(c_0_159, negated_conjecture, (r1_xboole_0(k3_subset_1(X1,k3_xboole_0(X1,esk2_0)),esk4_0)), inference(spm,[status(thm)],[c_0_150, c_0_151])).
% 55.17/55.37  cnf(c_0_160, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k2_xboole_0(X2,X3))|~r1_xboole_0(X1,k5_xboole_0(X3,k3_xboole_0(X3,X2)))), inference(spm,[status(thm)],[c_0_61, c_0_83])).
% 55.17/55.37  cnf(c_0_161, negated_conjecture, (r1_tarski(esk3_0,esk4_0)|r1_xboole_0(k3_subset_1(esk2_0,esk4_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_152, c_0_153]), c_0_58])])).
% 55.17/55.37  cnf(c_0_162, plain, (k2_xboole_0(X1,k3_subset_1(X2,X1))=k2_xboole_0(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_83, c_0_110])).
% 55.17/55.37  cnf(c_0_163, plain, (r1_tarski(k3_subset_1(k2_xboole_0(X1,X2),X3),X1)|~m1_subset_1(X3,k1_zfmisc_1(k2_xboole_0(X1,X2)))|~r1_xboole_0(k3_subset_1(k2_xboole_0(X1,X2),X3),X2)), inference(spm,[status(thm)],[c_0_154, c_0_110])).
% 55.17/55.37  cnf(c_0_164, negated_conjecture, (r1_xboole_0(k3_subset_1(X1,X2),X2)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_155, c_0_130])).
% 55.17/55.37  cnf(c_0_165, plain, (k2_xboole_0(X1,X2)=X1|~r1_tarski(k3_subset_1(X2,k3_xboole_0(X2,X1)),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_119]), c_0_34])])).
% 55.17/55.37  cnf(c_0_166, negated_conjecture, (r1_tarski(k3_subset_1(esk4_0,X1),esk2_0)|~r1_tarski(X1,esk4_0)), inference(spm,[status(thm)],[c_0_156, c_0_157])).
% 55.17/55.37  cnf(c_0_167, plain, (r1_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))|~r1_tarski(X1,k3_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_56, c_0_28])).
% 55.17/55.37  cnf(c_0_168, negated_conjecture, (r1_tarski(X1,X2)|~r1_tarski(X2,X1)|~r1_xboole_0(X1,k3_subset_1(X1,X2))), inference(spm,[status(thm)],[c_0_158, c_0_119])).
% 55.17/55.37  cnf(c_0_169, negated_conjecture, (r1_xboole_0(esk4_0,k3_subset_1(X1,k3_xboole_0(X1,esk2_0)))), inference(spm,[status(thm)],[c_0_116, c_0_159])).
% 55.17/55.37  cnf(c_0_170, plain, (r1_tarski(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~r1_tarski(X1,k2_xboole_0(X2,X3))|~r1_xboole_0(X1,k3_subset_1(X3,X2))), inference(spm,[status(thm)],[c_0_160, c_0_110])).
% 55.17/55.37  cnf(c_0_171, negated_conjecture, (r1_tarski(esk3_0,esk4_0)|r1_xboole_0(esk3_0,k3_subset_1(esk2_0,esk4_0))), inference(spm,[status(thm)],[c_0_116, c_0_161])).
% 55.17/55.37  cnf(c_0_172, plain, (r1_tarski(X1,k3_subset_1(X2,X3))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_tarski(X1,k2_xboole_0(X3,X2))|~r1_xboole_0(X1,X3)), inference(spm,[status(thm)],[c_0_93, c_0_162])).
% 55.17/55.37  cnf(c_0_173, negated_conjecture, (r1_tarski(k3_subset_1(k2_xboole_0(X1,X2),X2),X1)|~r1_tarski(X2,k2_xboole_0(X1,X2))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_163, c_0_164]), c_0_111])).
% 55.17/55.37  cnf(c_0_174, negated_conjecture, (k2_xboole_0(esk2_0,esk4_0)=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_165, c_0_166]), c_0_34])])).
% 55.17/55.37  cnf(c_0_175, plain, (r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3)|~r1_tarski(X3,k3_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_116, c_0_167])).
% 55.17/55.37  cnf(c_0_176, negated_conjecture, (r1_tarski(esk4_0,k3_xboole_0(esk2_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_168, c_0_169]), c_0_43]), c_0_34])])).
% 55.17/55.37  cnf(c_0_177, plain, (r1_tarski(k3_xboole_0(X1,X2),X2)), inference(spm,[status(thm)],[c_0_34, c_0_43])).
% 55.17/55.37  cnf(c_0_178, negated_conjecture, (r1_tarski(esk3_0,esk4_0)|~r1_tarski(esk3_0,k2_xboole_0(esk2_0,esk4_0))), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_170, c_0_171]), c_0_32])]), c_0_66])).
% 55.17/55.37  cnf(c_0_179, plain, (r1_tarski(X1,k3_subset_1(X2,X3))|~r1_tarski(X1,X2)|~r1_tarski(X3,X2)|~r1_xboole_0(X1,X3)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_172, c_0_62]), c_0_111])).
% 55.17/55.37  cnf(c_0_180, negated_conjecture, (r1_tarski(k3_subset_1(esk2_0,esk4_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_173, c_0_174]), c_0_39])])).
% 55.17/55.37  cnf(c_0_181, plain, (r1_xboole_0(k3_subset_1(X1,k3_xboole_0(X1,X2)),X3)|~r1_tarski(X3,k3_xboole_0(X1,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_175, c_0_119]), c_0_34])])).
% 55.17/55.37  cnf(c_0_182, negated_conjecture, (k3_xboole_0(esk2_0,esk4_0)=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_176]), c_0_177])])).
% 55.17/55.37  cnf(c_0_183, negated_conjecture, (~r1_tarski(esk3_0,esk4_0)|~r1_tarski(k3_subset_1(esk2_0,esk4_0),k3_subset_1(esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 55.17/55.37  cnf(c_0_184, negated_conjecture, (r1_tarski(esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_178, c_0_72]), c_0_70]), c_0_39])])).
% 55.17/55.37  cnf(c_0_185, negated_conjecture, (r1_tarski(k3_subset_1(esk2_0,esk4_0),k3_subset_1(esk2_0,X1))|~r1_tarski(X1,esk2_0)|~r1_xboole_0(k3_subset_1(esk2_0,esk4_0),X1)), inference(spm,[status(thm)],[c_0_179, c_0_180])).
% 55.17/55.37  cnf(c_0_186, negated_conjecture, (r1_xboole_0(k3_subset_1(esk2_0,esk4_0),X1)|~r1_tarski(X1,esk4_0)), inference(spm,[status(thm)],[c_0_181, c_0_182])).
% 55.17/55.37  cnf(c_0_187, negated_conjecture, (~r1_tarski(k3_subset_1(esk2_0,esk4_0),k3_subset_1(esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_183, c_0_184])])).
% 55.17/55.37  cnf(c_0_188, plain, ($false), inference(cdclpropres,[status(thm)],[c_0_185, c_0_186, c_0_187, c_0_184, c_0_70]), ['proof']).
% 55.17/55.37  # SZS output end CNFRefutation
% 55.17/55.37  # Proof object total steps             : 189
% 55.17/55.37  # Proof object clause steps            : 156
% 55.17/55.37  # Proof object formula steps           : 33
% 55.17/55.37  # Proof object conjectures             : 77
% 55.17/55.37  # Proof object clause conjectures      : 74
% 55.17/55.37  # Proof object formula conjectures     : 3
% 55.17/55.37  # Proof object initial clauses used    : 22
% 55.17/55.37  # Proof object initial formulas used   : 16
% 55.17/55.37  # Proof object generating inferences   : 119
% 55.17/55.37  # Proof object simplifying inferences  : 84
% 55.17/55.37  # Training examples: 0 positive, 0 negative
% 55.17/55.37  # Parsed axioms                        : 16
% 55.17/55.37  # Removed by relevancy pruning/SinE    : 0
% 55.17/55.37  # Initial clauses                      : 26
% 55.17/55.37  # Removed in clause preprocessing      : 1
% 55.17/55.37  # Initial clauses in saturation        : 25
% 55.17/55.37  # Processed clauses                    : 115044
% 55.17/55.37  # ...of these trivial                  : 1685
% 55.17/55.37  # ...subsumed                          : 103359
% 55.17/55.37  # ...remaining for further processing  : 10000
% 55.17/55.37  # Other redundant clauses eliminated   : 2
% 55.17/55.37  # Clauses deleted for lack of memory   : 303299
% 55.17/55.37  # Backward-subsumed                    : 1342
% 55.17/55.37  # Backward-rewritten                   : 1047
% 55.17/55.37  # Generated clauses                    : 4219880
% 55.17/55.37  # ...of the previous two non-trivial   : 3846516
% 55.17/55.37  # Contextual simplify-reflections      : 218
% 55.17/55.37  # Paramodulations                      : 4219112
% 55.17/55.37  # Factorizations                       : 766
% 55.17/55.37  # Equation resolutions                 : 2
% 55.17/55.37  # Propositional unsat checks           : 2
% 55.17/55.37  #    Propositional check models        : 0
% 55.17/55.37  #    Propositional check unsatisfiable : 1
% 55.17/55.37  #    Propositional clauses             : 1567664
% 55.17/55.37  #    Propositional clauses after purity: 333781
% 55.17/55.37  #    Propositional unsat core size     : 5
% 55.17/55.37  #    Propositional preprocessing time  : 0.000
% 55.17/55.37  #    Propositional encoding time       : 3.698
% 55.17/55.37  #    Propositional solver time         : 0.510
% 55.17/55.37  #    Success case prop preproc time    : 0.000
% 55.17/55.37  #    Success case prop encoding time   : 2.942
% 55.17/55.37  #    Success case prop solver time     : 0.278
% 55.17/55.37  # Current number of processed clauses  : 7584
% 55.17/55.37  #    Positive orientable unit clauses  : 667
% 55.17/55.37  #    Positive unorientable unit clauses: 4
% 55.17/55.37  #    Negative unit clauses             : 220
% 55.17/55.37  #    Non-unit-clauses                  : 6693
% 55.17/55.37  # Current number of unprocessed clauses: 1560080
% 55.17/55.37  # ...number of literals in the above   : 5981611
% 55.17/55.37  # Current number of archived formulas  : 0
% 55.17/55.37  # Current number of archived clauses   : 2415
% 55.17/55.37  # Clause-clause subsumption calls (NU) : 6711968
% 55.17/55.37  # Rec. Clause-clause subsumption calls : 4399273
% 55.17/55.37  # Non-unit clause-clause subsumptions  : 57121
% 55.17/55.37  # Unit Clause-clause subsumption calls : 300980
% 55.17/55.37  # Rewrite failures with RHS unbound    : 150
% 55.17/55.37  # BW rewrite match attempts            : 28739
% 55.17/55.37  # BW rewrite match successes           : 205
% 55.17/55.37  # Condensation attempts                : 0
% 55.17/55.37  # Condensation successes               : 0
% 55.17/55.37  # Termbank termtop insertions          : 175692399
% 55.24/55.46  
% 55.24/55.46  # -------------------------------------------------
% 55.24/55.46  # User time                : 53.842 s
% 55.24/55.46  # System time              : 1.264 s
% 55.24/55.46  # Total time               : 55.107 s
% 55.24/55.46  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
