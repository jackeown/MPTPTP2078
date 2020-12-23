%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:08:58 EST 2020

% Result     : CounterSatisfiable 0.14s
% Output     : Saturation 0.14s
% Verified   : 
% Statistics : Number of formulae       :  112 (1546 expanded)
%              Number of clauses        :   85 ( 695 expanded)
%              Number of leaves         :   13 ( 408 expanded)
%              Depth                    :   11
%              Number of atoms          :  261 (2592 expanded)
%              Number of equality atoms :  102 (1586 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t88_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => k4_xboole_0(k2_xboole_0(X1,X2),X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_xboole_1)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t21_xboole_1,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,k2_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(redefinition_k7_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k7_subset_1(X1,X2,X3) = k4_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(redefinition_k4_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => k4_subset_1(X1,X2,X3) = k2_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(t25_pre_topc,conjecture,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( ( k2_struct_0(X1) = k4_subset_1(u1_struct_0(X1),X2,X3)
                  & r1_xboole_0(X2,X3) )
               => X3 = k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_pre_topc)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(dt_k2_subset_1,axiom,(
    ! [X1] : m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(c_0_13,plain,(
    ! [X10,X11] : k4_xboole_0(X10,X11) = k5_xboole_0(X10,k3_xboole_0(X10,X11)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_14,plain,(
    ! [X26,X27] : k1_setfam_1(k2_tarski(X26,X27)) = k3_xboole_0(X26,X27) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_15,plain,(
    ! [X14,X15] :
      ( ~ r1_xboole_0(X14,X15)
      | k4_xboole_0(k2_xboole_0(X14,X15),X15) = X14 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t88_xboole_1])])).

fof(c_0_16,plain,(
    ! [X16,X17] : k3_tarski(k2_tarski(X16,X17)) = k2_xboole_0(X16,X17) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

cnf(c_0_17,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_19,plain,(
    ! [X6,X7] : k3_xboole_0(X6,X7) = k3_xboole_0(X7,X6) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_20,plain,(
    ! [X12,X13] : k3_xboole_0(X12,k2_xboole_0(X12,X13)) = X12 ),
    inference(variable_rename,[status(thm)],[t21_xboole_1])).

fof(c_0_21,plain,(
    ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_22,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X2) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_25,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_28,plain,(
    ! [X23,X24,X25] :
      ( ~ m1_subset_1(X24,k1_zfmisc_1(X23))
      | k7_subset_1(X23,X24,X25) = k4_xboole_0(X24,X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).

cnf(c_0_29,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k1_setfam_1(k2_tarski(k3_tarski(k2_tarski(X1,X2)),X2))) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22,c_0_23]),c_0_24])).

cnf(c_0_30,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k1_setfam_1(k2_tarski(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_18]),c_0_18]),
    [final]).

cnf(c_0_31,plain,
    ( k1_setfam_1(k2_tarski(X1,k3_tarski(k2_tarski(X1,X2)))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_23]),c_0_18]),
    [final]).

cnf(c_0_32,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k3_tarski(k2_tarski(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_23]),c_0_23]),
    [final]).

cnf(c_0_33,plain,
    ( k7_subset_1(X2,X1,X3) = k4_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_34,plain,(
    ! [X20,X21,X22] :
      ( ~ m1_subset_1(X21,k1_zfmisc_1(X20))
      | ~ m1_subset_1(X22,k1_zfmisc_1(X20))
      | k4_subset_1(X20,X21,X22) = k2_xboole_0(X21,X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).

cnf(c_0_35,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k1_setfam_1(k2_tarski(X2,k3_tarski(k2_tarski(X1,X2))))) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_36,plain,
    ( k1_setfam_1(k2_tarski(X1,k3_tarski(k2_tarski(X2,X1)))) = X1 ),
    inference(spm,[status(thm)],[c_0_31,c_0_32]),
    [final]).

cnf(c_0_37,plain,
    ( k7_subset_1(X2,X1,X3) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_33,c_0_24]),
    [final]).

cnf(c_0_38,plain,
    ( k4_subset_1(X2,X1,X3) = k2_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

fof(c_0_39,negated_conjecture,(
    ~ ! [X1] :
        ( l1_struct_0(X1)
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ( ( k2_struct_0(X1) = k4_subset_1(u1_struct_0(X1),X2,X3)
                    & r1_xboole_0(X2,X3) )
                 => X3 = k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t25_pre_topc])).

cnf(c_0_40,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_35,c_0_36]),
    [final]).

cnf(c_0_41,plain,
    ( k7_subset_1(X1,X2,X3) = k5_xboole_0(X2,k1_setfam_1(k2_tarski(X3,X2)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_30]),
    [final]).

cnf(c_0_42,plain,
    ( k4_subset_1(X2,X1,X3) = k3_tarski(k2_tarski(X1,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_38,c_0_23]),
    [final]).

fof(c_0_43,negated_conjecture,
    ( l1_struct_0(esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & k2_struct_0(esk1_0) = k4_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0)
    & r1_xboole_0(esk2_0,esk3_0)
    & esk3_0 != k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_39])])])).

cnf(c_0_44,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1) = X2
    | ~ r1_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_32]),
    [final]).

cnf(c_0_45,plain,
    ( k7_subset_1(X1,k3_tarski(k2_tarski(X2,X3)),X2) = k5_xboole_0(k3_tarski(k2_tarski(X2,X3)),X2)
    | ~ m1_subset_1(k3_tarski(k2_tarski(X2,X3)),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_31]),
    [final]).

cnf(c_0_46,plain,
    ( k1_setfam_1(k2_tarski(X1,k4_subset_1(X2,X1,X3))) = X1
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_42]),
    [final]).

cnf(c_0_47,negated_conjecture,
    ( k2_struct_0(esk1_0) = k4_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_43]),
    [final]).

cnf(c_0_48,plain,
    ( k4_subset_1(X1,X2,X3) = k4_subset_1(X4,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X4))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X4)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_42]),
    [final]).

cnf(c_0_49,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_43]),
    [final]).

cnf(c_0_50,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_43]),
    [final]).

fof(c_0_51,plain,(
    ! [X8,X9] :
      ( ~ r1_xboole_0(X8,X9)
      | r1_xboole_0(X9,X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

cnf(c_0_52,plain,
    ( k1_setfam_1(k2_tarski(X1,k4_subset_1(X2,X3,X1))) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_42]),
    [final]).

fof(c_0_53,plain,(
    ! [X19] : m1_subset_1(k2_subset_1(X19),k1_zfmisc_1(X19)) ),
    inference(variable_rename,[status(thm)],[dt_k2_subset_1])).

fof(c_0_54,plain,(
    ! [X18] : k2_subset_1(X18) = X18 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

cnf(c_0_55,plain,
    ( k7_subset_1(X1,k3_tarski(k2_tarski(X2,X3)),X2) = X3
    | ~ m1_subset_1(k3_tarski(k2_tarski(X2,X3)),k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X3,X2) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45]),
    [final]).

cnf(c_0_56,plain,
    ( k4_subset_1(X1,X2,X3) = k3_tarski(k2_tarski(X3,X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_42]),
    [final]).

cnf(c_0_57,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X3),X3) = X2
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X2,X3) ),
    inference(spm,[status(thm)],[c_0_40,c_0_42]),
    [final]).

cnf(c_0_58,plain,
    ( k7_subset_1(X1,k4_subset_1(X2,X3,X4),X3) = k5_xboole_0(k4_subset_1(X2,X3,X4),X3)
    | ~ m1_subset_1(k4_subset_1(X2,X3,X4),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_46]),
    [final]).

cnf(c_0_59,plain,
    ( k7_subset_1(X1,X2,k3_tarski(k2_tarski(X3,X2))) = k5_xboole_0(X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_36]),
    [final]).

cnf(c_0_60,plain,
    ( k7_subset_1(X1,X2,k3_tarski(k2_tarski(X2,X3))) = k5_xboole_0(X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_31]),
    [final]).

cnf(c_0_61,negated_conjecture,
    ( k4_subset_1(X1,esk2_0,esk3_0) = k2_struct_0(esk1_0)
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_49]),c_0_50])]),
    [final]).

cnf(c_0_62,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_51]),
    [final]).

cnf(c_0_63,negated_conjecture,
    ( r1_xboole_0(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_43]),
    [final]).

cnf(c_0_64,negated_conjecture,
    ( k1_setfam_1(k2_tarski(esk2_0,k2_struct_0(esk1_0))) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_49]),c_0_50])]),
    [final]).

cnf(c_0_65,plain,
    ( k7_subset_1(X1,k4_subset_1(X2,X3,X4),X4) = k5_xboole_0(k4_subset_1(X2,X3,X4),X4)
    | ~ m1_subset_1(k4_subset_1(X2,X3,X4),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_52]),
    [final]).

cnf(c_0_66,plain,
    ( m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_67,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_68,plain,
    ( k7_subset_1(X1,k4_subset_1(X2,X3,X4),X4) = X3
    | ~ m1_subset_1(k4_subset_1(X2,X3,X4),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(X3,X4) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56]),
    [final]).

cnf(c_0_69,plain,
    ( k7_subset_1(X1,k4_subset_1(X2,X3,X4),X3) = X4
    | ~ m1_subset_1(k4_subset_1(X2,X3,X4),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(X4,X3) ),
    inference(spm,[status(thm)],[c_0_55,c_0_42]),
    [final]).

cnf(c_0_70,plain,
    ( k7_subset_1(X1,k4_subset_1(X2,X3,X3),X3) = X3
    | ~ m1_subset_1(k4_subset_1(X2,X3,X3),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(X3,X3) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58]),
    [final]).

cnf(c_0_71,plain,
    ( k7_subset_1(X1,X2,k4_subset_1(X3,X4,X2)) = k5_xboole_0(X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_42]),
    [final]).

cnf(c_0_72,plain,
    ( k7_subset_1(X1,X2,k4_subset_1(X3,X2,X4)) = k5_xboole_0(X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_42]),
    [final]).

cnf(c_0_73,negated_conjecture,
    ( k3_tarski(k2_tarski(esk2_0,esk3_0)) = k2_struct_0(esk1_0)
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_61])).

cnf(c_0_74,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X3),X2) = X3
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X3,X2) ),
    inference(spm,[status(thm)],[c_0_44,c_0_42]),
    [final]).

cnf(c_0_75,negated_conjecture,
    ( r1_xboole_0(esk3_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63]),
    [final]).

cnf(c_0_76,negated_conjecture,
    ( esk3_0 != k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_43]),
    [final]).

cnf(c_0_77,negated_conjecture,
    ( k7_subset_1(X1,k2_struct_0(esk1_0),esk2_0) = k5_xboole_0(k2_struct_0(esk1_0),esk2_0)
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_64])).

cnf(c_0_78,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X3),k1_setfam_1(k2_tarski(X3,k4_subset_1(X1,X2,X3)))) = k5_xboole_0(k4_subset_1(X1,X2,X3),X3)
    | ~ m1_subset_1(k4_subset_1(X1,X2,X3),k1_zfmisc_1(X4))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_65]),c_0_30])).

cnf(c_0_79,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_66,c_0_67]),
    [final]).

cnf(c_0_80,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X3),k1_setfam_1(k2_tarski(X3,k4_subset_1(X1,X2,X3)))) = X2
    | ~ m1_subset_1(k4_subset_1(X1,X2,X3),k1_zfmisc_1(X4))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X2,X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_68]),c_0_30])).

cnf(c_0_81,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X3),k1_setfam_1(k2_tarski(X2,k4_subset_1(X1,X2,X3)))) = k5_xboole_0(k4_subset_1(X1,X2,X3),X2)
    | ~ m1_subset_1(k4_subset_1(X1,X2,X3),k1_zfmisc_1(X4))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_58]),c_0_30])).

cnf(c_0_82,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X3),k1_setfam_1(k2_tarski(X2,k4_subset_1(X1,X2,X3)))) = X3
    | ~ m1_subset_1(k4_subset_1(X1,X2,X3),k1_zfmisc_1(X4))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X3,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_69]),c_0_30])).

cnf(c_0_83,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X2),k1_setfam_1(k2_tarski(X2,k4_subset_1(X1,X2,X2)))) = X2
    | ~ m1_subset_1(k4_subset_1(X1,X2,X2),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X2,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_70]),c_0_30])).

cnf(c_0_84,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k4_subset_1(X2,X3,X1)))) = k5_xboole_0(X1,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X4))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_71])).

cnf(c_0_85,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k4_subset_1(X2,X1,X3)))) = k5_xboole_0(X1,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X4))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_72])).

cnf(c_0_86,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X2),X2) = X2
    | ~ m1_subset_1(k4_subset_1(X1,X2,X2),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X2,X2) ),
    inference(spm,[status(thm)],[c_0_58,c_0_70])).

cnf(c_0_87,plain,
    ( k7_subset_1(X1,k3_tarski(k2_tarski(X2,X3)),X3) = k5_xboole_0(k3_tarski(k2_tarski(X2,X3)),X3)
    | ~ m1_subset_1(k3_tarski(k2_tarski(X2,X3)),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_36]),
    [final]).

cnf(c_0_88,negated_conjecture,
    ( k3_tarski(k2_tarski(esk2_0,esk3_0)) = k2_struct_0(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_49]),c_0_50])]),
    [final]).

cnf(c_0_89,negated_conjecture,
    ( k1_setfam_1(k2_tarski(esk3_0,k2_struct_0(esk1_0))) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_47]),c_0_49]),c_0_50])]),
    [final]).

cnf(c_0_90,negated_conjecture,
    ( k5_xboole_0(k2_struct_0(esk1_0),esk3_0) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_47]),c_0_49]),c_0_50]),c_0_63])]),
    [final]).

cnf(c_0_91,negated_conjecture,
    ( k5_xboole_0(k2_struct_0(esk1_0),esk2_0) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_47]),c_0_49]),c_0_50]),c_0_75])]),
    [final]).

cnf(c_0_92,plain,
    ( k7_subset_1(X1,X2,X3) = k7_subset_1(X4,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X4)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_37]),
    [final]).

cnf(c_0_93,negated_conjecture,
    ( k5_xboole_0(k2_struct_0(esk1_0),esk2_0) != esk3_0
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_76,c_0_77])).

cnf(c_0_94,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X3),k1_setfam_1(k2_tarski(X3,k4_subset_1(X1,X2,X3)))) = k5_xboole_0(k4_subset_1(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_78,c_0_79]),
    [final]).

cnf(c_0_95,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X3),k1_setfam_1(k2_tarski(X3,k4_subset_1(X1,X2,X3)))) = X2
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X2,X3) ),
    inference(spm,[status(thm)],[c_0_80,c_0_79]),
    [final]).

cnf(c_0_96,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X3),k1_setfam_1(k2_tarski(X2,k4_subset_1(X1,X2,X3)))) = k5_xboole_0(k4_subset_1(X1,X2,X3),X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_81,c_0_79]),
    [final]).

cnf(c_0_97,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X3),k1_setfam_1(k2_tarski(X2,k4_subset_1(X1,X2,X3)))) = X3
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X3,X2) ),
    inference(spm,[status(thm)],[c_0_82,c_0_79]),
    [final]).

cnf(c_0_98,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X2),k1_setfam_1(k2_tarski(X2,k4_subset_1(X1,X2,X2)))) = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X2,X2) ),
    inference(spm,[status(thm)],[c_0_83,c_0_79]),
    [final]).

cnf(c_0_99,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k4_subset_1(X2,X3,X1)))) = k5_xboole_0(X1,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_84,c_0_79]),
    [final]).

cnf(c_0_100,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k4_subset_1(X2,X1,X3)))) = k5_xboole_0(X1,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_85,c_0_79]),
    [final]).

cnf(c_0_101,plain,
    ( k5_xboole_0(k4_subset_1(X1,X2,X2),X2) = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X2,X2) ),
    inference(spm,[status(thm)],[c_0_86,c_0_79]),
    [final]).

cnf(c_0_102,plain,
    ( k4_subset_1(X1,X2,X3) = k4_subset_1(X4,X3,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X4))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X4)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_56]),
    [final]).

cnf(c_0_103,plain,
    ( k7_subset_1(X1,k3_tarski(k2_tarski(X2,X3)),X3) = X2
    | ~ m1_subset_1(k3_tarski(k2_tarski(X2,X3)),k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X2,X3) ),
    inference(spm,[status(thm)],[c_0_40,c_0_87]),
    [final]).

cnf(c_0_104,negated_conjecture,
    ( k4_subset_1(X1,esk3_0,esk2_0) = k2_struct_0(esk1_0)
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_88]),
    [final]).

cnf(c_0_105,negated_conjecture,
    ( k7_subset_1(X1,esk3_0,k2_struct_0(esk1_0)) = k5_xboole_0(esk3_0,esk3_0)
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_89]),
    [final]).

cnf(c_0_106,negated_conjecture,
    ( k7_subset_1(X1,k2_struct_0(esk1_0),esk3_0) = esk2_0
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_89]),c_0_90]),
    [final]).

cnf(c_0_107,negated_conjecture,
    ( k7_subset_1(X1,k2_struct_0(esk1_0),esk2_0) = esk3_0
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_77,c_0_91]),
    [final]).

cnf(c_0_108,negated_conjecture,
    ( k7_subset_1(X1,esk2_0,k2_struct_0(esk1_0)) = k5_xboole_0(esk2_0,esk2_0)
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_64]),
    [final]).

cnf(c_0_109,negated_conjecture,
    ( k7_subset_1(X1,k2_struct_0(esk1_0),esk2_0) != esk3_0
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_76,c_0_92]),
    [final]).

cnf(c_0_110,negated_conjecture,
    ( ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_93,c_0_91])]),
    [final]).

cnf(c_0_111,negated_conjecture,
    ( l1_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_43]),
    [final]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.32  % Computer   : n006.cluster.edu
% 0.14/0.32  % Model      : x86_64 x86_64
% 0.14/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.32  % Memory     : 8042.1875MB
% 0.14/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.32  % CPULimit   : 60
% 0.14/0.32  % WCLimit    : 600
% 0.14/0.32  % DateTime   : Tue Dec  1 16:25:37 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.14/0.33  # Version: 2.5pre002
% 0.14/0.33  # No SInE strategy applied
% 0.14/0.33  # Trying AutoSched0 for 299 seconds
% 0.14/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.14/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.14/0.38  #
% 0.14/0.38  # Preprocessing time       : 0.026 s
% 0.14/0.38  # Presaturation interreduction done
% 0.14/0.38  
% 0.14/0.38  # No proof found!
% 0.14/0.38  # SZS status CounterSatisfiable
% 0.14/0.38  # SZS output start Saturation
% 0.14/0.38  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.14/0.38  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.14/0.38  fof(t88_xboole_1, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>k4_xboole_0(k2_xboole_0(X1,X2),X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_xboole_1)).
% 0.14/0.38  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.14/0.38  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.14/0.38  fof(t21_xboole_1, axiom, ![X1, X2]:k3_xboole_0(X1,k2_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_xboole_1)).
% 0.14/0.38  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.14/0.38  fof(redefinition_k7_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k7_subset_1(X1,X2,X3)=k4_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 0.14/0.38  fof(redefinition_k4_subset_1, axiom, ![X1, X2, X3]:((m1_subset_1(X2,k1_zfmisc_1(X1))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>k4_subset_1(X1,X2,X3)=k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 0.14/0.38  fof(t25_pre_topc, conjecture, ![X1]:(l1_struct_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((k2_struct_0(X1)=k4_subset_1(u1_struct_0(X1),X2,X3)&r1_xboole_0(X2,X3))=>X3=k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_pre_topc)).
% 0.14/0.38  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 0.14/0.38  fof(dt_k2_subset_1, axiom, ![X1]:m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 0.14/0.38  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 0.14/0.38  fof(c_0_13, plain, ![X10, X11]:k4_xboole_0(X10,X11)=k5_xboole_0(X10,k3_xboole_0(X10,X11)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.14/0.38  fof(c_0_14, plain, ![X26, X27]:k1_setfam_1(k2_tarski(X26,X27))=k3_xboole_0(X26,X27), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.14/0.38  fof(c_0_15, plain, ![X14, X15]:(~r1_xboole_0(X14,X15)|k4_xboole_0(k2_xboole_0(X14,X15),X15)=X14), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t88_xboole_1])])).
% 0.14/0.38  fof(c_0_16, plain, ![X16, X17]:k3_tarski(k2_tarski(X16,X17))=k2_xboole_0(X16,X17), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.14/0.38  cnf(c_0_17, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.14/0.38  cnf(c_0_18, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.14/0.38  fof(c_0_19, plain, ![X6, X7]:k3_xboole_0(X6,X7)=k3_xboole_0(X7,X6), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.14/0.38  fof(c_0_20, plain, ![X12, X13]:k3_xboole_0(X12,k2_xboole_0(X12,X13))=X12, inference(variable_rename,[status(thm)],[t21_xboole_1])).
% 0.14/0.38  fof(c_0_21, plain, ![X4, X5]:k2_xboole_0(X4,X5)=k2_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.14/0.38  cnf(c_0_22, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X2)=X1|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.14/0.38  cnf(c_0_23, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.14/0.38  cnf(c_0_24, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))), inference(rw,[status(thm)],[c_0_17, c_0_18])).
% 0.14/0.38  cnf(c_0_25, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.14/0.38  cnf(c_0_26, plain, (k3_xboole_0(X1,k2_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.14/0.38  cnf(c_0_27, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.14/0.38  fof(c_0_28, plain, ![X23, X24, X25]:(~m1_subset_1(X24,k1_zfmisc_1(X23))|k7_subset_1(X23,X24,X25)=k4_xboole_0(X24,X25)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).
% 0.14/0.38  cnf(c_0_29, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k1_setfam_1(k2_tarski(k3_tarski(k2_tarski(X1,X2)),X2)))=X1|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22, c_0_23]), c_0_24])).
% 0.14/0.38  cnf(c_0_30, plain, (k1_setfam_1(k2_tarski(X1,X2))=k1_setfam_1(k2_tarski(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25, c_0_18]), c_0_18]), ['final']).
% 0.14/0.38  cnf(c_0_31, plain, (k1_setfam_1(k2_tarski(X1,k3_tarski(k2_tarski(X1,X2))))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26, c_0_23]), c_0_18]), ['final']).
% 0.14/0.38  cnf(c_0_32, plain, (k3_tarski(k2_tarski(X1,X2))=k3_tarski(k2_tarski(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27, c_0_23]), c_0_23]), ['final']).
% 0.14/0.38  cnf(c_0_33, plain, (k7_subset_1(X2,X1,X3)=k4_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.14/0.38  fof(c_0_34, plain, ![X20, X21, X22]:(~m1_subset_1(X21,k1_zfmisc_1(X20))|~m1_subset_1(X22,k1_zfmisc_1(X20))|k4_subset_1(X20,X21,X22)=k2_xboole_0(X21,X22)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).
% 0.14/0.38  cnf(c_0_35, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),k1_setfam_1(k2_tarski(X2,k3_tarski(k2_tarski(X1,X2)))))=X1|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_29, c_0_30])).
% 0.14/0.38  cnf(c_0_36, plain, (k1_setfam_1(k2_tarski(X1,k3_tarski(k2_tarski(X2,X1))))=X1), inference(spm,[status(thm)],[c_0_31, c_0_32]), ['final']).
% 0.14/0.38  cnf(c_0_37, plain, (k7_subset_1(X2,X1,X3)=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X3)))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_33, c_0_24]), ['final']).
% 0.14/0.38  cnf(c_0_38, plain, (k4_subset_1(X2,X1,X3)=k2_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.14/0.38  fof(c_0_39, negated_conjecture, ~(![X1]:(l1_struct_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((k2_struct_0(X1)=k4_subset_1(u1_struct_0(X1),X2,X3)&r1_xboole_0(X2,X3))=>X3=k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2)))))), inference(assume_negation,[status(cth)],[t25_pre_topc])).
% 0.14/0.38  cnf(c_0_40, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2)=X1|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_35, c_0_36]), ['final']).
% 0.14/0.38  cnf(c_0_41, plain, (k7_subset_1(X1,X2,X3)=k5_xboole_0(X2,k1_setfam_1(k2_tarski(X3,X2)))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_37, c_0_30]), ['final']).
% 0.14/0.38  cnf(c_0_42, plain, (k4_subset_1(X2,X1,X3)=k3_tarski(k2_tarski(X1,X3))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_38, c_0_23]), ['final']).
% 0.14/0.38  fof(c_0_43, negated_conjecture, (l1_struct_0(esk1_0)&(m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&(m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&((k2_struct_0(esk1_0)=k4_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0)&r1_xboole_0(esk2_0,esk3_0))&esk3_0!=k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_39])])])).
% 0.14/0.38  cnf(c_0_44, plain, (k5_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1)=X2|~r1_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_40, c_0_32]), ['final']).
% 0.14/0.38  cnf(c_0_45, plain, (k7_subset_1(X1,k3_tarski(k2_tarski(X2,X3)),X2)=k5_xboole_0(k3_tarski(k2_tarski(X2,X3)),X2)|~m1_subset_1(k3_tarski(k2_tarski(X2,X3)),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_41, c_0_31]), ['final']).
% 0.14/0.38  cnf(c_0_46, plain, (k1_setfam_1(k2_tarski(X1,k4_subset_1(X2,X1,X3)))=X1|~m1_subset_1(X3,k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_31, c_0_42]), ['final']).
% 0.14/0.38  cnf(c_0_47, negated_conjecture, (k2_struct_0(esk1_0)=k4_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_43]), ['final']).
% 0.14/0.38  cnf(c_0_48, plain, (k4_subset_1(X1,X2,X3)=k4_subset_1(X4,X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~m1_subset_1(X3,k1_zfmisc_1(X4))|~m1_subset_1(X2,k1_zfmisc_1(X4))), inference(spm,[status(thm)],[c_0_42, c_0_42]), ['final']).
% 0.14/0.38  cnf(c_0_49, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_43]), ['final']).
% 0.14/0.38  cnf(c_0_50, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_43]), ['final']).
% 0.14/0.38  fof(c_0_51, plain, ![X8, X9]:(~r1_xboole_0(X8,X9)|r1_xboole_0(X9,X8)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 0.14/0.38  cnf(c_0_52, plain, (k1_setfam_1(k2_tarski(X1,k4_subset_1(X2,X3,X1)))=X1|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_36, c_0_42]), ['final']).
% 0.14/0.38  fof(c_0_53, plain, ![X19]:m1_subset_1(k2_subset_1(X19),k1_zfmisc_1(X19)), inference(variable_rename,[status(thm)],[dt_k2_subset_1])).
% 0.14/0.38  fof(c_0_54, plain, ![X18]:k2_subset_1(X18)=X18, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 0.14/0.38  cnf(c_0_55, plain, (k7_subset_1(X1,k3_tarski(k2_tarski(X2,X3)),X2)=X3|~m1_subset_1(k3_tarski(k2_tarski(X2,X3)),k1_zfmisc_1(X1))|~r1_xboole_0(X3,X2)), inference(spm,[status(thm)],[c_0_44, c_0_45]), ['final']).
% 0.14/0.38  cnf(c_0_56, plain, (k4_subset_1(X1,X2,X3)=k3_tarski(k2_tarski(X3,X2))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_32, c_0_42]), ['final']).
% 0.14/0.38  cnf(c_0_57, plain, (k5_xboole_0(k4_subset_1(X1,X2,X3),X3)=X2|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(X2,X3)), inference(spm,[status(thm)],[c_0_40, c_0_42]), ['final']).
% 0.14/0.38  cnf(c_0_58, plain, (k7_subset_1(X1,k4_subset_1(X2,X3,X4),X3)=k5_xboole_0(k4_subset_1(X2,X3,X4),X3)|~m1_subset_1(k4_subset_1(X2,X3,X4),k1_zfmisc_1(X1))|~m1_subset_1(X4,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_41, c_0_46]), ['final']).
% 0.14/0.38  cnf(c_0_59, plain, (k7_subset_1(X1,X2,k3_tarski(k2_tarski(X3,X2)))=k5_xboole_0(X2,X2)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_37, c_0_36]), ['final']).
% 0.14/0.38  cnf(c_0_60, plain, (k7_subset_1(X1,X2,k3_tarski(k2_tarski(X2,X3)))=k5_xboole_0(X2,X2)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_37, c_0_31]), ['final']).
% 0.14/0.38  cnf(c_0_61, negated_conjecture, (k4_subset_1(X1,esk2_0,esk3_0)=k2_struct_0(esk1_0)|~m1_subset_1(esk3_0,k1_zfmisc_1(X1))|~m1_subset_1(esk2_0,k1_zfmisc_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_49]), c_0_50])]), ['final']).
% 0.14/0.38  cnf(c_0_62, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_51]), ['final']).
% 0.14/0.38  cnf(c_0_63, negated_conjecture, (r1_xboole_0(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_43]), ['final']).
% 0.14/0.38  cnf(c_0_64, negated_conjecture, (k1_setfam_1(k2_tarski(esk2_0,k2_struct_0(esk1_0)))=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_49]), c_0_50])]), ['final']).
% 0.14/0.38  cnf(c_0_65, plain, (k7_subset_1(X1,k4_subset_1(X2,X3,X4),X4)=k5_xboole_0(k4_subset_1(X2,X3,X4),X4)|~m1_subset_1(k4_subset_1(X2,X3,X4),k1_zfmisc_1(X1))|~m1_subset_1(X4,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_41, c_0_52]), ['final']).
% 0.14/0.38  cnf(c_0_66, plain, (m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.14/0.38  cnf(c_0_67, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.14/0.38  cnf(c_0_68, plain, (k7_subset_1(X1,k4_subset_1(X2,X3,X4),X4)=X3|~m1_subset_1(k4_subset_1(X2,X3,X4),k1_zfmisc_1(X1))|~m1_subset_1(X4,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_xboole_0(X3,X4)), inference(spm,[status(thm)],[c_0_55, c_0_56]), ['final']).
% 0.14/0.38  cnf(c_0_69, plain, (k7_subset_1(X1,k4_subset_1(X2,X3,X4),X3)=X4|~m1_subset_1(k4_subset_1(X2,X3,X4),k1_zfmisc_1(X1))|~m1_subset_1(X4,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_xboole_0(X4,X3)), inference(spm,[status(thm)],[c_0_55, c_0_42]), ['final']).
% 0.14/0.38  cnf(c_0_70, plain, (k7_subset_1(X1,k4_subset_1(X2,X3,X3),X3)=X3|~m1_subset_1(k4_subset_1(X2,X3,X3),k1_zfmisc_1(X1))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_xboole_0(X3,X3)), inference(spm,[status(thm)],[c_0_57, c_0_58]), ['final']).
% 0.14/0.38  cnf(c_0_71, plain, (k7_subset_1(X1,X2,k4_subset_1(X3,X4,X2))=k5_xboole_0(X2,X2)|~m1_subset_1(X2,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X3))|~m1_subset_1(X4,k1_zfmisc_1(X3))), inference(spm,[status(thm)],[c_0_59, c_0_42]), ['final']).
% 0.14/0.38  cnf(c_0_72, plain, (k7_subset_1(X1,X2,k4_subset_1(X3,X2,X4))=k5_xboole_0(X2,X2)|~m1_subset_1(X2,k1_zfmisc_1(X1))|~m1_subset_1(X4,k1_zfmisc_1(X3))|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(spm,[status(thm)],[c_0_60, c_0_42]), ['final']).
% 0.14/0.38  cnf(c_0_73, negated_conjecture, (k3_tarski(k2_tarski(esk2_0,esk3_0))=k2_struct_0(esk1_0)|~m1_subset_1(esk3_0,k1_zfmisc_1(X1))|~m1_subset_1(esk2_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_42, c_0_61])).
% 0.14/0.38  cnf(c_0_74, plain, (k5_xboole_0(k4_subset_1(X1,X2,X3),X2)=X3|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(X3,X2)), inference(spm,[status(thm)],[c_0_44, c_0_42]), ['final']).
% 0.14/0.38  cnf(c_0_75, negated_conjecture, (r1_xboole_0(esk3_0,esk2_0)), inference(spm,[status(thm)],[c_0_62, c_0_63]), ['final']).
% 0.14/0.38  cnf(c_0_76, negated_conjecture, (esk3_0!=k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)), inference(split_conjunct,[status(thm)],[c_0_43]), ['final']).
% 0.14/0.38  cnf(c_0_77, negated_conjecture, (k7_subset_1(X1,k2_struct_0(esk1_0),esk2_0)=k5_xboole_0(k2_struct_0(esk1_0),esk2_0)|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_41, c_0_64])).
% 0.14/0.38  cnf(c_0_78, plain, (k5_xboole_0(k4_subset_1(X1,X2,X3),k1_setfam_1(k2_tarski(X3,k4_subset_1(X1,X2,X3))))=k5_xboole_0(k4_subset_1(X1,X2,X3),X3)|~m1_subset_1(k4_subset_1(X1,X2,X3),k1_zfmisc_1(X4))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_65]), c_0_30])).
% 0.14/0.38  cnf(c_0_79, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_66, c_0_67]), ['final']).
% 0.14/0.38  cnf(c_0_80, plain, (k5_xboole_0(k4_subset_1(X1,X2,X3),k1_setfam_1(k2_tarski(X3,k4_subset_1(X1,X2,X3))))=X2|~m1_subset_1(k4_subset_1(X1,X2,X3),k1_zfmisc_1(X4))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(X2,X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_68]), c_0_30])).
% 0.14/0.38  cnf(c_0_81, plain, (k5_xboole_0(k4_subset_1(X1,X2,X3),k1_setfam_1(k2_tarski(X2,k4_subset_1(X1,X2,X3))))=k5_xboole_0(k4_subset_1(X1,X2,X3),X2)|~m1_subset_1(k4_subset_1(X1,X2,X3),k1_zfmisc_1(X4))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_58]), c_0_30])).
% 0.14/0.38  cnf(c_0_82, plain, (k5_xboole_0(k4_subset_1(X1,X2,X3),k1_setfam_1(k2_tarski(X2,k4_subset_1(X1,X2,X3))))=X3|~m1_subset_1(k4_subset_1(X1,X2,X3),k1_zfmisc_1(X4))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(X3,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_69]), c_0_30])).
% 0.14/0.38  cnf(c_0_83, plain, (k5_xboole_0(k4_subset_1(X1,X2,X2),k1_setfam_1(k2_tarski(X2,k4_subset_1(X1,X2,X2))))=X2|~m1_subset_1(k4_subset_1(X1,X2,X2),k1_zfmisc_1(X3))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(X2,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_70]), c_0_30])).
% 0.14/0.38  cnf(c_0_84, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k4_subset_1(X2,X3,X1))))=k5_xboole_0(X1,X1)|~m1_subset_1(X1,k1_zfmisc_1(X4))|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_37, c_0_71])).
% 0.14/0.38  cnf(c_0_85, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k4_subset_1(X2,X1,X3))))=k5_xboole_0(X1,X1)|~m1_subset_1(X1,k1_zfmisc_1(X4))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_37, c_0_72])).
% 0.14/0.38  cnf(c_0_86, plain, (k5_xboole_0(k4_subset_1(X1,X2,X2),X2)=X2|~m1_subset_1(k4_subset_1(X1,X2,X2),k1_zfmisc_1(X3))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(X2,X2)), inference(spm,[status(thm)],[c_0_58, c_0_70])).
% 0.14/0.38  cnf(c_0_87, plain, (k7_subset_1(X1,k3_tarski(k2_tarski(X2,X3)),X3)=k5_xboole_0(k3_tarski(k2_tarski(X2,X3)),X3)|~m1_subset_1(k3_tarski(k2_tarski(X2,X3)),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_41, c_0_36]), ['final']).
% 0.14/0.38  cnf(c_0_88, negated_conjecture, (k3_tarski(k2_tarski(esk2_0,esk3_0))=k2_struct_0(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_49]), c_0_50])]), ['final']).
% 0.14/0.38  cnf(c_0_89, negated_conjecture, (k1_setfam_1(k2_tarski(esk3_0,k2_struct_0(esk1_0)))=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_47]), c_0_49]), c_0_50])]), ['final']).
% 0.14/0.38  cnf(c_0_90, negated_conjecture, (k5_xboole_0(k2_struct_0(esk1_0),esk3_0)=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_47]), c_0_49]), c_0_50]), c_0_63])]), ['final']).
% 0.14/0.38  cnf(c_0_91, negated_conjecture, (k5_xboole_0(k2_struct_0(esk1_0),esk2_0)=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_47]), c_0_49]), c_0_50]), c_0_75])]), ['final']).
% 0.14/0.38  cnf(c_0_92, plain, (k7_subset_1(X1,X2,X3)=k7_subset_1(X4,X2,X3)|~m1_subset_1(X2,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X4))), inference(spm,[status(thm)],[c_0_37, c_0_37]), ['final']).
% 0.14/0.38  cnf(c_0_93, negated_conjecture, (k5_xboole_0(k2_struct_0(esk1_0),esk2_0)!=esk3_0|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_76, c_0_77])).
% 0.14/0.38  cnf(c_0_94, plain, (k5_xboole_0(k4_subset_1(X1,X2,X3),k1_setfam_1(k2_tarski(X3,k4_subset_1(X1,X2,X3))))=k5_xboole_0(k4_subset_1(X1,X2,X3),X3)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_78, c_0_79]), ['final']).
% 0.14/0.38  cnf(c_0_95, plain, (k5_xboole_0(k4_subset_1(X1,X2,X3),k1_setfam_1(k2_tarski(X3,k4_subset_1(X1,X2,X3))))=X2|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(X2,X3)), inference(spm,[status(thm)],[c_0_80, c_0_79]), ['final']).
% 0.14/0.38  cnf(c_0_96, plain, (k5_xboole_0(k4_subset_1(X1,X2,X3),k1_setfam_1(k2_tarski(X2,k4_subset_1(X1,X2,X3))))=k5_xboole_0(k4_subset_1(X1,X2,X3),X2)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_81, c_0_79]), ['final']).
% 0.14/0.38  cnf(c_0_97, plain, (k5_xboole_0(k4_subset_1(X1,X2,X3),k1_setfam_1(k2_tarski(X2,k4_subset_1(X1,X2,X3))))=X3|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(X3,X2)), inference(spm,[status(thm)],[c_0_82, c_0_79]), ['final']).
% 0.14/0.38  cnf(c_0_98, plain, (k5_xboole_0(k4_subset_1(X1,X2,X2),k1_setfam_1(k2_tarski(X2,k4_subset_1(X1,X2,X2))))=X2|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(X2,X2)), inference(spm,[status(thm)],[c_0_83, c_0_79]), ['final']).
% 0.14/0.38  cnf(c_0_99, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k4_subset_1(X2,X3,X1))))=k5_xboole_0(X1,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_84, c_0_79]), ['final']).
% 0.14/0.38  cnf(c_0_100, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k4_subset_1(X2,X1,X3))))=k5_xboole_0(X1,X1)|~m1_subset_1(X3,k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_85, c_0_79]), ['final']).
% 0.14/0.38  cnf(c_0_101, plain, (k5_xboole_0(k4_subset_1(X1,X2,X2),X2)=X2|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(X2,X2)), inference(spm,[status(thm)],[c_0_86, c_0_79]), ['final']).
% 0.14/0.38  cnf(c_0_102, plain, (k4_subset_1(X1,X2,X3)=k4_subset_1(X4,X3,X2)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X4))|~m1_subset_1(X3,k1_zfmisc_1(X4))), inference(spm,[status(thm)],[c_0_42, c_0_56]), ['final']).
% 0.14/0.38  cnf(c_0_103, plain, (k7_subset_1(X1,k3_tarski(k2_tarski(X2,X3)),X3)=X2|~m1_subset_1(k3_tarski(k2_tarski(X2,X3)),k1_zfmisc_1(X1))|~r1_xboole_0(X2,X3)), inference(spm,[status(thm)],[c_0_40, c_0_87]), ['final']).
% 0.14/0.38  cnf(c_0_104, negated_conjecture, (k4_subset_1(X1,esk3_0,esk2_0)=k2_struct_0(esk1_0)|~m1_subset_1(esk2_0,k1_zfmisc_1(X1))|~m1_subset_1(esk3_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_56, c_0_88]), ['final']).
% 0.14/0.38  cnf(c_0_105, negated_conjecture, (k7_subset_1(X1,esk3_0,k2_struct_0(esk1_0))=k5_xboole_0(esk3_0,esk3_0)|~m1_subset_1(esk3_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_37, c_0_89]), ['final']).
% 0.14/0.38  cnf(c_0_106, negated_conjecture, (k7_subset_1(X1,k2_struct_0(esk1_0),esk3_0)=esk2_0|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_89]), c_0_90]), ['final']).
% 0.14/0.38  cnf(c_0_107, negated_conjecture, (k7_subset_1(X1,k2_struct_0(esk1_0),esk2_0)=esk3_0|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_77, c_0_91]), ['final']).
% 0.14/0.38  cnf(c_0_108, negated_conjecture, (k7_subset_1(X1,esk2_0,k2_struct_0(esk1_0))=k5_xboole_0(esk2_0,esk2_0)|~m1_subset_1(esk2_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_37, c_0_64]), ['final']).
% 0.14/0.38  cnf(c_0_109, negated_conjecture, (k7_subset_1(X1,k2_struct_0(esk1_0),esk2_0)!=esk3_0|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_76, c_0_92]), ['final']).
% 0.14/0.38  cnf(c_0_110, negated_conjecture, (~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_93, c_0_91])]), ['final']).
% 0.14/0.38  cnf(c_0_111, negated_conjecture, (l1_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_43]), ['final']).
% 0.14/0.38  # SZS output end Saturation
% 0.14/0.38  # Proof object total steps             : 112
% 0.14/0.38  # Proof object clause steps            : 85
% 0.14/0.38  # Proof object formula steps           : 27
% 0.14/0.38  # Proof object conjectures             : 26
% 0.14/0.38  # Proof object clause conjectures      : 23
% 0.14/0.38  # Proof object formula conjectures     : 3
% 0.14/0.38  # Proof object initial clauses used    : 18
% 0.14/0.38  # Proof object initial formulas used   : 13
% 0.14/0.38  # Proof object generating inferences   : 55
% 0.14/0.38  # Proof object simplifying inferences  : 42
% 0.14/0.38  # Parsed axioms                        : 13
% 0.14/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.38  # Initial clauses                      : 18
% 0.14/0.38  # Removed in clause preprocessing      : 4
% 0.14/0.38  # Initial clauses in saturation        : 14
% 0.14/0.38  # Processed clauses                    : 531
% 0.14/0.38  # ...of these trivial                  : 8
% 0.14/0.38  # ...subsumed                          : 425
% 0.14/0.38  # ...remaining for further processing  : 98
% 0.14/0.38  # Other redundant clauses eliminated   : 0
% 0.14/0.38  # Clauses deleted for lack of memory   : 0
% 0.14/0.38  # Backward-subsumed                    : 21
% 0.14/0.38  # Backward-rewritten                   : 3
% 0.14/0.38  # Generated clauses                    : 677
% 0.14/0.38  # ...of the previous two non-trivial   : 550
% 0.14/0.38  # Contextual simplify-reflections      : 0
% 0.14/0.38  # Paramodulations                      : 677
% 0.14/0.38  # Factorizations                       : 0
% 0.14/0.38  # Equation resolutions                 : 0
% 0.14/0.38  # Propositional unsat checks           : 0
% 0.14/0.38  #    Propositional check models        : 0
% 0.14/0.38  #    Propositional check unsatisfiable : 0
% 0.14/0.38  #    Propositional clauses             : 0
% 0.14/0.38  #    Propositional clauses after purity: 0
% 0.14/0.38  #    Propositional unsat core size     : 0
% 0.14/0.38  #    Propositional preprocessing time  : 0.000
% 0.14/0.38  #    Propositional encoding time       : 0.000
% 0.14/0.38  #    Propositional solver time         : 0.000
% 0.14/0.38  #    Success case prop preproc time    : 0.000
% 0.14/0.38  #    Success case prop encoding time   : 0.000
% 0.14/0.38  #    Success case prop solver time     : 0.000
% 0.14/0.38  # Current number of processed clauses  : 60
% 0.14/0.38  #    Positive orientable unit clauses  : 14
% 0.14/0.38  #    Positive unorientable unit clauses: 2
% 0.14/0.38  #    Negative unit clauses             : 2
% 0.14/0.38  #    Non-unit-clauses                  : 42
% 0.14/0.38  # Current number of unprocessed clauses: 0
% 0.14/0.38  # ...number of literals in the above   : 0
% 0.14/0.38  # Current number of archived formulas  : 0
% 0.14/0.38  # Current number of archived clauses   : 42
% 0.14/0.38  # Clause-clause subsumption calls (NU) : 4431
% 0.14/0.38  # Rec. Clause-clause subsumption calls : 989
% 0.14/0.38  # Non-unit clause-clause subsumptions  : 443
% 0.14/0.38  # Unit Clause-clause subsumption calls : 1
% 0.14/0.38  # Rewrite failures with RHS unbound    : 0
% 0.14/0.38  # BW rewrite match attempts            : 17
% 0.14/0.38  # BW rewrite match successes           : 12
% 0.14/0.38  # Condensation attempts                : 0
% 0.14/0.38  # Condensation successes               : 0
% 0.14/0.38  # Termbank termtop insertions          : 15769
% 0.14/0.38  
% 0.14/0.38  # -------------------------------------------------
% 0.14/0.38  # User time                : 0.051 s
% 0.14/0.38  # System time              : 0.003 s
% 0.14/0.38  # Total time               : 0.054 s
% 0.14/0.38  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
