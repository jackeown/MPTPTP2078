%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:11:12 EST 2020

% Result     : Theorem 0.98s
% Output     : CNFRefutation 0.98s
% Verified   : 
% Statistics : Number of formulae       :  110 (1182 expanded)
%              Number of clauses        :   69 ( 561 expanded)
%              Number of leaves         :   20 ( 297 expanded)
%              Depth                    :   23
%              Number of atoms          :  256 (2573 expanded)
%              Number of equality atoms :   87 (1186 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(t75_tops_1,conjecture,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k2_tops_1(X1,k2_tops_1(X1,k2_tops_1(X1,X2))) = k2_tops_1(X1,k2_tops_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_tops_1)).

fof(involutiveness_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,k3_subset_1(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

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

fof(t62_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k2_tops_1(X1,X2) = k2_tops_1(X1,k3_subset_1(u1_struct_0(X1),X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_tops_1)).

fof(dt_k2_tops_1,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k2_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(t69_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v4_pre_topc(X2,X1)
           => r1_tarski(k2_tops_1(X1,X2),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_tops_1)).

fof(redefinition_k7_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k7_subset_1(X1,X2,X3) = k4_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(t74_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k1_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

fof(fc1_tops_1,axiom,(
    ! [X1,X2] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => v4_pre_topc(k2_pre_topc(X1,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_tops_1)).

fof(l79_tops_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k2_pre_topc(X1,k2_tops_1(X1,X2)) = k2_tops_1(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l79_tops_1)).

fof(l80_tops_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k1_tops_1(X1,k2_tops_1(X1,k2_tops_1(X1,X2))) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l80_tops_1)).

fof(c_0_20,plain,(
    ! [X12,X13] :
      ( ~ r1_tarski(X12,X13)
      | k3_xboole_0(X12,X13) = X12 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

fof(c_0_21,plain,(
    ! [X17,X18] : k4_xboole_0(X17,k4_xboole_0(X17,X18)) = k3_xboole_0(X17,X18) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_22,plain,(
    ! [X4,X5] : k3_xboole_0(X4,X5) = k3_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_23,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_24,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_25,plain,(
    ! [X8,X9] :
      ( ( k4_xboole_0(X8,X9) != k1_xboole_0
        | r1_tarski(X8,X9) )
      & ( ~ r1_tarski(X8,X9)
        | k4_xboole_0(X8,X9) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

fof(c_0_26,plain,(
    ! [X6,X7] :
      ( ( r1_tarski(X6,X7)
        | X6 != X7 )
      & ( r1_tarski(X7,X6)
        | X6 != X7 )
      & ( ~ r1_tarski(X6,X7)
        | ~ r1_tarski(X7,X6)
        | X6 = X7 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_27,plain,(
    ! [X14,X15,X16] : k4_xboole_0(k4_xboole_0(X14,X15),X16) = k4_xboole_0(X14,k2_xboole_0(X15,X16)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

cnf(c_0_28,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_30,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_31,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_32,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_33,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X2,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_24]),c_0_24])).

cnf(c_0_34,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_35,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_31])).

cnf(c_0_36,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k1_xboole_0
    | ~ r1_tarski(X1,k2_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_32])).

cnf(c_0_37,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k1_xboole_0
    | ~ r1_tarski(X2,k4_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_33])).

cnf(c_0_38,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

fof(c_0_39,plain,(
    ! [X28,X29] :
      ( ( ~ m1_subset_1(X28,k1_zfmisc_1(X29))
        | r1_tarski(X28,X29) )
      & ( ~ r1_tarski(X28,X29)
        | m1_subset_1(X28,k1_zfmisc_1(X29)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_40,plain,
    ( k4_xboole_0(k4_xboole_0(k2_xboole_0(X1,X2),X1),X2) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_36,c_0_35])).

cnf(c_0_41,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1)) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_35])])).

fof(c_0_42,plain,(
    ! [X10,X11] :
      ( ~ r1_tarski(X10,X11)
      | k2_xboole_0(X10,X11) = X11 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_43,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_44,plain,
    ( k4_xboole_0(k2_xboole_0(k1_xboole_0,X1),X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_40,c_0_38])).

cnf(c_0_45,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_41]),c_0_38])).

cnf(c_0_46,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0
    | ~ r1_tarski(k2_xboole_0(X2,X1),X2) ),
    inference(spm,[status(thm)],[c_0_40,c_0_30])).

cnf(c_0_47,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_48,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_xboole_0(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_36,c_0_43])).

cnf(c_0_49,plain,
    ( k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_44]),c_0_38]),c_0_32]),c_0_38]),c_0_45]),c_0_38])).

cnf(c_0_50,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

fof(c_0_51,negated_conjecture,(
    ~ ! [X1] :
        ( ( v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => k2_tops_1(X1,k2_tops_1(X1,k2_tops_1(X1,X2))) = k2_tops_1(X1,k2_tops_1(X1,X2)) ) ) ),
    inference(assume_negation,[status(cth)],[t75_tops_1])).

fof(c_0_52,plain,(
    ! [X23,X24] :
      ( ~ m1_subset_1(X24,k1_zfmisc_1(X23))
      | k3_subset_1(X23,k3_subset_1(X23,X24)) = X24 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).

fof(c_0_53,plain,(
    ! [X19,X20] :
      ( ~ m1_subset_1(X20,k1_zfmisc_1(X19))
      | k3_subset_1(X19,X20) = k4_xboole_0(X19,X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

cnf(c_0_54,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,X3)
    | ~ r1_tarski(X2,X3) ),
    inference(spm,[status(thm)],[c_0_32,c_0_47])).

cnf(c_0_55,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_38])).

cnf(c_0_56,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_35]),c_0_35])])).

fof(c_0_57,negated_conjecture,
    ( v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & k2_tops_1(esk1_0,k2_tops_1(esk1_0,k2_tops_1(esk1_0,esk2_0))) != k2_tops_1(esk1_0,k2_tops_1(esk1_0,esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_51])])])).

cnf(c_0_58,plain,
    ( k3_subset_1(X2,k3_subset_1(X2,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_59,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_60,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3))
    | ~ r1_tarski(X3,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_56])).

cnf(c_0_61,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_62,plain,
    ( k3_subset_1(X1,k4_xboole_0(X1,X2)) = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_63,negated_conjecture,
    ( k4_xboole_0(esk2_0,X1) = k1_xboole_0
    | ~ r1_tarski(u1_struct_0(esk1_0),X1) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

fof(c_0_64,plain,(
    ! [X21,X22] :
      ( ~ m1_subset_1(X22,k1_zfmisc_1(X21))
      | m1_subset_1(k3_subset_1(X21,X22),k1_zfmisc_1(X21)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).

cnf(c_0_65,plain,
    ( k3_subset_1(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1))) = k4_xboole_0(X1,X2)
    | ~ m1_subset_1(k4_xboole_0(X1,X2),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_33])).

cnf(c_0_66,negated_conjecture,
    ( k4_xboole_0(esk2_0,u1_struct_0(esk1_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_63,c_0_35])).

cnf(c_0_67,plain,
    ( m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

fof(c_0_68,plain,(
    ! [X40,X41] :
      ( ~ l1_pre_topc(X40)
      | ~ m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(X40)))
      | k2_tops_1(X40,X41) = k2_tops_1(X40,k3_subset_1(u1_struct_0(X40),X41)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t62_tops_1])])])).

cnf(c_0_69,negated_conjecture,
    ( k3_subset_1(u1_struct_0(esk1_0),esk2_0) = k4_xboole_0(u1_struct_0(esk1_0),esk2_0)
    | ~ m1_subset_1(k4_xboole_0(u1_struct_0(esk1_0),esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_38])).

cnf(c_0_70,plain,
    ( m1_subset_1(k4_xboole_0(X1,X2),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_67,c_0_59])).

fof(c_0_71,plain,(
    ! [X32,X33] :
      ( ~ l1_pre_topc(X32)
      | ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))
      | m1_subset_1(k2_tops_1(X32,X33),k1_zfmisc_1(u1_struct_0(X32))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_tops_1])])).

cnf(c_0_72,plain,
    ( k2_tops_1(X1,X2) = k2_tops_1(X1,k3_subset_1(u1_struct_0(X1),X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_73,negated_conjecture,
    ( k3_subset_1(u1_struct_0(esk1_0),esk2_0) = k4_xboole_0(u1_struct_0(esk1_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_61])])).

cnf(c_0_74,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_75,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_76,plain,
    ( r1_tarski(X1,X2)
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_77,plain,(
    ! [X42,X43] :
      ( ~ l1_pre_topc(X42)
      | ~ m1_subset_1(X43,k1_zfmisc_1(u1_struct_0(X42)))
      | ~ v4_pre_topc(X43,X42)
      | r1_tarski(k2_tops_1(X42,X43),X43) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t69_tops_1])])])).

cnf(c_0_78,plain,
    ( m1_subset_1(k2_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_79,negated_conjecture,
    ( k2_tops_1(esk1_0,k4_xboole_0(u1_struct_0(esk1_0),esk2_0)) = k2_tops_1(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_74]),c_0_61])])).

cnf(c_0_80,plain,
    ( X1 = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_75,c_0_43])).

cnf(c_0_81,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | k4_xboole_0(k4_xboole_0(X1,X2),X3) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_76,c_0_32])).

fof(c_0_82,plain,(
    ! [X25,X26,X27] :
      ( ~ m1_subset_1(X26,k1_zfmisc_1(X25))
      | k7_subset_1(X25,X26,X27) = k4_xboole_0(X26,X27) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).

fof(c_0_83,plain,(
    ! [X44,X45] :
      ( ~ l1_pre_topc(X44)
      | ~ m1_subset_1(X45,k1_zfmisc_1(u1_struct_0(X44)))
      | k1_tops_1(X44,X45) = k7_subset_1(u1_struct_0(X44),X45,k2_tops_1(X44,X45)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t74_tops_1])])])).

cnf(c_0_84,plain,
    ( r1_tarski(k2_tops_1(X1,X2),X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_77])).

cnf(c_0_85,negated_conjecture,
    ( m1_subset_1(k2_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(k4_xboole_0(u1_struct_0(esk1_0),esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_74])])).

cnf(c_0_86,plain,
    ( X1 = k2_xboole_0(X2,X3)
    | k4_xboole_0(k4_xboole_0(X1,X2),X3) != k1_xboole_0
    | ~ m1_subset_1(k2_xboole_0(X2,X3),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_80,c_0_81])).

cnf(c_0_87,plain,
    ( k7_subset_1(X2,X1,X3) = k4_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_82])).

cnf(c_0_88,plain,
    ( k1_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_83])).

cnf(c_0_89,plain,
    ( r1_tarski(k2_tops_1(X1,k2_tops_1(X1,X2)),k2_tops_1(X1,X2))
    | ~ v4_pre_topc(k2_tops_1(X1,X2),X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_84,c_0_78])).

cnf(c_0_90,negated_conjecture,
    ( m1_subset_1(k2_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_70]),c_0_61])])).

cnf(c_0_91,plain,
    ( X1 = X2
    | k4_xboole_0(X1,X2) != k1_xboole_0
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_49]),c_0_38])).

cnf(c_0_92,plain,
    ( k1_tops_1(X1,X2) = k4_xboole_0(X2,k2_tops_1(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_87,c_0_88])).

cnf(c_0_93,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_94,negated_conjecture,
    ( r1_tarski(k2_tops_1(esk1_0,k2_tops_1(esk1_0,k2_tops_1(esk1_0,esk2_0))),k2_tops_1(esk1_0,k2_tops_1(esk1_0,esk2_0)))
    | ~ v4_pre_topc(k2_tops_1(esk1_0,k2_tops_1(esk1_0,esk2_0)),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_90]),c_0_74])])).

fof(c_0_95,plain,(
    ! [X34,X35] :
      ( ~ v2_pre_topc(X34)
      | ~ l1_pre_topc(X34)
      | ~ m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X34)))
      | v4_pre_topc(k2_pre_topc(X34,X35),X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_tops_1])])).

fof(c_0_96,plain,(
    ! [X36,X37] :
      ( ~ v2_pre_topc(X36)
      | ~ l1_pre_topc(X36)
      | ~ m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X36)))
      | k2_pre_topc(X36,k2_tops_1(X36,X37)) = k2_tops_1(X36,X37) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l79_tops_1])])])).

cnf(c_0_97,plain,
    ( k2_tops_1(X1,X2) = X2
    | k1_tops_1(X1,X2) != k1_xboole_0
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(k2_tops_1(X1,X2),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_91,c_0_92])).

cnf(c_0_98,negated_conjecture,
    ( m1_subset_1(k2_tops_1(esk1_0,k2_tops_1(esk1_0,k2_tops_1(esk1_0,esk2_0))),k1_zfmisc_1(k2_tops_1(esk1_0,k2_tops_1(esk1_0,esk2_0))))
    | ~ v4_pre_topc(k2_tops_1(esk1_0,k2_tops_1(esk1_0,esk2_0)),esk1_0) ),
    inference(spm,[status(thm)],[c_0_93,c_0_94])).

cnf(c_0_99,negated_conjecture,
    ( k2_tops_1(esk1_0,k2_tops_1(esk1_0,k2_tops_1(esk1_0,esk2_0))) != k2_tops_1(esk1_0,k2_tops_1(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_100,plain,
    ( v4_pre_topc(k2_pre_topc(X1,X2),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_95])).

cnf(c_0_101,plain,
    ( k2_pre_topc(X1,k2_tops_1(X1,X2)) = k2_tops_1(X1,X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_96])).

cnf(c_0_102,negated_conjecture,
    ( k1_tops_1(esk1_0,k2_tops_1(esk1_0,k2_tops_1(esk1_0,esk2_0))) != k1_xboole_0
    | ~ v4_pre_topc(k2_tops_1(esk1_0,k2_tops_1(esk1_0,esk2_0)),esk1_0)
    | ~ m1_subset_1(k2_tops_1(esk1_0,k2_tops_1(esk1_0,esk2_0)),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_98]),c_0_74])]),c_0_99])).

cnf(c_0_103,plain,
    ( v4_pre_topc(k2_tops_1(X1,X2),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_101]),c_0_78])).

cnf(c_0_104,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

fof(c_0_105,plain,(
    ! [X38,X39] :
      ( ~ v2_pre_topc(X38)
      | ~ l1_pre_topc(X38)
      | ~ m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(X38)))
      | k1_tops_1(X38,k2_tops_1(X38,k2_tops_1(X38,X39))) = k1_xboole_0 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l80_tops_1])])])).

cnf(c_0_106,negated_conjecture,
    ( k1_tops_1(esk1_0,k2_tops_1(esk1_0,k2_tops_1(esk1_0,esk2_0))) != k1_xboole_0
    | ~ m1_subset_1(k2_tops_1(esk1_0,k2_tops_1(esk1_0,esk2_0)),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_103]),c_0_104]),c_0_74]),c_0_90])])).

cnf(c_0_107,plain,
    ( k1_tops_1(X1,k2_tops_1(X1,k2_tops_1(X1,X2))) = k1_xboole_0
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_105])).

cnf(c_0_108,negated_conjecture,
    ( ~ m1_subset_1(k2_tops_1(esk1_0,k2_tops_1(esk1_0,esk2_0)),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_107]),c_0_104]),c_0_74]),c_0_61])])).

cnf(c_0_109,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_78]),c_0_74]),c_0_90])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n005.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 17:54:47 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.98/1.14  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.98/1.14  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.98/1.14  #
% 0.98/1.14  # Preprocessing time       : 0.028 s
% 0.98/1.14  # Presaturation interreduction done
% 0.98/1.14  
% 0.98/1.14  # Proof found!
% 0.98/1.14  # SZS status Theorem
% 0.98/1.14  # SZS output start CNFRefutation
% 0.98/1.14  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.98/1.14  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.98/1.14  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.98/1.14  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.98/1.14  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.98/1.14  fof(t41_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 0.98/1.14  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.98/1.14  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.98/1.14  fof(t75_tops_1, conjecture, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k2_tops_1(X1,k2_tops_1(X1,k2_tops_1(X1,X2)))=k2_tops_1(X1,k2_tops_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_tops_1)).
% 0.98/1.14  fof(involutiveness_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,k3_subset_1(X1,X2))=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 0.98/1.14  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 0.98/1.14  fof(dt_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 0.98/1.14  fof(t62_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k2_tops_1(X1,X2)=k2_tops_1(X1,k3_subset_1(u1_struct_0(X1),X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_tops_1)).
% 0.98/1.14  fof(dt_k2_tops_1, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>m1_subset_1(k2_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 0.98/1.14  fof(t69_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v4_pre_topc(X2,X1)=>r1_tarski(k2_tops_1(X1,X2),X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_tops_1)).
% 0.98/1.14  fof(redefinition_k7_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k7_subset_1(X1,X2,X3)=k4_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 0.98/1.14  fof(t74_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k1_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_tops_1)).
% 0.98/1.14  fof(fc1_tops_1, axiom, ![X1, X2]:(((v2_pre_topc(X1)&l1_pre_topc(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>v4_pre_topc(k2_pre_topc(X1,X2),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_tops_1)).
% 0.98/1.14  fof(l79_tops_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k2_pre_topc(X1,k2_tops_1(X1,X2))=k2_tops_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l79_tops_1)).
% 0.98/1.14  fof(l80_tops_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k1_tops_1(X1,k2_tops_1(X1,k2_tops_1(X1,X2)))=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l80_tops_1)).
% 0.98/1.14  fof(c_0_20, plain, ![X12, X13]:(~r1_tarski(X12,X13)|k3_xboole_0(X12,X13)=X12), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.98/1.14  fof(c_0_21, plain, ![X17, X18]:k4_xboole_0(X17,k4_xboole_0(X17,X18))=k3_xboole_0(X17,X18), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.98/1.14  fof(c_0_22, plain, ![X4, X5]:k3_xboole_0(X4,X5)=k3_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.98/1.14  cnf(c_0_23, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.98/1.14  cnf(c_0_24, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.98/1.14  fof(c_0_25, plain, ![X8, X9]:((k4_xboole_0(X8,X9)!=k1_xboole_0|r1_tarski(X8,X9))&(~r1_tarski(X8,X9)|k4_xboole_0(X8,X9)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.98/1.14  fof(c_0_26, plain, ![X6, X7]:(((r1_tarski(X6,X7)|X6!=X7)&(r1_tarski(X7,X6)|X6!=X7))&(~r1_tarski(X6,X7)|~r1_tarski(X7,X6)|X6=X7)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.98/1.14  fof(c_0_27, plain, ![X14, X15, X16]:k4_xboole_0(k4_xboole_0(X14,X15),X16)=k4_xboole_0(X14,k2_xboole_0(X15,X16)), inference(variable_rename,[status(thm)],[t41_xboole_1])).
% 0.98/1.14  cnf(c_0_28, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.98/1.14  cnf(c_0_29, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=X1|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_23, c_0_24])).
% 0.98/1.14  cnf(c_0_30, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.98/1.14  cnf(c_0_31, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.98/1.14  cnf(c_0_32, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.98/1.14  cnf(c_0_33, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k4_xboole_0(X2,k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_24]), c_0_24])).
% 0.98/1.14  cnf(c_0_34, plain, (k4_xboole_0(X1,k1_xboole_0)=X1|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.98/1.14  cnf(c_0_35, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_31])).
% 0.98/1.14  cnf(c_0_36, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k1_xboole_0|~r1_tarski(X1,k2_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_30, c_0_32])).
% 0.98/1.14  cnf(c_0_37, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k1_xboole_0|~r1_tarski(X2,k4_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_30, c_0_33])).
% 0.98/1.14  cnf(c_0_38, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.98/1.14  fof(c_0_39, plain, ![X28, X29]:((~m1_subset_1(X28,k1_zfmisc_1(X29))|r1_tarski(X28,X29))&(~r1_tarski(X28,X29)|m1_subset_1(X28,k1_zfmisc_1(X29)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.98/1.14  cnf(c_0_40, plain, (k4_xboole_0(k4_xboole_0(k2_xboole_0(X1,X2),X1),X2)=k1_xboole_0), inference(spm,[status(thm)],[c_0_36, c_0_35])).
% 0.98/1.14  cnf(c_0_41, plain, (k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_35])])).
% 0.98/1.14  fof(c_0_42, plain, ![X10, X11]:(~r1_tarski(X10,X11)|k2_xboole_0(X10,X11)=X11), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.98/1.14  cnf(c_0_43, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.98/1.14  cnf(c_0_44, plain, (k4_xboole_0(k2_xboole_0(k1_xboole_0,X1),X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_40, c_0_38])).
% 0.98/1.14  cnf(c_0_45, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_41]), c_0_38])).
% 0.98/1.14  cnf(c_0_46, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0|~r1_tarski(k2_xboole_0(X2,X1),X2)), inference(spm,[status(thm)],[c_0_40, c_0_30])).
% 0.98/1.14  cnf(c_0_47, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.98/1.14  cnf(c_0_48, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k2_xboole_0(X2,X3)))), inference(spm,[status(thm)],[c_0_36, c_0_43])).
% 0.98/1.14  cnf(c_0_49, plain, (k2_xboole_0(k1_xboole_0,X1)=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_44]), c_0_38]), c_0_32]), c_0_38]), c_0_45]), c_0_38])).
% 0.98/1.14  cnf(c_0_50, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.98/1.14  fof(c_0_51, negated_conjecture, ~(![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k2_tops_1(X1,k2_tops_1(X1,k2_tops_1(X1,X2)))=k2_tops_1(X1,k2_tops_1(X1,X2))))), inference(assume_negation,[status(cth)],[t75_tops_1])).
% 0.98/1.14  fof(c_0_52, plain, ![X23, X24]:(~m1_subset_1(X24,k1_zfmisc_1(X23))|k3_subset_1(X23,k3_subset_1(X23,X24))=X24), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).
% 0.98/1.14  fof(c_0_53, plain, ![X19, X20]:(~m1_subset_1(X20,k1_zfmisc_1(X19))|k3_subset_1(X19,X20)=k4_xboole_0(X19,X20)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 0.98/1.14  cnf(c_0_54, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,X3)|~r1_tarski(X2,X3)), inference(spm,[status(thm)],[c_0_32, c_0_47])).
% 0.98/1.14  cnf(c_0_55, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_38])).
% 0.98/1.14  cnf(c_0_56, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_35]), c_0_35])])).
% 0.98/1.14  fof(c_0_57, negated_conjecture, ((v2_pre_topc(esk1_0)&l1_pre_topc(esk1_0))&(m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&k2_tops_1(esk1_0,k2_tops_1(esk1_0,k2_tops_1(esk1_0,esk2_0)))!=k2_tops_1(esk1_0,k2_tops_1(esk1_0,esk2_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_51])])])).
% 0.98/1.14  cnf(c_0_58, plain, (k3_subset_1(X2,k3_subset_1(X2,X1))=X1|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.98/1.14  cnf(c_0_59, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.98/1.14  cnf(c_0_60, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(X3))|~r1_tarski(X3,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_56])).
% 0.98/1.14  cnf(c_0_61, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.98/1.14  cnf(c_0_62, plain, (k3_subset_1(X1,k4_xboole_0(X1,X2))=X2|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.98/1.14  cnf(c_0_63, negated_conjecture, (k4_xboole_0(esk2_0,X1)=k1_xboole_0|~r1_tarski(u1_struct_0(esk1_0),X1)), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.98/1.14  fof(c_0_64, plain, ![X21, X22]:(~m1_subset_1(X22,k1_zfmisc_1(X21))|m1_subset_1(k3_subset_1(X21,X22),k1_zfmisc_1(X21))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).
% 0.98/1.14  cnf(c_0_65, plain, (k3_subset_1(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1)))=k4_xboole_0(X1,X2)|~m1_subset_1(k4_xboole_0(X1,X2),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_62, c_0_33])).
% 0.98/1.14  cnf(c_0_66, negated_conjecture, (k4_xboole_0(esk2_0,u1_struct_0(esk1_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_63, c_0_35])).
% 0.98/1.14  cnf(c_0_67, plain, (m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.98/1.14  fof(c_0_68, plain, ![X40, X41]:(~l1_pre_topc(X40)|(~m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(X40)))|k2_tops_1(X40,X41)=k2_tops_1(X40,k3_subset_1(u1_struct_0(X40),X41)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t62_tops_1])])])).
% 0.98/1.14  cnf(c_0_69, negated_conjecture, (k3_subset_1(u1_struct_0(esk1_0),esk2_0)=k4_xboole_0(u1_struct_0(esk1_0),esk2_0)|~m1_subset_1(k4_xboole_0(u1_struct_0(esk1_0),esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_38])).
% 0.98/1.14  cnf(c_0_70, plain, (m1_subset_1(k4_xboole_0(X1,X2),k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_67, c_0_59])).
% 0.98/1.14  fof(c_0_71, plain, ![X32, X33]:(~l1_pre_topc(X32)|~m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))|m1_subset_1(k2_tops_1(X32,X33),k1_zfmisc_1(u1_struct_0(X32)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_tops_1])])).
% 0.98/1.14  cnf(c_0_72, plain, (k2_tops_1(X1,X2)=k2_tops_1(X1,k3_subset_1(u1_struct_0(X1),X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.98/1.14  cnf(c_0_73, negated_conjecture, (k3_subset_1(u1_struct_0(esk1_0),esk2_0)=k4_xboole_0(u1_struct_0(esk1_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_61])])).
% 0.98/1.14  cnf(c_0_74, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.98/1.14  cnf(c_0_75, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.98/1.14  cnf(c_0_76, plain, (r1_tarski(X1,X2)|k4_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.98/1.14  fof(c_0_77, plain, ![X42, X43]:(~l1_pre_topc(X42)|(~m1_subset_1(X43,k1_zfmisc_1(u1_struct_0(X42)))|(~v4_pre_topc(X43,X42)|r1_tarski(k2_tops_1(X42,X43),X43)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t69_tops_1])])])).
% 0.98/1.14  cnf(c_0_78, plain, (m1_subset_1(k2_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_71])).
% 0.98/1.14  cnf(c_0_79, negated_conjecture, (k2_tops_1(esk1_0,k4_xboole_0(u1_struct_0(esk1_0),esk2_0))=k2_tops_1(esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_73]), c_0_74]), c_0_61])])).
% 0.98/1.14  cnf(c_0_80, plain, (X1=X2|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_75, c_0_43])).
% 0.98/1.14  cnf(c_0_81, plain, (r1_tarski(X1,k2_xboole_0(X2,X3))|k4_xboole_0(k4_xboole_0(X1,X2),X3)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_76, c_0_32])).
% 0.98/1.14  fof(c_0_82, plain, ![X25, X26, X27]:(~m1_subset_1(X26,k1_zfmisc_1(X25))|k7_subset_1(X25,X26,X27)=k4_xboole_0(X26,X27)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).
% 0.98/1.14  fof(c_0_83, plain, ![X44, X45]:(~l1_pre_topc(X44)|(~m1_subset_1(X45,k1_zfmisc_1(u1_struct_0(X44)))|k1_tops_1(X44,X45)=k7_subset_1(u1_struct_0(X44),X45,k2_tops_1(X44,X45)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t74_tops_1])])])).
% 0.98/1.14  cnf(c_0_84, plain, (r1_tarski(k2_tops_1(X1,X2),X2)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v4_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_77])).
% 0.98/1.14  cnf(c_0_85, negated_conjecture, (m1_subset_1(k2_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(k4_xboole_0(u1_struct_0(esk1_0),esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_79]), c_0_74])])).
% 0.98/1.14  cnf(c_0_86, plain, (X1=k2_xboole_0(X2,X3)|k4_xboole_0(k4_xboole_0(X1,X2),X3)!=k1_xboole_0|~m1_subset_1(k2_xboole_0(X2,X3),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_80, c_0_81])).
% 0.98/1.14  cnf(c_0_87, plain, (k7_subset_1(X2,X1,X3)=k4_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_82])).
% 0.98/1.14  cnf(c_0_88, plain, (k1_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_83])).
% 0.98/1.14  cnf(c_0_89, plain, (r1_tarski(k2_tops_1(X1,k2_tops_1(X1,X2)),k2_tops_1(X1,X2))|~v4_pre_topc(k2_tops_1(X1,X2),X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_84, c_0_78])).
% 0.98/1.14  cnf(c_0_90, negated_conjecture, (m1_subset_1(k2_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_70]), c_0_61])])).
% 0.98/1.14  cnf(c_0_91, plain, (X1=X2|k4_xboole_0(X1,X2)!=k1_xboole_0|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_49]), c_0_38])).
% 0.98/1.14  cnf(c_0_92, plain, (k1_tops_1(X1,X2)=k4_xboole_0(X2,k2_tops_1(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_87, c_0_88])).
% 0.98/1.14  cnf(c_0_93, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.98/1.14  cnf(c_0_94, negated_conjecture, (r1_tarski(k2_tops_1(esk1_0,k2_tops_1(esk1_0,k2_tops_1(esk1_0,esk2_0))),k2_tops_1(esk1_0,k2_tops_1(esk1_0,esk2_0)))|~v4_pre_topc(k2_tops_1(esk1_0,k2_tops_1(esk1_0,esk2_0)),esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_90]), c_0_74])])).
% 0.98/1.14  fof(c_0_95, plain, ![X34, X35]:(~v2_pre_topc(X34)|~l1_pre_topc(X34)|~m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X34)))|v4_pre_topc(k2_pre_topc(X34,X35),X34)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_tops_1])])).
% 0.98/1.14  fof(c_0_96, plain, ![X36, X37]:(~v2_pre_topc(X36)|~l1_pre_topc(X36)|(~m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X36)))|k2_pre_topc(X36,k2_tops_1(X36,X37))=k2_tops_1(X36,X37))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l79_tops_1])])])).
% 0.98/1.14  cnf(c_0_97, plain, (k2_tops_1(X1,X2)=X2|k1_tops_1(X1,X2)!=k1_xboole_0|~l1_pre_topc(X1)|~m1_subset_1(k2_tops_1(X1,X2),k1_zfmisc_1(X2))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_91, c_0_92])).
% 0.98/1.14  cnf(c_0_98, negated_conjecture, (m1_subset_1(k2_tops_1(esk1_0,k2_tops_1(esk1_0,k2_tops_1(esk1_0,esk2_0))),k1_zfmisc_1(k2_tops_1(esk1_0,k2_tops_1(esk1_0,esk2_0))))|~v4_pre_topc(k2_tops_1(esk1_0,k2_tops_1(esk1_0,esk2_0)),esk1_0)), inference(spm,[status(thm)],[c_0_93, c_0_94])).
% 0.98/1.14  cnf(c_0_99, negated_conjecture, (k2_tops_1(esk1_0,k2_tops_1(esk1_0,k2_tops_1(esk1_0,esk2_0)))!=k2_tops_1(esk1_0,k2_tops_1(esk1_0,esk2_0))), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.98/1.14  cnf(c_0_100, plain, (v4_pre_topc(k2_pre_topc(X1,X2),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_95])).
% 0.98/1.14  cnf(c_0_101, plain, (k2_pre_topc(X1,k2_tops_1(X1,X2))=k2_tops_1(X1,X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_96])).
% 0.98/1.14  cnf(c_0_102, negated_conjecture, (k1_tops_1(esk1_0,k2_tops_1(esk1_0,k2_tops_1(esk1_0,esk2_0)))!=k1_xboole_0|~v4_pre_topc(k2_tops_1(esk1_0,k2_tops_1(esk1_0,esk2_0)),esk1_0)|~m1_subset_1(k2_tops_1(esk1_0,k2_tops_1(esk1_0,esk2_0)),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97, c_0_98]), c_0_74])]), c_0_99])).
% 0.98/1.14  cnf(c_0_103, plain, (v4_pre_topc(k2_tops_1(X1,X2),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_101]), c_0_78])).
% 0.98/1.14  cnf(c_0_104, negated_conjecture, (v2_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.98/1.14  fof(c_0_105, plain, ![X38, X39]:(~v2_pre_topc(X38)|~l1_pre_topc(X38)|(~m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(X38)))|k1_tops_1(X38,k2_tops_1(X38,k2_tops_1(X38,X39)))=k1_xboole_0)), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l80_tops_1])])])).
% 0.98/1.14  cnf(c_0_106, negated_conjecture, (k1_tops_1(esk1_0,k2_tops_1(esk1_0,k2_tops_1(esk1_0,esk2_0)))!=k1_xboole_0|~m1_subset_1(k2_tops_1(esk1_0,k2_tops_1(esk1_0,esk2_0)),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102, c_0_103]), c_0_104]), c_0_74]), c_0_90])])).
% 0.98/1.14  cnf(c_0_107, plain, (k1_tops_1(X1,k2_tops_1(X1,k2_tops_1(X1,X2)))=k1_xboole_0|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_105])).
% 0.98/1.14  cnf(c_0_108, negated_conjecture, (~m1_subset_1(k2_tops_1(esk1_0,k2_tops_1(esk1_0,esk2_0)),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106, c_0_107]), c_0_104]), c_0_74]), c_0_61])])).
% 0.98/1.14  cnf(c_0_109, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108, c_0_78]), c_0_74]), c_0_90])]), ['proof']).
% 0.98/1.14  # SZS output end CNFRefutation
% 0.98/1.14  # Proof object total steps             : 110
% 0.98/1.14  # Proof object clause steps            : 69
% 0.98/1.14  # Proof object formula steps           : 41
% 0.98/1.14  # Proof object conjectures             : 20
% 0.98/1.14  # Proof object clause conjectures      : 17
% 0.98/1.14  # Proof object formula conjectures     : 3
% 0.98/1.14  # Proof object initial clauses used    : 26
% 0.98/1.14  # Proof object initial formulas used   : 20
% 0.98/1.14  # Proof object generating inferences   : 40
% 0.98/1.14  # Proof object simplifying inferences  : 44
% 0.98/1.14  # Training examples: 0 positive, 0 negative
% 0.98/1.14  # Parsed axioms                        : 21
% 0.98/1.14  # Removed by relevancy pruning/SinE    : 0
% 0.98/1.14  # Initial clauses                      : 28
% 0.98/1.14  # Removed in clause preprocessing      : 1
% 0.98/1.14  # Initial clauses in saturation        : 27
% 0.98/1.14  # Processed clauses                    : 7604
% 0.98/1.14  # ...of these trivial                  : 44
% 0.98/1.14  # ...subsumed                          : 6401
% 0.98/1.14  # ...remaining for further processing  : 1159
% 0.98/1.14  # Other redundant clauses eliminated   : 1057
% 0.98/1.14  # Clauses deleted for lack of memory   : 0
% 0.98/1.14  # Backward-subsumed                    : 103
% 0.98/1.14  # Backward-rewritten                   : 45
% 0.98/1.14  # Generated clauses                    : 73257
% 0.98/1.14  # ...of the previous two non-trivial   : 63893
% 0.98/1.14  # Contextual simplify-reflections      : 36
% 0.98/1.14  # Paramodulations                      : 72200
% 0.98/1.14  # Factorizations                       : 0
% 0.98/1.14  # Equation resolutions                 : 1057
% 0.98/1.14  # Propositional unsat checks           : 0
% 0.98/1.14  #    Propositional check models        : 0
% 0.98/1.14  #    Propositional check unsatisfiable : 0
% 0.98/1.14  #    Propositional clauses             : 0
% 0.98/1.14  #    Propositional clauses after purity: 0
% 0.98/1.14  #    Propositional unsat core size     : 0
% 0.98/1.14  #    Propositional preprocessing time  : 0.000
% 0.98/1.14  #    Propositional encoding time       : 0.000
% 0.98/1.14  #    Propositional solver time         : 0.000
% 0.98/1.14  #    Success case prop preproc time    : 0.000
% 0.98/1.14  #    Success case prop encoding time   : 0.000
% 0.98/1.14  #    Success case prop solver time     : 0.000
% 0.98/1.14  # Current number of processed clauses  : 983
% 0.98/1.14  #    Positive orientable unit clauses  : 47
% 0.98/1.14  #    Positive unorientable unit clauses: 5
% 0.98/1.14  #    Negative unit clauses             : 33
% 0.98/1.14  #    Non-unit-clauses                  : 898
% 0.98/1.14  # Current number of unprocessed clauses: 55861
% 0.98/1.14  # ...number of literals in the above   : 199311
% 0.98/1.14  # Current number of archived formulas  : 0
% 0.98/1.14  # Current number of archived clauses   : 175
% 0.98/1.14  # Clause-clause subsumption calls (NU) : 157582
% 0.98/1.14  # Rec. Clause-clause subsumption calls : 102466
% 0.98/1.14  # Non-unit clause-clause subsumptions  : 4127
% 0.98/1.14  # Unit Clause-clause subsumption calls : 2687
% 0.98/1.14  # Rewrite failures with RHS unbound    : 0
% 0.98/1.14  # BW rewrite match attempts            : 125
% 0.98/1.14  # BW rewrite match successes           : 35
% 0.98/1.14  # Condensation attempts                : 0
% 0.98/1.14  # Condensation successes               : 0
% 0.98/1.14  # Termbank termtop insertions          : 1149521
% 0.98/1.14  
% 0.98/1.14  # -------------------------------------------------
% 0.98/1.14  # User time                : 0.777 s
% 0.98/1.14  # System time              : 0.031 s
% 0.98/1.14  # Total time               : 0.808 s
% 0.98/1.14  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
