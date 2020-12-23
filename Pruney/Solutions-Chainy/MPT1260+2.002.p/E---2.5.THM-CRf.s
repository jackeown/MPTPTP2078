%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:11:15 EST 2020

% Result     : Theorem 1.81s
% Output     : CNFRefutation 1.81s
% Verified   : 
% Statistics : Number of formulae       :  200 (8519 expanded)
%              Number of clauses        :  131 (3827 expanded)
%              Number of leaves         :   34 (2270 expanded)
%              Depth                    :   20
%              Number of atoms          :  355 (12264 expanded)
%              Number of equality atoms :  132 (7450 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t46_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(dt_k6_subset_1,axiom,(
    ! [X1,X2] : m1_subset_1(k6_subset_1(X1,X2),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).

fof(redefinition_k6_subset_1,axiom,(
    ! [X1,X2] : k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(t52_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(X1,k4_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(involutiveness_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,k3_subset_1(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(redefinition_k4_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => k4_subset_1(X1,X2,X3) = k2_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(t76_tops_1,conjecture,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_pre_topc(X2,X1)
          <=> k2_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tops_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(dt_k4_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => m1_subset_1(k4_subset_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_subset_1)).

fof(t62_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k2_tops_1(X1,X2) = k2_tops_1(X1,k3_subset_1(u1_struct_0(X1),X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_tops_1)).

fof(dt_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(dt_k2_tops_1,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k2_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(t65_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k2_pre_topc(X1,X2) = k4_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

fof(redefinition_k7_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k7_subset_1(X1,X2,X3) = k4_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t3_xboole_1,axiom,(
    ! [X1] :
      ( r1_tarski(X1,k1_xboole_0)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(t74_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k1_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

fof(t32_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => k7_subset_1(X1,X2,X3) = k9_subset_1(X1,X2,k3_subset_1(X1,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_subset_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t56_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( ( v3_pre_topc(X2,X1)
                  & r1_tarski(X2,X3) )
               => r1_tarski(X2,k1_tops_1(X1,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tops_1)).

fof(idempotence_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k9_subset_1)).

fof(existence_m1_subset_1,axiom,(
    ! [X1] :
    ? [X2] : m1_subset_1(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(fc9_tops_1,axiom,(
    ! [X1,X2] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => v3_pre_topc(k1_tops_1(X1,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

fof(l78_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k2_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k1_tops_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

fof(c_0_34,plain,(
    ! [X15,X16] : k4_xboole_0(X15,X16) = k5_xboole_0(X15,k3_xboole_0(X15,X16)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_35,plain,(
    ! [X74,X75] : k1_setfam_1(k2_tarski(X74,X75)) = k3_xboole_0(X74,X75) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_36,plain,(
    ! [X35,X36] : k4_xboole_0(X35,k2_xboole_0(X35,X36)) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t46_xboole_1])).

cnf(c_0_37,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_38,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

fof(c_0_39,plain,(
    ! [X12] : k3_xboole_0(X12,X12) = X12 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

fof(c_0_40,plain,(
    ! [X51,X52] : m1_subset_1(k6_subset_1(X51,X52),k1_zfmisc_1(X51)) ),
    inference(variable_rename,[status(thm)],[dt_k6_subset_1])).

fof(c_0_41,plain,(
    ! [X66,X67] : k6_subset_1(X66,X67) = k4_xboole_0(X66,X67) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).

fof(c_0_42,plain,(
    ! [X27] : k4_xboole_0(X27,k1_xboole_0) = X27 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

fof(c_0_43,plain,(
    ! [X44,X45] :
      ( ~ m1_subset_1(X45,k1_zfmisc_1(X44))
      | k3_subset_1(X44,X45) = k4_xboole_0(X44,X45) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

fof(c_0_44,plain,(
    ! [X37,X38,X39] : k4_xboole_0(X37,k4_xboole_0(X38,X39)) = k2_xboole_0(k4_xboole_0(X37,X38),k3_xboole_0(X37,X39)) ),
    inference(variable_rename,[status(thm)],[t52_xboole_1])).

cnf(c_0_45,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_46,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_37,c_0_38])).

fof(c_0_47,plain,(
    ! [X19] : k2_xboole_0(X19,k1_xboole_0) = X19 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

cnf(c_0_48,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

fof(c_0_49,plain,(
    ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_50,plain,
    ( m1_subset_1(k6_subset_1(X1,X2),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_51,plain,
    ( k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_52,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

fof(c_0_53,plain,(
    ! [X58,X59] :
      ( ~ m1_subset_1(X59,k1_zfmisc_1(X58))
      | k3_subset_1(X58,k3_subset_1(X58,X59)) = X59 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).

cnf(c_0_54,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_55,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_56,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k2_xboole_0(X1,X2)))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_57,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_58,plain,
    ( k1_setfam_1(k2_tarski(X1,X1)) = X1 ),
    inference(rw,[status(thm)],[c_0_48,c_0_38])).

cnf(c_0_59,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

fof(c_0_60,plain,(
    ! [X63,X64,X65] :
      ( ~ m1_subset_1(X64,k1_zfmisc_1(X63))
      | ~ m1_subset_1(X65,k1_zfmisc_1(X63))
      | k4_subset_1(X63,X64,X65) = k2_xboole_0(X64,X65) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).

cnf(c_0_61,plain,
    ( m1_subset_1(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50,c_0_51]),c_0_46])).

cnf(c_0_62,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k1_xboole_0))) = X1 ),
    inference(rw,[status(thm)],[c_0_52,c_0_46])).

fof(c_0_63,negated_conjecture,(
    ~ ! [X1] :
        ( ( v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( v3_pre_topc(X2,X1)
            <=> k2_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t76_tops_1])).

cnf(c_0_64,plain,
    ( k3_subset_1(X2,k3_subset_1(X2,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_65,plain,
    ( k3_subset_1(X2,X1) = k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_54,c_0_46])).

cnf(c_0_66,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X3)))))) = k2_xboole_0(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),k1_setfam_1(k2_tarski(X1,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55,c_0_38]),c_0_46]),c_0_46]),c_0_46])).

cnf(c_0_67,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_58])).

cnf(c_0_68,plain,
    ( k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_57,c_0_59])).

cnf(c_0_69,plain,
    ( k4_subset_1(X2,X1,X3) = k2_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_70,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

fof(c_0_71,negated_conjecture,
    ( v2_pre_topc(esk3_0)
    & l1_pre_topc(esk3_0)
    & m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))
    & ( ~ v3_pre_topc(esk4_0,esk3_0)
      | k2_tops_1(esk3_0,esk4_0) != k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),esk4_0) )
    & ( v3_pre_topc(esk4_0,esk3_0)
      | k2_tops_1(esk3_0,esk4_0) = k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),esk4_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_63])])])).

fof(c_0_72,plain,(
    ! [X76,X77] :
      ( ( ~ m1_subset_1(X76,k1_zfmisc_1(X77))
        | r1_tarski(X76,X77) )
      & ( ~ r1_tarski(X76,X77)
        | m1_subset_1(X76,k1_zfmisc_1(X77)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_73,plain,(
    ! [X48,X49,X50] :
      ( ~ m1_subset_1(X49,k1_zfmisc_1(X48))
      | ~ m1_subset_1(X50,k1_zfmisc_1(X48))
      | m1_subset_1(k4_subset_1(X48,X49,X50),k1_zfmisc_1(X48)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_subset_1])])).

cnf(c_0_74,plain,
    ( k3_subset_1(X1,k3_subset_1(X1,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))))) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_64,c_0_61])).

cnf(c_0_75,plain,
    ( k3_subset_1(X1,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))) = k1_setfam_1(k2_tarski(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_61]),c_0_66]),c_0_58]),c_0_67]),c_0_68])).

fof(c_0_76,plain,(
    ! [X87,X88] :
      ( ~ l1_pre_topc(X87)
      | ~ m1_subset_1(X88,k1_zfmisc_1(u1_struct_0(X87)))
      | k2_tops_1(X87,X88) = k2_tops_1(X87,k3_subset_1(u1_struct_0(X87),X88)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t62_tops_1])])])).

fof(c_0_77,plain,(
    ! [X46,X47] :
      ( ~ m1_subset_1(X47,k1_zfmisc_1(X46))
      | m1_subset_1(k3_subset_1(X46,X47),k1_zfmisc_1(X46)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).

cnf(c_0_78,plain,
    ( k4_subset_1(X1,X2,X1) = k2_xboole_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_79,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_80,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_81,plain,
    ( m1_subset_1(k4_subset_1(X2,X1,X3),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_82,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k3_subset_1(X1,k1_setfam_1(k2_tarski(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_74,c_0_75])).

fof(c_0_83,plain,(
    ! [X17,X18] : r1_tarski(k3_xboole_0(X17,X18),X17) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

fof(c_0_84,plain,(
    ! [X78,X79] :
      ( ~ l1_pre_topc(X78)
      | ~ m1_subset_1(X79,k1_zfmisc_1(u1_struct_0(X78)))
      | m1_subset_1(k2_tops_1(X78,X79),k1_zfmisc_1(u1_struct_0(X78))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_tops_1])])).

cnf(c_0_85,plain,
    ( k2_tops_1(X1,X2) = k2_tops_1(X1,k3_subset_1(u1_struct_0(X1),X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_76])).

cnf(c_0_86,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_87,plain,
    ( m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_77])).

cnf(c_0_88,negated_conjecture,
    ( k4_subset_1(u1_struct_0(esk3_0),esk4_0,u1_struct_0(esk3_0)) = k2_xboole_0(esk4_0,u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_78,c_0_79])).

fof(c_0_89,plain,(
    ! [X40,X41] : r1_tarski(X40,k2_xboole_0(X40,X41)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

cnf(c_0_90,plain,
    ( r1_tarski(k4_subset_1(X1,X2,X3),X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_80,c_0_81])).

cnf(c_0_91,plain,
    ( k3_subset_1(X1,k3_subset_1(X1,k1_setfam_1(k2_tarski(X1,X2)))) = k1_setfam_1(k2_tarski(X1,X2)) ),
    inference(rw,[status(thm)],[c_0_75,c_0_82])).

cnf(c_0_92,plain,
    ( m1_subset_1(k3_subset_1(X1,k1_setfam_1(k2_tarski(X1,X2))),k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_61,c_0_82])).

fof(c_0_93,plain,(
    ! [X42,X43] : k2_tarski(X42,X43) = k2_tarski(X43,X42) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

cnf(c_0_94,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_95,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k2_xboole_0(X2,X1)))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_56,c_0_59])).

cnf(c_0_96,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_61,c_0_56])).

cnf(c_0_97,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_83])).

cnf(c_0_98,plain,
    ( m1_subset_1(k2_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_84])).

cnf(c_0_99,negated_conjecture,
    ( k2_tops_1(esk3_0,k3_subset_1(u1_struct_0(esk3_0),esk4_0)) = k2_tops_1(esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_79]),c_0_86])])).

cnf(c_0_100,plain,
    ( r1_tarski(k3_subset_1(X1,X2),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_80,c_0_87])).

fof(c_0_101,plain,(
    ! [X89,X90] :
      ( ~ l1_pre_topc(X89)
      | ~ m1_subset_1(X90,k1_zfmisc_1(u1_struct_0(X89)))
      | k2_pre_topc(X89,X90) = k4_subset_1(u1_struct_0(X89),X90,k2_tops_1(X89,X90)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_tops_1])])])).

fof(c_0_102,plain,(
    ! [X68,X69,X70] :
      ( ~ m1_subset_1(X69,k1_zfmisc_1(X68))
      | k7_subset_1(X68,X69,X70) = k4_xboole_0(X69,X70) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).

fof(c_0_103,plain,(
    ! [X13,X14] :
      ( ( r1_tarski(X13,X14)
        | X13 != X14 )
      & ( r1_tarski(X14,X13)
        | X13 != X14 )
      & ( ~ r1_tarski(X13,X14)
        | ~ r1_tarski(X14,X13)
        | X13 = X14 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_104,negated_conjecture,
    ( m1_subset_1(k2_xboole_0(esk4_0,u1_struct_0(esk3_0)),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_88]),c_0_70]),c_0_79])])).

cnf(c_0_105,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_89])).

fof(c_0_106,plain,(
    ! [X28] :
      ( ~ r1_tarski(X28,k1_xboole_0)
      | X28 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).

cnf(c_0_107,plain,
    ( r1_tarski(k4_subset_1(X1,X2,X1),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_90,c_0_70])).

cnf(c_0_108,plain,
    ( m1_subset_1(k1_setfam_1(k2_tarski(X1,X2)),k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_91]),c_0_92])])).

cnf(c_0_109,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_93])).

cnf(c_0_110,plain,
    ( k3_subset_1(X1,k3_subset_1(X1,X2)) = X2
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_64,c_0_94])).

cnf(c_0_111,plain,
    ( k3_subset_1(X1,k1_setfam_1(k2_tarski(X1,k2_xboole_0(X2,X1)))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_95,c_0_82])).

cnf(c_0_112,plain,
    ( k3_subset_1(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_96]),c_0_62])).

cnf(c_0_113,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(X1,X2)),X1) ),
    inference(rw,[status(thm)],[c_0_97,c_0_38])).

cnf(c_0_114,negated_conjecture,
    ( m1_subset_1(k2_tops_1(esk3_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(esk3_0),esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_99]),c_0_86])])).

cnf(c_0_115,negated_conjecture,
    ( r1_tarski(k3_subset_1(u1_struct_0(esk3_0),esk4_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_100,c_0_79])).

cnf(c_0_116,plain,
    ( k2_pre_topc(X1,X2) = k4_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_101])).

fof(c_0_117,plain,(
    ! [X91,X92] :
      ( ~ l1_pre_topc(X91)
      | ~ m1_subset_1(X92,k1_zfmisc_1(u1_struct_0(X91)))
      | k1_tops_1(X91,X92) = k7_subset_1(u1_struct_0(X91),X92,k2_tops_1(X91,X92)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t74_tops_1])])])).

cnf(c_0_118,plain,
    ( k7_subset_1(X2,X1,X3) = k4_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_102])).

cnf(c_0_119,plain,
    ( k3_subset_1(X1,k1_setfam_1(k2_tarski(X1,k2_xboole_0(X1,X2)))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_56,c_0_82])).

cnf(c_0_120,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_103])).

cnf(c_0_121,negated_conjecture,
    ( r1_tarski(k2_xboole_0(esk4_0,u1_struct_0(esk3_0)),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_80,c_0_104])).

cnf(c_0_122,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_105,c_0_59])).

cnf(c_0_123,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_106])).

cnf(c_0_124,plain,
    ( r1_tarski(k4_subset_1(X1,X2,X1),X1)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_107,c_0_94])).

cnf(c_0_125,plain,
    ( k4_subset_1(X1,X2,X1) = k2_xboole_0(X2,X1)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_78,c_0_94])).

cnf(c_0_126,plain,
    ( m1_subset_1(k1_setfam_1(k2_tarski(X1,X2)),k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_108,c_0_109])).

cnf(c_0_127,plain,
    ( k1_setfam_1(k2_tarski(X1,k2_xboole_0(X2,X1))) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110,c_0_111]),c_0_112]),c_0_113])])).

cnf(c_0_128,negated_conjecture,
    ( m1_subset_1(k2_tops_1(esk3_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114,c_0_94]),c_0_115])])).

cnf(c_0_129,negated_conjecture,
    ( k4_subset_1(u1_struct_0(esk3_0),esk4_0,k2_tops_1(esk3_0,esk4_0)) = k2_pre_topc(esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116,c_0_79]),c_0_86])])).

cnf(c_0_130,plain,
    ( k1_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_117])).

cnf(c_0_131,plain,
    ( k7_subset_1(X2,X1,X3) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_118,c_0_46])).

cnf(c_0_132,plain,
    ( k1_setfam_1(k2_tarski(X1,k2_xboole_0(X1,X2))) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110,c_0_119]),c_0_112]),c_0_113])])).

cnf(c_0_133,negated_conjecture,
    ( k2_xboole_0(esk4_0,u1_struct_0(esk3_0)) = u1_struct_0(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120,c_0_121]),c_0_122])])).

cnf(c_0_134,plain,
    ( k1_setfam_1(k2_tarski(k1_xboole_0,X1)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_123,c_0_113])).

cnf(c_0_135,plain,
    ( r1_tarski(k2_xboole_0(X1,X2),X2)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_124,c_0_125])).

cnf(c_0_136,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_xboole_0(X2,X1))) ),
    inference(spm,[status(thm)],[c_0_126,c_0_127])).

cnf(c_0_137,negated_conjecture,
    ( k4_subset_1(u1_struct_0(esk3_0),X1,k2_tops_1(esk3_0,esk4_0)) = k2_xboole_0(X1,k2_tops_1(esk3_0,esk4_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_69,c_0_128])).

cnf(c_0_138,negated_conjecture,
    ( m1_subset_1(k2_pre_topc(esk3_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ m1_subset_1(k2_tops_1(esk3_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_129]),c_0_79])])).

cnf(c_0_139,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk3_0),esk4_0,k2_tops_1(esk3_0,esk4_0)) = k1_tops_1(esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_130,c_0_79]),c_0_86])])).

cnf(c_0_140,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk3_0),esk4_0,X1) = k5_xboole_0(esk4_0,k1_setfam_1(k2_tarski(esk4_0,X1))) ),
    inference(spm,[status(thm)],[c_0_131,c_0_79])).

cnf(c_0_141,plain,
    ( k3_subset_1(X1,k1_setfam_1(k2_tarski(X1,k3_subset_1(X2,k1_setfam_1(k2_tarski(X2,X3)))))) = k2_xboole_0(k3_subset_1(X1,k1_setfam_1(k2_tarski(X1,X2))),k1_setfam_1(k2_tarski(X1,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66,c_0_82]),c_0_82]),c_0_82])).

cnf(c_0_142,negated_conjecture,
    ( k1_setfam_1(k2_tarski(esk4_0,u1_struct_0(esk3_0))) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_132,c_0_133])).

cnf(c_0_143,plain,
    ( k3_subset_1(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_70]),c_0_58]),c_0_67])).

cnf(c_0_144,plain,
    ( k1_setfam_1(k2_tarski(X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_134,c_0_109])).

cnf(c_0_145,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120,c_0_135]),c_0_122])])).

fof(c_0_146,plain,(
    ! [X71,X72,X73] :
      ( ~ m1_subset_1(X72,k1_zfmisc_1(X71))
      | ~ m1_subset_1(X73,k1_zfmisc_1(X71))
      | k7_subset_1(X71,X72,X73) = k9_subset_1(X71,X72,k3_subset_1(X71,X73)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t32_subset_1])])])).

cnf(c_0_147,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_xboole_0(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_136,c_0_59])).

cnf(c_0_148,negated_conjecture,
    ( k2_xboole_0(esk4_0,k2_tops_1(esk3_0,esk4_0)) = k2_pre_topc(esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_137,c_0_79]),c_0_129])).

cnf(c_0_149,plain,
    ( k7_subset_1(X1,X2,X3) = k3_subset_1(X2,k1_setfam_1(k2_tarski(X2,X3)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_131,c_0_82])).

cnf(c_0_150,negated_conjecture,
    ( m1_subset_1(k2_pre_topc(esk3_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_138,c_0_128])])).

cnf(c_0_151,negated_conjecture,
    ( k5_xboole_0(esk4_0,k1_setfam_1(k2_tarski(esk4_0,k2_tops_1(esk3_0,esk4_0)))) = k1_tops_1(esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[c_0_139,c_0_140])).

fof(c_0_152,plain,(
    ! [X23,X24] : r1_tarski(k4_xboole_0(X23,X24),X23) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

fof(c_0_153,plain,(
    ! [X84,X85,X86] :
      ( ~ l1_pre_topc(X84)
      | ~ m1_subset_1(X85,k1_zfmisc_1(u1_struct_0(X84)))
      | ~ m1_subset_1(X86,k1_zfmisc_1(u1_struct_0(X84)))
      | ~ v3_pre_topc(X85,X84)
      | ~ r1_tarski(X85,X86)
      | r1_tarski(X85,k1_tops_1(X84,X86)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t56_tops_1])])])).

cnf(c_0_154,negated_conjecture,
    ( k2_xboole_0(k3_subset_1(X1,k1_setfam_1(k2_tarski(X1,esk4_0))),k1_setfam_1(k2_tarski(X1,u1_struct_0(esk3_0)))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_141,c_0_142]),c_0_143]),c_0_144]),c_0_112])).

cnf(c_0_155,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_132,c_0_145])).

cnf(c_0_156,plain,
    ( k7_subset_1(X2,X1,X3) = k9_subset_1(X2,X1,k3_subset_1(X2,X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_146])).

cnf(c_0_157,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_pre_topc(esk3_0,esk4_0))) ),
    inference(spm,[status(thm)],[c_0_147,c_0_148])).

cnf(c_0_158,negated_conjecture,
    ( v3_pre_topc(esk4_0,esk3_0)
    | k2_tops_1(esk3_0,esk4_0) = k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_159,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),X1) = k3_subset_1(k2_pre_topc(esk3_0,esk4_0),k1_setfam_1(k2_tarski(k2_pre_topc(esk3_0,esk4_0),X1))) ),
    inference(spm,[status(thm)],[c_0_149,c_0_150])).

cnf(c_0_160,negated_conjecture,
    ( k1_setfam_1(k2_tarski(esk4_0,k2_pre_topc(esk3_0,esk4_0))) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_132,c_0_148])).

fof(c_0_161,plain,(
    ! [X55,X56,X57] :
      ( ~ m1_subset_1(X57,k1_zfmisc_1(X55))
      | k9_subset_1(X55,X56,X56) = X56 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[idempotence_k9_subset_1])])).

fof(c_0_162,plain,(
    ! [X53] : m1_subset_1(esk2_1(X53),X53) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).

cnf(c_0_163,negated_conjecture,
    ( k3_subset_1(esk4_0,k1_setfam_1(k2_tarski(esk4_0,k2_tops_1(esk3_0,esk4_0)))) = k1_tops_1(esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[c_0_151,c_0_82])).

cnf(c_0_164,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_152])).

cnf(c_0_165,plain,
    ( r1_tarski(X2,k1_tops_1(X1,X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(X2,X1)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_153])).

cnf(c_0_166,negated_conjecture,
    ( k1_setfam_1(k2_tarski(X1,u1_struct_0(esk3_0))) = X1
    | ~ r1_tarski(X1,esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_154,c_0_155]),c_0_143]),c_0_68])).

cnf(c_0_167,plain,
    ( k7_subset_1(X1,X2,X3) = k9_subset_1(X1,X2,k3_subset_1(X1,X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_tarski(X3,X1) ),
    inference(spm,[status(thm)],[c_0_156,c_0_94])).

cnf(c_0_168,negated_conjecture,
    ( k7_subset_1(k2_pre_topc(esk3_0,esk4_0),esk4_0,X1) = k3_subset_1(esk4_0,k1_setfam_1(k2_tarski(esk4_0,X1))) ),
    inference(spm,[status(thm)],[c_0_149,c_0_157])).

cnf(c_0_169,negated_conjecture,
    ( k3_subset_1(k2_pre_topc(esk3_0,esk4_0),esk4_0) = k2_tops_1(esk3_0,esk4_0)
    | v3_pre_topc(esk4_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_158,c_0_159]),c_0_109]),c_0_160])).

cnf(c_0_170,negated_conjecture,
    ( r1_tarski(esk4_0,k2_pre_topc(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_105,c_0_148])).

cnf(c_0_171,plain,
    ( k9_subset_1(X2,X3,X3) = X3
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_161])).

cnf(c_0_172,plain,
    ( m1_subset_1(esk2_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_162])).

cnf(c_0_173,negated_conjecture,
    ( k1_setfam_1(k2_tarski(esk4_0,k2_tops_1(esk3_0,esk4_0))) = k3_subset_1(esk4_0,k1_tops_1(esk3_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110,c_0_163]),c_0_113])])).

cnf(c_0_174,plain,
    ( r1_tarski(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),X1) ),
    inference(rw,[status(thm)],[c_0_164,c_0_46])).

fof(c_0_175,plain,(
    ! [X80,X81] :
      ( ~ v2_pre_topc(X80)
      | ~ l1_pre_topc(X80)
      | ~ m1_subset_1(X81,k1_zfmisc_1(u1_struct_0(X80)))
      | v3_pre_topc(k1_tops_1(X80,X81),X80) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc9_tops_1])])).

cnf(c_0_176,negated_conjecture,
    ( r1_tarski(X1,k1_tops_1(esk3_0,esk4_0))
    | ~ v3_pre_topc(X1,esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ r1_tarski(X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_165,c_0_79]),c_0_86])])).

cnf(c_0_177,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ r1_tarski(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_126,c_0_166])).

cnf(c_0_178,negated_conjecture,
    ( k9_subset_1(k2_pre_topc(esk3_0,esk4_0),esk4_0,k3_subset_1(k2_pre_topc(esk3_0,esk4_0),X1)) = k3_subset_1(esk4_0,k1_setfam_1(k2_tarski(esk4_0,X1)))
    | ~ r1_tarski(X1,k2_pre_topc(esk3_0,esk4_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_167,c_0_157]),c_0_168])).

cnf(c_0_179,negated_conjecture,
    ( k3_subset_1(k2_pre_topc(esk3_0,esk4_0),k2_tops_1(esk3_0,esk4_0)) = esk4_0
    | v3_pre_topc(esk4_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110,c_0_169]),c_0_170])])).

cnf(c_0_180,plain,
    ( k9_subset_1(X1,X2,X2) = X2 ),
    inference(spm,[status(thm)],[c_0_171,c_0_172])).

cnf(c_0_181,negated_conjecture,
    ( k3_subset_1(esk4_0,k3_subset_1(esk4_0,k1_tops_1(esk3_0,esk4_0))) = k1_tops_1(esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[c_0_163,c_0_173])).

cnf(c_0_182,negated_conjecture,
    ( r1_tarski(k2_tops_1(esk3_0,esk4_0),k2_pre_topc(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_122,c_0_148])).

cnf(c_0_183,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_103])).

cnf(c_0_184,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk3_0,esk4_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_174,c_0_151])).

cnf(c_0_185,plain,
    ( v3_pre_topc(k1_tops_1(X1,X2),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_175])).

cnf(c_0_186,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_187,negated_conjecture,
    ( r1_tarski(X1,k1_tops_1(esk3_0,esk4_0))
    | ~ v3_pre_topc(X1,esk3_0)
    | ~ r1_tarski(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_176,c_0_177])).

cnf(c_0_188,negated_conjecture,
    ( k1_tops_1(esk3_0,esk4_0) = esk4_0
    | v3_pre_topc(esk4_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_178,c_0_179]),c_0_180]),c_0_173]),c_0_181]),c_0_182])])).

cnf(c_0_189,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_183])).

cnf(c_0_190,negated_conjecture,
    ( k1_tops_1(esk3_0,esk4_0) = esk4_0
    | ~ r1_tarski(esk4_0,k1_tops_1(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_120,c_0_184])).

cnf(c_0_191,negated_conjecture,
    ( ~ v3_pre_topc(esk4_0,esk3_0)
    | k2_tops_1(esk3_0,esk4_0) != k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_192,negated_conjecture,
    ( v3_pre_topc(k1_tops_1(esk3_0,esk4_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_185,c_0_79]),c_0_186]),c_0_86])])).

cnf(c_0_193,negated_conjecture,
    ( k1_tops_1(esk3_0,esk4_0) = esk4_0 ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_187,c_0_188]),c_0_189])]),c_0_190])).

fof(c_0_194,plain,(
    ! [X82,X83] :
      ( ~ l1_pre_topc(X82)
      | ~ m1_subset_1(X83,k1_zfmisc_1(u1_struct_0(X82)))
      | k2_tops_1(X82,X83) = k7_subset_1(u1_struct_0(X82),k2_pre_topc(X82,X83),k1_tops_1(X82,X83)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l78_tops_1])])])).

cnf(c_0_195,negated_conjecture,
    ( k3_subset_1(k2_pre_topc(esk3_0,esk4_0),esk4_0) != k2_tops_1(esk3_0,esk4_0)
    | ~ v3_pre_topc(esk4_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_191,c_0_159]),c_0_109]),c_0_160])).

cnf(c_0_196,negated_conjecture,
    ( v3_pre_topc(esk4_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_192,c_0_193])).

cnf(c_0_197,plain,
    ( k2_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k1_tops_1(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_194])).

cnf(c_0_198,negated_conjecture,
    ( k3_subset_1(k2_pre_topc(esk3_0,esk4_0),esk4_0) != k2_tops_1(esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_195,c_0_196])])).

cnf(c_0_199,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_197,c_0_193]),c_0_159]),c_0_109]),c_0_160]),c_0_86]),c_0_79])]),c_0_198]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:43:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.20/0.35  # No SInE strategy applied
% 0.20/0.35  # Trying AutoSched0 for 299 seconds
% 1.81/1.99  # AutoSched0-Mode selected heuristic G_E___107_C36_F1_PI_AE_Q4_CS_SP_PS_S0Y
% 1.81/1.99  # and selection function SelectMaxLComplexAvoidPosPred.
% 1.81/1.99  #
% 1.81/1.99  # Preprocessing time       : 0.029 s
% 1.81/1.99  # Presaturation interreduction done
% 1.81/1.99  
% 1.81/1.99  # Proof found!
% 1.81/1.99  # SZS status Theorem
% 1.81/1.99  # SZS output start CNFRefutation
% 1.81/1.99  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 1.81/1.99  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 1.81/1.99  fof(t46_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 1.81/1.99  fof(idempotence_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 1.81/1.99  fof(dt_k6_subset_1, axiom, ![X1, X2]:m1_subset_1(k6_subset_1(X1,X2),k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_subset_1)).
% 1.81/1.99  fof(redefinition_k6_subset_1, axiom, ![X1, X2]:k6_subset_1(X1,X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 1.81/1.99  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 1.81/1.99  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 1.81/1.99  fof(t52_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(X1,k4_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_xboole_1)).
% 1.81/1.99  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 1.81/1.99  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 1.81/1.99  fof(involutiveness_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,k3_subset_1(X1,X2))=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 1.81/1.99  fof(redefinition_k4_subset_1, axiom, ![X1, X2, X3]:((m1_subset_1(X2,k1_zfmisc_1(X1))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>k4_subset_1(X1,X2,X3)=k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 1.81/1.99  fof(t76_tops_1, conjecture, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>k2_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_tops_1)).
% 1.81/1.99  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 1.81/1.99  fof(dt_k4_subset_1, axiom, ![X1, X2, X3]:((m1_subset_1(X2,k1_zfmisc_1(X1))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>m1_subset_1(k4_subset_1(X1,X2,X3),k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_subset_1)).
% 1.81/1.99  fof(t62_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k2_tops_1(X1,X2)=k2_tops_1(X1,k3_subset_1(u1_struct_0(X1),X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_tops_1)).
% 1.81/1.99  fof(dt_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 1.81/1.99  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 1.81/1.99  fof(dt_k2_tops_1, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>m1_subset_1(k2_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 1.81/1.99  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 1.81/1.99  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 1.81/1.99  fof(t65_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k2_pre_topc(X1,X2)=k4_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_1)).
% 1.81/1.99  fof(redefinition_k7_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k7_subset_1(X1,X2,X3)=k4_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 1.81/1.99  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.81/1.99  fof(t3_xboole_1, axiom, ![X1]:(r1_tarski(X1,k1_xboole_0)=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 1.81/1.99  fof(t74_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k1_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_tops_1)).
% 1.81/1.99  fof(t32_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k7_subset_1(X1,X2,X3)=k9_subset_1(X1,X2,k3_subset_1(X1,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_subset_1)).
% 1.81/1.99  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 1.81/1.99  fof(t56_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((v3_pre_topc(X2,X1)&r1_tarski(X2,X3))=>r1_tarski(X2,k1_tops_1(X1,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_tops_1)).
% 1.81/1.99  fof(idempotence_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k9_subset_1(X1,X2,X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k9_subset_1)).
% 1.81/1.99  fof(existence_m1_subset_1, axiom, ![X1]:?[X2]:m1_subset_1(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 1.81/1.99  fof(fc9_tops_1, axiom, ![X1, X2]:(((v2_pre_topc(X1)&l1_pre_topc(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>v3_pre_topc(k1_tops_1(X1,X2),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_tops_1)).
% 1.81/1.99  fof(l78_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k2_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k1_tops_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l78_tops_1)).
% 1.81/1.99  fof(c_0_34, plain, ![X15, X16]:k4_xboole_0(X15,X16)=k5_xboole_0(X15,k3_xboole_0(X15,X16)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 1.81/1.99  fof(c_0_35, plain, ![X74, X75]:k1_setfam_1(k2_tarski(X74,X75))=k3_xboole_0(X74,X75), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 1.81/1.99  fof(c_0_36, plain, ![X35, X36]:k4_xboole_0(X35,k2_xboole_0(X35,X36))=k1_xboole_0, inference(variable_rename,[status(thm)],[t46_xboole_1])).
% 1.81/1.99  cnf(c_0_37, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 1.81/1.99  cnf(c_0_38, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 1.81/1.99  fof(c_0_39, plain, ![X12]:k3_xboole_0(X12,X12)=X12, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).
% 1.81/1.99  fof(c_0_40, plain, ![X51, X52]:m1_subset_1(k6_subset_1(X51,X52),k1_zfmisc_1(X51)), inference(variable_rename,[status(thm)],[dt_k6_subset_1])).
% 1.81/1.99  fof(c_0_41, plain, ![X66, X67]:k6_subset_1(X66,X67)=k4_xboole_0(X66,X67), inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).
% 1.81/1.99  fof(c_0_42, plain, ![X27]:k4_xboole_0(X27,k1_xboole_0)=X27, inference(variable_rename,[status(thm)],[t3_boole])).
% 1.81/1.99  fof(c_0_43, plain, ![X44, X45]:(~m1_subset_1(X45,k1_zfmisc_1(X44))|k3_subset_1(X44,X45)=k4_xboole_0(X44,X45)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 1.81/1.99  fof(c_0_44, plain, ![X37, X38, X39]:k4_xboole_0(X37,k4_xboole_0(X38,X39))=k2_xboole_0(k4_xboole_0(X37,X38),k3_xboole_0(X37,X39)), inference(variable_rename,[status(thm)],[t52_xboole_1])).
% 1.81/1.99  cnf(c_0_45, plain, (k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_36])).
% 1.81/1.99  cnf(c_0_46, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))), inference(rw,[status(thm)],[c_0_37, c_0_38])).
% 1.81/1.99  fof(c_0_47, plain, ![X19]:k2_xboole_0(X19,k1_xboole_0)=X19, inference(variable_rename,[status(thm)],[t1_boole])).
% 1.81/1.99  cnf(c_0_48, plain, (k3_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_39])).
% 1.81/1.99  fof(c_0_49, plain, ![X4, X5]:k2_xboole_0(X4,X5)=k2_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 1.81/1.99  cnf(c_0_50, plain, (m1_subset_1(k6_subset_1(X1,X2),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 1.81/1.99  cnf(c_0_51, plain, (k6_subset_1(X1,X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 1.81/1.99  cnf(c_0_52, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_42])).
% 1.81/1.99  fof(c_0_53, plain, ![X58, X59]:(~m1_subset_1(X59,k1_zfmisc_1(X58))|k3_subset_1(X58,k3_subset_1(X58,X59))=X59), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).
% 1.81/1.99  cnf(c_0_54, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 1.81/1.99  cnf(c_0_55, plain, (k4_xboole_0(X1,k4_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 1.81/1.99  cnf(c_0_56, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k2_xboole_0(X1,X2))))=k1_xboole_0), inference(rw,[status(thm)],[c_0_45, c_0_46])).
% 1.81/1.99  cnf(c_0_57, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_47])).
% 1.81/1.99  cnf(c_0_58, plain, (k1_setfam_1(k2_tarski(X1,X1))=X1), inference(rw,[status(thm)],[c_0_48, c_0_38])).
% 1.81/1.99  cnf(c_0_59, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 1.81/1.99  fof(c_0_60, plain, ![X63, X64, X65]:(~m1_subset_1(X64,k1_zfmisc_1(X63))|~m1_subset_1(X65,k1_zfmisc_1(X63))|k4_subset_1(X63,X64,X65)=k2_xboole_0(X64,X65)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).
% 1.81/1.99  cnf(c_0_61, plain, (m1_subset_1(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),k1_zfmisc_1(X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50, c_0_51]), c_0_46])).
% 1.81/1.99  cnf(c_0_62, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k1_xboole_0)))=X1), inference(rw,[status(thm)],[c_0_52, c_0_46])).
% 1.81/1.99  fof(c_0_63, negated_conjecture, ~(![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>k2_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),X2))))), inference(assume_negation,[status(cth)],[t76_tops_1])).
% 1.81/1.99  cnf(c_0_64, plain, (k3_subset_1(X2,k3_subset_1(X2,X1))=X1|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_53])).
% 1.81/1.99  cnf(c_0_65, plain, (k3_subset_1(X2,X1)=k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_54, c_0_46])).
% 1.81/1.99  cnf(c_0_66, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X3))))))=k2_xboole_0(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),k1_setfam_1(k2_tarski(X1,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55, c_0_38]), c_0_46]), c_0_46]), c_0_46])).
% 1.81/1.99  cnf(c_0_67, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_58])).
% 1.81/1.99  cnf(c_0_68, plain, (k2_xboole_0(k1_xboole_0,X1)=X1), inference(spm,[status(thm)],[c_0_57, c_0_59])).
% 1.81/1.99  cnf(c_0_69, plain, (k4_subset_1(X2,X1,X3)=k2_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_60])).
% 1.81/1.99  cnf(c_0_70, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 1.81/1.99  fof(c_0_71, negated_conjecture, ((v2_pre_topc(esk3_0)&l1_pre_topc(esk3_0))&(m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))&((~v3_pre_topc(esk4_0,esk3_0)|k2_tops_1(esk3_0,esk4_0)!=k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),esk4_0))&(v3_pre_topc(esk4_0,esk3_0)|k2_tops_1(esk3_0,esk4_0)=k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),esk4_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_63])])])).
% 1.81/1.99  fof(c_0_72, plain, ![X76, X77]:((~m1_subset_1(X76,k1_zfmisc_1(X77))|r1_tarski(X76,X77))&(~r1_tarski(X76,X77)|m1_subset_1(X76,k1_zfmisc_1(X77)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 1.81/1.99  fof(c_0_73, plain, ![X48, X49, X50]:(~m1_subset_1(X49,k1_zfmisc_1(X48))|~m1_subset_1(X50,k1_zfmisc_1(X48))|m1_subset_1(k4_subset_1(X48,X49,X50),k1_zfmisc_1(X48))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_subset_1])])).
% 1.81/1.99  cnf(c_0_74, plain, (k3_subset_1(X1,k3_subset_1(X1,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))))=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))), inference(spm,[status(thm)],[c_0_64, c_0_61])).
% 1.81/1.99  cnf(c_0_75, plain, (k3_subset_1(X1,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))))=k1_setfam_1(k2_tarski(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_61]), c_0_66]), c_0_58]), c_0_67]), c_0_68])).
% 1.81/1.99  fof(c_0_76, plain, ![X87, X88]:(~l1_pre_topc(X87)|(~m1_subset_1(X88,k1_zfmisc_1(u1_struct_0(X87)))|k2_tops_1(X87,X88)=k2_tops_1(X87,k3_subset_1(u1_struct_0(X87),X88)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t62_tops_1])])])).
% 1.81/1.99  fof(c_0_77, plain, ![X46, X47]:(~m1_subset_1(X47,k1_zfmisc_1(X46))|m1_subset_1(k3_subset_1(X46,X47),k1_zfmisc_1(X46))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).
% 1.81/1.99  cnf(c_0_78, plain, (k4_subset_1(X1,X2,X1)=k2_xboole_0(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_69, c_0_70])).
% 1.81/1.99  cnf(c_0_79, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_71])).
% 1.81/1.99  cnf(c_0_80, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_72])).
% 1.81/1.99  cnf(c_0_81, plain, (m1_subset_1(k4_subset_1(X2,X1,X3),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_73])).
% 1.81/1.99  cnf(c_0_82, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))=k3_subset_1(X1,k1_setfam_1(k2_tarski(X1,X2)))), inference(rw,[status(thm)],[c_0_74, c_0_75])).
% 1.81/1.99  fof(c_0_83, plain, ![X17, X18]:r1_tarski(k3_xboole_0(X17,X18),X17), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 1.81/1.99  fof(c_0_84, plain, ![X78, X79]:(~l1_pre_topc(X78)|~m1_subset_1(X79,k1_zfmisc_1(u1_struct_0(X78)))|m1_subset_1(k2_tops_1(X78,X79),k1_zfmisc_1(u1_struct_0(X78)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_tops_1])])).
% 1.81/1.99  cnf(c_0_85, plain, (k2_tops_1(X1,X2)=k2_tops_1(X1,k3_subset_1(u1_struct_0(X1),X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_76])).
% 1.81/1.99  cnf(c_0_86, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_71])).
% 1.81/1.99  cnf(c_0_87, plain, (m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_77])).
% 1.81/1.99  cnf(c_0_88, negated_conjecture, (k4_subset_1(u1_struct_0(esk3_0),esk4_0,u1_struct_0(esk3_0))=k2_xboole_0(esk4_0,u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_78, c_0_79])).
% 1.81/1.99  fof(c_0_89, plain, ![X40, X41]:r1_tarski(X40,k2_xboole_0(X40,X41)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 1.81/1.99  cnf(c_0_90, plain, (r1_tarski(k4_subset_1(X1,X2,X3),X1)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_80, c_0_81])).
% 1.81/1.99  cnf(c_0_91, plain, (k3_subset_1(X1,k3_subset_1(X1,k1_setfam_1(k2_tarski(X1,X2))))=k1_setfam_1(k2_tarski(X1,X2))), inference(rw,[status(thm)],[c_0_75, c_0_82])).
% 1.81/1.99  cnf(c_0_92, plain, (m1_subset_1(k3_subset_1(X1,k1_setfam_1(k2_tarski(X1,X2))),k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_61, c_0_82])).
% 1.81/1.99  fof(c_0_93, plain, ![X42, X43]:k2_tarski(X42,X43)=k2_tarski(X43,X42), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 1.81/1.99  cnf(c_0_94, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_72])).
% 1.81/1.99  cnf(c_0_95, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k2_xboole_0(X2,X1))))=k1_xboole_0), inference(spm,[status(thm)],[c_0_56, c_0_59])).
% 1.81/1.99  cnf(c_0_96, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_61, c_0_56])).
% 1.81/1.99  cnf(c_0_97, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_83])).
% 1.81/1.99  cnf(c_0_98, plain, (m1_subset_1(k2_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_84])).
% 1.81/1.99  cnf(c_0_99, negated_conjecture, (k2_tops_1(esk3_0,k3_subset_1(u1_struct_0(esk3_0),esk4_0))=k2_tops_1(esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_79]), c_0_86])])).
% 1.81/1.99  cnf(c_0_100, plain, (r1_tarski(k3_subset_1(X1,X2),X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_80, c_0_87])).
% 1.81/1.99  fof(c_0_101, plain, ![X89, X90]:(~l1_pre_topc(X89)|(~m1_subset_1(X90,k1_zfmisc_1(u1_struct_0(X89)))|k2_pre_topc(X89,X90)=k4_subset_1(u1_struct_0(X89),X90,k2_tops_1(X89,X90)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_tops_1])])])).
% 1.81/1.99  fof(c_0_102, plain, ![X68, X69, X70]:(~m1_subset_1(X69,k1_zfmisc_1(X68))|k7_subset_1(X68,X69,X70)=k4_xboole_0(X69,X70)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).
% 1.81/1.99  fof(c_0_103, plain, ![X13, X14]:(((r1_tarski(X13,X14)|X13!=X14)&(r1_tarski(X14,X13)|X13!=X14))&(~r1_tarski(X13,X14)|~r1_tarski(X14,X13)|X13=X14)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 1.81/1.99  cnf(c_0_104, negated_conjecture, (m1_subset_1(k2_xboole_0(esk4_0,u1_struct_0(esk3_0)),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_88]), c_0_70]), c_0_79])])).
% 1.81/1.99  cnf(c_0_105, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_89])).
% 1.81/1.99  fof(c_0_106, plain, ![X28]:(~r1_tarski(X28,k1_xboole_0)|X28=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).
% 1.81/1.99  cnf(c_0_107, plain, (r1_tarski(k4_subset_1(X1,X2,X1),X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_90, c_0_70])).
% 1.81/1.99  cnf(c_0_108, plain, (m1_subset_1(k1_setfam_1(k2_tarski(X1,X2)),k1_zfmisc_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_91]), c_0_92])])).
% 1.81/1.99  cnf(c_0_109, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_93])).
% 1.81/1.99  cnf(c_0_110, plain, (k3_subset_1(X1,k3_subset_1(X1,X2))=X2|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_64, c_0_94])).
% 1.81/1.99  cnf(c_0_111, plain, (k3_subset_1(X1,k1_setfam_1(k2_tarski(X1,k2_xboole_0(X2,X1))))=k1_xboole_0), inference(rw,[status(thm)],[c_0_95, c_0_82])).
% 1.81/1.99  cnf(c_0_112, plain, (k3_subset_1(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_96]), c_0_62])).
% 1.81/1.99  cnf(c_0_113, plain, (r1_tarski(k1_setfam_1(k2_tarski(X1,X2)),X1)), inference(rw,[status(thm)],[c_0_97, c_0_38])).
% 1.81/1.99  cnf(c_0_114, negated_conjecture, (m1_subset_1(k2_tops_1(esk3_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))|~m1_subset_1(k3_subset_1(u1_struct_0(esk3_0),esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_99]), c_0_86])])).
% 1.81/1.99  cnf(c_0_115, negated_conjecture, (r1_tarski(k3_subset_1(u1_struct_0(esk3_0),esk4_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_100, c_0_79])).
% 1.81/1.99  cnf(c_0_116, plain, (k2_pre_topc(X1,X2)=k4_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_101])).
% 1.81/1.99  fof(c_0_117, plain, ![X91, X92]:(~l1_pre_topc(X91)|(~m1_subset_1(X92,k1_zfmisc_1(u1_struct_0(X91)))|k1_tops_1(X91,X92)=k7_subset_1(u1_struct_0(X91),X92,k2_tops_1(X91,X92)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t74_tops_1])])])).
% 1.81/1.99  cnf(c_0_118, plain, (k7_subset_1(X2,X1,X3)=k4_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_102])).
% 1.81/1.99  cnf(c_0_119, plain, (k3_subset_1(X1,k1_setfam_1(k2_tarski(X1,k2_xboole_0(X1,X2))))=k1_xboole_0), inference(rw,[status(thm)],[c_0_56, c_0_82])).
% 1.81/1.99  cnf(c_0_120, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_103])).
% 1.81/1.99  cnf(c_0_121, negated_conjecture, (r1_tarski(k2_xboole_0(esk4_0,u1_struct_0(esk3_0)),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_80, c_0_104])).
% 1.81/1.99  cnf(c_0_122, plain, (r1_tarski(X1,k2_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_105, c_0_59])).
% 1.81/1.99  cnf(c_0_123, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_106])).
% 1.81/1.99  cnf(c_0_124, plain, (r1_tarski(k4_subset_1(X1,X2,X1),X1)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_107, c_0_94])).
% 1.81/1.99  cnf(c_0_125, plain, (k4_subset_1(X1,X2,X1)=k2_xboole_0(X2,X1)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_78, c_0_94])).
% 1.81/1.99  cnf(c_0_126, plain, (m1_subset_1(k1_setfam_1(k2_tarski(X1,X2)),k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_108, c_0_109])).
% 1.81/1.99  cnf(c_0_127, plain, (k1_setfam_1(k2_tarski(X1,k2_xboole_0(X2,X1)))=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110, c_0_111]), c_0_112]), c_0_113])])).
% 1.81/1.99  cnf(c_0_128, negated_conjecture, (m1_subset_1(k2_tops_1(esk3_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114, c_0_94]), c_0_115])])).
% 1.81/1.99  cnf(c_0_129, negated_conjecture, (k4_subset_1(u1_struct_0(esk3_0),esk4_0,k2_tops_1(esk3_0,esk4_0))=k2_pre_topc(esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116, c_0_79]), c_0_86])])).
% 1.81/1.99  cnf(c_0_130, plain, (k1_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_117])).
% 1.81/1.99  cnf(c_0_131, plain, (k7_subset_1(X2,X1,X3)=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X3)))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_118, c_0_46])).
% 1.81/1.99  cnf(c_0_132, plain, (k1_setfam_1(k2_tarski(X1,k2_xboole_0(X1,X2)))=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110, c_0_119]), c_0_112]), c_0_113])])).
% 1.81/1.99  cnf(c_0_133, negated_conjecture, (k2_xboole_0(esk4_0,u1_struct_0(esk3_0))=u1_struct_0(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120, c_0_121]), c_0_122])])).
% 1.81/1.99  cnf(c_0_134, plain, (k1_setfam_1(k2_tarski(k1_xboole_0,X1))=k1_xboole_0), inference(spm,[status(thm)],[c_0_123, c_0_113])).
% 1.81/1.99  cnf(c_0_135, plain, (r1_tarski(k2_xboole_0(X1,X2),X2)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_124, c_0_125])).
% 1.81/1.99  cnf(c_0_136, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_xboole_0(X2,X1)))), inference(spm,[status(thm)],[c_0_126, c_0_127])).
% 1.81/1.99  cnf(c_0_137, negated_conjecture, (k4_subset_1(u1_struct_0(esk3_0),X1,k2_tops_1(esk3_0,esk4_0))=k2_xboole_0(X1,k2_tops_1(esk3_0,esk4_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(spm,[status(thm)],[c_0_69, c_0_128])).
% 1.81/1.99  cnf(c_0_138, negated_conjecture, (m1_subset_1(k2_pre_topc(esk3_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))|~m1_subset_1(k2_tops_1(esk3_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_129]), c_0_79])])).
% 1.81/1.99  cnf(c_0_139, negated_conjecture, (k7_subset_1(u1_struct_0(esk3_0),esk4_0,k2_tops_1(esk3_0,esk4_0))=k1_tops_1(esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_130, c_0_79]), c_0_86])])).
% 1.81/1.99  cnf(c_0_140, negated_conjecture, (k7_subset_1(u1_struct_0(esk3_0),esk4_0,X1)=k5_xboole_0(esk4_0,k1_setfam_1(k2_tarski(esk4_0,X1)))), inference(spm,[status(thm)],[c_0_131, c_0_79])).
% 1.81/1.99  cnf(c_0_141, plain, (k3_subset_1(X1,k1_setfam_1(k2_tarski(X1,k3_subset_1(X2,k1_setfam_1(k2_tarski(X2,X3))))))=k2_xboole_0(k3_subset_1(X1,k1_setfam_1(k2_tarski(X1,X2))),k1_setfam_1(k2_tarski(X1,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66, c_0_82]), c_0_82]), c_0_82])).
% 1.81/1.99  cnf(c_0_142, negated_conjecture, (k1_setfam_1(k2_tarski(esk4_0,u1_struct_0(esk3_0)))=esk4_0), inference(spm,[status(thm)],[c_0_132, c_0_133])).
% 1.81/1.99  cnf(c_0_143, plain, (k3_subset_1(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_70]), c_0_58]), c_0_67])).
% 1.81/1.99  cnf(c_0_144, plain, (k1_setfam_1(k2_tarski(X1,k1_xboole_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_134, c_0_109])).
% 1.81/1.99  cnf(c_0_145, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120, c_0_135]), c_0_122])])).
% 1.81/1.99  fof(c_0_146, plain, ![X71, X72, X73]:(~m1_subset_1(X72,k1_zfmisc_1(X71))|(~m1_subset_1(X73,k1_zfmisc_1(X71))|k7_subset_1(X71,X72,X73)=k9_subset_1(X71,X72,k3_subset_1(X71,X73)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t32_subset_1])])])).
% 1.81/1.99  cnf(c_0_147, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_xboole_0(X1,X2)))), inference(spm,[status(thm)],[c_0_136, c_0_59])).
% 1.81/1.99  cnf(c_0_148, negated_conjecture, (k2_xboole_0(esk4_0,k2_tops_1(esk3_0,esk4_0))=k2_pre_topc(esk3_0,esk4_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_137, c_0_79]), c_0_129])).
% 1.81/1.99  cnf(c_0_149, plain, (k7_subset_1(X1,X2,X3)=k3_subset_1(X2,k1_setfam_1(k2_tarski(X2,X3)))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_131, c_0_82])).
% 1.81/1.99  cnf(c_0_150, negated_conjecture, (m1_subset_1(k2_pre_topc(esk3_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_138, c_0_128])])).
% 1.81/1.99  cnf(c_0_151, negated_conjecture, (k5_xboole_0(esk4_0,k1_setfam_1(k2_tarski(esk4_0,k2_tops_1(esk3_0,esk4_0))))=k1_tops_1(esk3_0,esk4_0)), inference(rw,[status(thm)],[c_0_139, c_0_140])).
% 1.81/1.99  fof(c_0_152, plain, ![X23, X24]:r1_tarski(k4_xboole_0(X23,X24),X23), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 1.81/1.99  fof(c_0_153, plain, ![X84, X85, X86]:(~l1_pre_topc(X84)|(~m1_subset_1(X85,k1_zfmisc_1(u1_struct_0(X84)))|(~m1_subset_1(X86,k1_zfmisc_1(u1_struct_0(X84)))|(~v3_pre_topc(X85,X84)|~r1_tarski(X85,X86)|r1_tarski(X85,k1_tops_1(X84,X86)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t56_tops_1])])])).
% 1.81/1.99  cnf(c_0_154, negated_conjecture, (k2_xboole_0(k3_subset_1(X1,k1_setfam_1(k2_tarski(X1,esk4_0))),k1_setfam_1(k2_tarski(X1,u1_struct_0(esk3_0))))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_141, c_0_142]), c_0_143]), c_0_144]), c_0_112])).
% 1.81/1.99  cnf(c_0_155, plain, (k1_setfam_1(k2_tarski(X1,X2))=X1|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_132, c_0_145])).
% 1.81/1.99  cnf(c_0_156, plain, (k7_subset_1(X2,X1,X3)=k9_subset_1(X2,X1,k3_subset_1(X2,X3))|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_146])).
% 1.81/1.99  cnf(c_0_157, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_pre_topc(esk3_0,esk4_0)))), inference(spm,[status(thm)],[c_0_147, c_0_148])).
% 1.81/1.99  cnf(c_0_158, negated_conjecture, (v3_pre_topc(esk4_0,esk3_0)|k2_tops_1(esk3_0,esk4_0)=k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),esk4_0)), inference(split_conjunct,[status(thm)],[c_0_71])).
% 1.81/1.99  cnf(c_0_159, negated_conjecture, (k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),X1)=k3_subset_1(k2_pre_topc(esk3_0,esk4_0),k1_setfam_1(k2_tarski(k2_pre_topc(esk3_0,esk4_0),X1)))), inference(spm,[status(thm)],[c_0_149, c_0_150])).
% 1.81/1.99  cnf(c_0_160, negated_conjecture, (k1_setfam_1(k2_tarski(esk4_0,k2_pre_topc(esk3_0,esk4_0)))=esk4_0), inference(spm,[status(thm)],[c_0_132, c_0_148])).
% 1.81/1.99  fof(c_0_161, plain, ![X55, X56, X57]:(~m1_subset_1(X57,k1_zfmisc_1(X55))|k9_subset_1(X55,X56,X56)=X56), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[idempotence_k9_subset_1])])).
% 1.81/1.99  fof(c_0_162, plain, ![X53]:m1_subset_1(esk2_1(X53),X53), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).
% 1.81/1.99  cnf(c_0_163, negated_conjecture, (k3_subset_1(esk4_0,k1_setfam_1(k2_tarski(esk4_0,k2_tops_1(esk3_0,esk4_0))))=k1_tops_1(esk3_0,esk4_0)), inference(rw,[status(thm)],[c_0_151, c_0_82])).
% 1.81/1.99  cnf(c_0_164, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_152])).
% 1.81/1.99  cnf(c_0_165, plain, (r1_tarski(X2,k1_tops_1(X1,X3))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v3_pre_topc(X2,X1)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_153])).
% 1.81/1.99  cnf(c_0_166, negated_conjecture, (k1_setfam_1(k2_tarski(X1,u1_struct_0(esk3_0)))=X1|~r1_tarski(X1,esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_154, c_0_155]), c_0_143]), c_0_68])).
% 1.81/1.99  cnf(c_0_167, plain, (k7_subset_1(X1,X2,X3)=k9_subset_1(X1,X2,k3_subset_1(X1,X3))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_tarski(X3,X1)), inference(spm,[status(thm)],[c_0_156, c_0_94])).
% 1.81/1.99  cnf(c_0_168, negated_conjecture, (k7_subset_1(k2_pre_topc(esk3_0,esk4_0),esk4_0,X1)=k3_subset_1(esk4_0,k1_setfam_1(k2_tarski(esk4_0,X1)))), inference(spm,[status(thm)],[c_0_149, c_0_157])).
% 1.81/1.99  cnf(c_0_169, negated_conjecture, (k3_subset_1(k2_pre_topc(esk3_0,esk4_0),esk4_0)=k2_tops_1(esk3_0,esk4_0)|v3_pre_topc(esk4_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_158, c_0_159]), c_0_109]), c_0_160])).
% 1.81/1.99  cnf(c_0_170, negated_conjecture, (r1_tarski(esk4_0,k2_pre_topc(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_105, c_0_148])).
% 1.81/1.99  cnf(c_0_171, plain, (k9_subset_1(X2,X3,X3)=X3|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_161])).
% 1.81/1.99  cnf(c_0_172, plain, (m1_subset_1(esk2_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_162])).
% 1.81/1.99  cnf(c_0_173, negated_conjecture, (k1_setfam_1(k2_tarski(esk4_0,k2_tops_1(esk3_0,esk4_0)))=k3_subset_1(esk4_0,k1_tops_1(esk3_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110, c_0_163]), c_0_113])])).
% 1.81/1.99  cnf(c_0_174, plain, (r1_tarski(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),X1)), inference(rw,[status(thm)],[c_0_164, c_0_46])).
% 1.81/1.99  fof(c_0_175, plain, ![X80, X81]:(~v2_pre_topc(X80)|~l1_pre_topc(X80)|~m1_subset_1(X81,k1_zfmisc_1(u1_struct_0(X80)))|v3_pre_topc(k1_tops_1(X80,X81),X80)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc9_tops_1])])).
% 1.81/1.99  cnf(c_0_176, negated_conjecture, (r1_tarski(X1,k1_tops_1(esk3_0,esk4_0))|~v3_pre_topc(X1,esk3_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))|~r1_tarski(X1,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_165, c_0_79]), c_0_86])])).
% 1.81/1.99  cnf(c_0_177, negated_conjecture, (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))|~r1_tarski(X1,esk4_0)), inference(spm,[status(thm)],[c_0_126, c_0_166])).
% 1.81/1.99  cnf(c_0_178, negated_conjecture, (k9_subset_1(k2_pre_topc(esk3_0,esk4_0),esk4_0,k3_subset_1(k2_pre_topc(esk3_0,esk4_0),X1))=k3_subset_1(esk4_0,k1_setfam_1(k2_tarski(esk4_0,X1)))|~r1_tarski(X1,k2_pre_topc(esk3_0,esk4_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_167, c_0_157]), c_0_168])).
% 1.81/1.99  cnf(c_0_179, negated_conjecture, (k3_subset_1(k2_pre_topc(esk3_0,esk4_0),k2_tops_1(esk3_0,esk4_0))=esk4_0|v3_pre_topc(esk4_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110, c_0_169]), c_0_170])])).
% 1.81/1.99  cnf(c_0_180, plain, (k9_subset_1(X1,X2,X2)=X2), inference(spm,[status(thm)],[c_0_171, c_0_172])).
% 1.81/1.99  cnf(c_0_181, negated_conjecture, (k3_subset_1(esk4_0,k3_subset_1(esk4_0,k1_tops_1(esk3_0,esk4_0)))=k1_tops_1(esk3_0,esk4_0)), inference(rw,[status(thm)],[c_0_163, c_0_173])).
% 1.81/1.99  cnf(c_0_182, negated_conjecture, (r1_tarski(k2_tops_1(esk3_0,esk4_0),k2_pre_topc(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_122, c_0_148])).
% 1.81/1.99  cnf(c_0_183, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_103])).
% 1.81/1.99  cnf(c_0_184, negated_conjecture, (r1_tarski(k1_tops_1(esk3_0,esk4_0),esk4_0)), inference(spm,[status(thm)],[c_0_174, c_0_151])).
% 1.81/1.99  cnf(c_0_185, plain, (v3_pre_topc(k1_tops_1(X1,X2),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_175])).
% 1.81/1.99  cnf(c_0_186, negated_conjecture, (v2_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_71])).
% 1.81/1.99  cnf(c_0_187, negated_conjecture, (r1_tarski(X1,k1_tops_1(esk3_0,esk4_0))|~v3_pre_topc(X1,esk3_0)|~r1_tarski(X1,esk4_0)), inference(spm,[status(thm)],[c_0_176, c_0_177])).
% 1.81/1.99  cnf(c_0_188, negated_conjecture, (k1_tops_1(esk3_0,esk4_0)=esk4_0|v3_pre_topc(esk4_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_178, c_0_179]), c_0_180]), c_0_173]), c_0_181]), c_0_182])])).
% 1.81/1.99  cnf(c_0_189, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_183])).
% 1.81/1.99  cnf(c_0_190, negated_conjecture, (k1_tops_1(esk3_0,esk4_0)=esk4_0|~r1_tarski(esk4_0,k1_tops_1(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_120, c_0_184])).
% 1.81/1.99  cnf(c_0_191, negated_conjecture, (~v3_pre_topc(esk4_0,esk3_0)|k2_tops_1(esk3_0,esk4_0)!=k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),esk4_0)), inference(split_conjunct,[status(thm)],[c_0_71])).
% 1.81/1.99  cnf(c_0_192, negated_conjecture, (v3_pre_topc(k1_tops_1(esk3_0,esk4_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_185, c_0_79]), c_0_186]), c_0_86])])).
% 1.81/1.99  cnf(c_0_193, negated_conjecture, (k1_tops_1(esk3_0,esk4_0)=esk4_0), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_187, c_0_188]), c_0_189])]), c_0_190])).
% 1.81/1.99  fof(c_0_194, plain, ![X82, X83]:(~l1_pre_topc(X82)|(~m1_subset_1(X83,k1_zfmisc_1(u1_struct_0(X82)))|k2_tops_1(X82,X83)=k7_subset_1(u1_struct_0(X82),k2_pre_topc(X82,X83),k1_tops_1(X82,X83)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l78_tops_1])])])).
% 1.81/1.99  cnf(c_0_195, negated_conjecture, (k3_subset_1(k2_pre_topc(esk3_0,esk4_0),esk4_0)!=k2_tops_1(esk3_0,esk4_0)|~v3_pre_topc(esk4_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_191, c_0_159]), c_0_109]), c_0_160])).
% 1.81/1.99  cnf(c_0_196, negated_conjecture, (v3_pre_topc(esk4_0,esk3_0)), inference(rw,[status(thm)],[c_0_192, c_0_193])).
% 1.81/1.99  cnf(c_0_197, plain, (k2_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k1_tops_1(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_194])).
% 1.81/1.99  cnf(c_0_198, negated_conjecture, (k3_subset_1(k2_pre_topc(esk3_0,esk4_0),esk4_0)!=k2_tops_1(esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_195, c_0_196])])).
% 1.81/1.99  cnf(c_0_199, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_197, c_0_193]), c_0_159]), c_0_109]), c_0_160]), c_0_86]), c_0_79])]), c_0_198]), ['proof']).
% 1.81/1.99  # SZS output end CNFRefutation
% 1.81/1.99  # Proof object total steps             : 200
% 1.81/1.99  # Proof object clause steps            : 131
% 1.81/1.99  # Proof object formula steps           : 69
% 1.81/1.99  # Proof object conjectures             : 51
% 1.81/1.99  # Proof object clause conjectures      : 48
% 1.81/1.99  # Proof object formula conjectures     : 3
% 1.81/1.99  # Proof object initial clauses used    : 40
% 1.81/1.99  # Proof object initial formulas used   : 34
% 1.81/1.99  # Proof object generating inferences   : 65
% 1.81/1.99  # Proof object simplifying inferences  : 104
% 1.81/1.99  # Training examples: 0 positive, 0 negative
% 1.81/1.99  # Parsed axioms                        : 40
% 1.81/1.99  # Removed by relevancy pruning/SinE    : 0
% 1.81/1.99  # Initial clauses                      : 49
% 1.81/1.99  # Removed in clause preprocessing      : 3
% 1.81/1.99  # Initial clauses in saturation        : 46
% 1.81/1.99  # Processed clauses                    : 15963
% 1.81/1.99  # ...of these trivial                  : 912
% 1.81/1.99  # ...subsumed                          : 11684
% 1.81/1.99  # ...remaining for further processing  : 3366
% 1.81/1.99  # Other redundant clauses eliminated   : 2
% 1.81/1.99  # Clauses deleted for lack of memory   : 0
% 1.81/1.99  # Backward-subsumed                    : 139
% 1.81/1.99  # Backward-rewritten                   : 575
% 1.81/1.99  # Generated clauses                    : 180683
% 1.81/1.99  # ...of the previous two non-trivial   : 142759
% 1.81/1.99  # Contextual simplify-reflections      : 87
% 1.81/1.99  # Paramodulations                      : 180681
% 1.81/1.99  # Factorizations                       : 0
% 1.81/1.99  # Equation resolutions                 : 2
% 1.81/1.99  # Propositional unsat checks           : 0
% 1.81/1.99  #    Propositional check models        : 0
% 1.81/1.99  #    Propositional check unsatisfiable : 0
% 1.81/1.99  #    Propositional clauses             : 0
% 1.81/1.99  #    Propositional clauses after purity: 0
% 1.81/1.99  #    Propositional unsat core size     : 0
% 1.81/1.99  #    Propositional preprocessing time  : 0.000
% 1.81/1.99  #    Propositional encoding time       : 0.000
% 1.81/1.99  #    Propositional solver time         : 0.000
% 1.81/1.99  #    Success case prop preproc time    : 0.000
% 1.81/1.99  #    Success case prop encoding time   : 0.000
% 1.81/1.99  #    Success case prop solver time     : 0.000
% 1.81/1.99  # Current number of processed clauses  : 2605
% 1.81/1.99  #    Positive orientable unit clauses  : 988
% 1.81/1.99  #    Positive unorientable unit clauses: 12
% 1.81/1.99  #    Negative unit clauses             : 9
% 1.81/1.99  #    Non-unit-clauses                  : 1596
% 1.81/1.99  # Current number of unprocessed clauses: 125179
% 1.81/1.99  # ...number of literals in the above   : 289565
% 1.81/1.99  # Current number of archived formulas  : 0
% 1.81/1.99  # Current number of archived clauses   : 762
% 1.81/1.99  # Clause-clause subsumption calls (NU) : 405121
% 1.81/1.99  # Rec. Clause-clause subsumption calls : 318584
% 1.81/1.99  # Non-unit clause-clause subsumptions  : 6821
% 1.81/1.99  # Unit Clause-clause subsumption calls : 10748
% 1.81/1.99  # Rewrite failures with RHS unbound    : 0
% 1.81/1.99  # BW rewrite match attempts            : 9007
% 1.81/1.99  # BW rewrite match successes           : 208
% 1.81/1.99  # Condensation attempts                : 0
% 1.81/1.99  # Condensation successes               : 0
% 1.81/1.99  # Termbank termtop insertions          : 3793256
% 1.81/2.00  
% 1.81/2.00  # -------------------------------------------------
% 1.81/2.00  # User time                : 1.563 s
% 1.81/2.00  # System time              : 0.078 s
% 1.81/2.00  # Total time               : 1.641 s
% 1.81/2.00  # Maximum resident set size: 1608 pages
%------------------------------------------------------------------------------
