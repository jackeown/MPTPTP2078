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
% DateTime   : Thu Dec  3 11:18:14 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 874 expanded)
%              Number of clauses        :   51 ( 371 expanded)
%              Number of leaves         :   12 ( 226 expanded)
%              Depth                    :   16
%              Number of atoms          :  288 (2954 expanded)
%              Number of equality atoms :   40 ( 575 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal clause size      :   12 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(cc1_tops_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v1_xboole_0(X2)
           => v3_pre_topc(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_tops_1)).

fof(redefinition_k9_setfam_1,axiom,(
    ! [X1] : k9_setfam_1(X1) = k1_zfmisc_1(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).

fof(rc1_connsp_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ? [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
          & v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_connsp_1)).

fof(cc3_tops_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v1_xboole_0(X2)
           => v3_tops_1(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_tops_1)).

fof(t97_tops_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( ( v3_pre_topc(X2,X1)
              & v3_tops_1(X2,X1) )
           => X2 = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_tops_1)).

fof(d9_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k6_tmap_1(X1,X2) = g1_pre_topc(u1_struct_0(X1),k5_tmap_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_tmap_1)).

fof(t103_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( r2_hidden(X2,u1_pre_topc(X1))
          <=> u1_pre_topc(X1) = k5_tmap_1(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_tmap_1)).

fof(t106_tmap_1,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_pre_topc(X2,X1)
          <=> g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k6_tmap_1(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_tmap_1)).

fof(t5_pre_topc,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => r2_hidden(k1_xboole_0,u1_pre_topc(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_pre_topc)).

fof(t104_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( u1_struct_0(k6_tmap_1(X1,X2)) = u1_struct_0(X1)
            & u1_pre_topc(k6_tmap_1(X1,X2)) = k5_tmap_1(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_tmap_1)).

fof(t102_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => r2_hidden(X2,k5_tmap_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t102_tmap_1)).

fof(d5_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_pre_topc(X2,X1)
          <=> r2_hidden(X2,u1_pre_topc(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_pre_topc)).

fof(c_0_12,plain,(
    ! [X7,X8] :
      ( ~ v2_pre_topc(X7)
      | ~ l1_pre_topc(X7)
      | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X7)))
      | ~ v1_xboole_0(X8)
      | v3_pre_topc(X8,X7) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_tops_1])])])).

fof(c_0_13,plain,(
    ! [X3] : k9_setfam_1(X3) = k1_zfmisc_1(X3) ),
    inference(variable_rename,[status(thm)],[redefinition_k9_setfam_1])).

fof(c_0_14,plain,(
    ! [X13] :
      ( ( m1_subset_1(esk1_1(X13),k1_zfmisc_1(u1_struct_0(X13)))
        | ~ l1_pre_topc(X13) )
      & ( v1_xboole_0(esk1_1(X13))
        | ~ l1_pre_topc(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[rc1_connsp_1])])])])).

fof(c_0_15,plain,(
    ! [X9,X10] :
      ( ~ v2_pre_topc(X9)
      | ~ l1_pre_topc(X9)
      | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9)))
      | ~ v1_xboole_0(X10)
      | v3_tops_1(X10,X9) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc3_tops_1])])])).

fof(c_0_16,plain,(
    ! [X11,X12] :
      ( ~ v2_pre_topc(X11)
      | ~ l1_pre_topc(X11)
      | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X11)))
      | ~ v3_pre_topc(X12,X11)
      | ~ v3_tops_1(X12,X11)
      | X12 = k1_xboole_0 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t97_tops_1])])])).

cnf(c_0_17,plain,
    ( v3_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( k9_setfam_1(X1) = k1_zfmisc_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( m1_subset_1(esk1_1(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( v3_tops_1(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( X2 = k1_xboole_0
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(X2,X1)
    | ~ v3_tops_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,plain,
    ( v3_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ v1_xboole_0(X2)
    | ~ m1_subset_1(X2,k9_setfam_1(u1_struct_0(X1))) ),
    inference(rw,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_23,plain,
    ( m1_subset_1(esk1_1(X1),k9_setfam_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(rw,[status(thm)],[c_0_19,c_0_18])).

cnf(c_0_24,plain,
    ( v1_xboole_0(esk1_1(X1))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_25,plain,
    ( v3_tops_1(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ v1_xboole_0(X2)
    | ~ m1_subset_1(X2,k9_setfam_1(u1_struct_0(X1))) ),
    inference(rw,[status(thm)],[c_0_20,c_0_18])).

fof(c_0_26,plain,(
    ! [X15,X16] :
      ( v2_struct_0(X15)
      | ~ v2_pre_topc(X15)
      | ~ l1_pre_topc(X15)
      | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
      | k6_tmap_1(X15,X16) = g1_pre_topc(u1_struct_0(X15),k5_tmap_1(X15,X16)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d9_tmap_1])])])])).

cnf(c_0_27,plain,
    ( X2 = k1_xboole_0
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ v3_pre_topc(X2,X1)
    | ~ v3_tops_1(X2,X1)
    | ~ m1_subset_1(X2,k9_setfam_1(u1_struct_0(X1))) ),
    inference(rw,[status(thm)],[c_0_21,c_0_18])).

cnf(c_0_28,plain,
    ( v3_pre_topc(esk1_1(X1),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24])).

cnf(c_0_29,plain,
    ( v3_tops_1(esk1_1(X1),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_23]),c_0_24])).

fof(c_0_30,plain,(
    ! [X19,X20] :
      ( ( ~ r2_hidden(X20,u1_pre_topc(X19))
        | u1_pre_topc(X19) = k5_tmap_1(X19,X20)
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))
        | v2_struct_0(X19)
        | ~ v2_pre_topc(X19)
        | ~ l1_pre_topc(X19) )
      & ( u1_pre_topc(X19) != k5_tmap_1(X19,X20)
        | r2_hidden(X20,u1_pre_topc(X19))
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))
        | v2_struct_0(X19)
        | ~ v2_pre_topc(X19)
        | ~ l1_pre_topc(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t103_tmap_1])])])])])).

fof(c_0_31,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( v3_pre_topc(X2,X1)
            <=> g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k6_tmap_1(X1,X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t106_tmap_1])).

cnf(c_0_32,plain,
    ( v2_struct_0(X1)
    | k6_tmap_1(X1,X2) = g1_pre_topc(u1_struct_0(X1),k5_tmap_1(X1,X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_33,plain,
    ( esk1_1(X1) = k1_xboole_0
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_23]),c_0_28]),c_0_29])).

cnf(c_0_34,plain,
    ( u1_pre_topc(X2) = k5_tmap_1(X2,X1)
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,u1_pre_topc(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_35,plain,(
    ! [X6] :
      ( ~ v2_pre_topc(X6)
      | ~ l1_pre_topc(X6)
      | r2_hidden(k1_xboole_0,u1_pre_topc(X6)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_pre_topc])])).

fof(c_0_36,plain,(
    ! [X21,X22] :
      ( ( u1_struct_0(k6_tmap_1(X21,X22)) = u1_struct_0(X21)
        | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))
        | v2_struct_0(X21)
        | ~ v2_pre_topc(X21)
        | ~ l1_pre_topc(X21) )
      & ( u1_pre_topc(k6_tmap_1(X21,X22)) = k5_tmap_1(X21,X22)
        | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))
        | v2_struct_0(X21)
        | ~ v2_pre_topc(X21)
        | ~ l1_pre_topc(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t104_tmap_1])])])])])).

fof(c_0_37,negated_conjecture,
    ( ~ v2_struct_0(esk2_0)
    & v2_pre_topc(esk2_0)
    & l1_pre_topc(esk2_0)
    & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
    & ( ~ v3_pre_topc(esk3_0,esk2_0)
      | g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)) != k6_tmap_1(esk2_0,esk3_0) )
    & ( v3_pre_topc(esk3_0,esk2_0)
      | g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)) = k6_tmap_1(esk2_0,esk3_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_31])])])])).

cnf(c_0_38,plain,
    ( k6_tmap_1(X1,X2) = g1_pre_topc(u1_struct_0(X1),k5_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X2,k9_setfam_1(u1_struct_0(X1))) ),
    inference(rw,[status(thm)],[c_0_32,c_0_18])).

cnf(c_0_39,plain,
    ( m1_subset_1(k1_xboole_0,k9_setfam_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_33])).

cnf(c_0_40,plain,
    ( u1_pre_topc(X2) = k5_tmap_1(X2,X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2)
    | ~ r2_hidden(X1,u1_pre_topc(X2))
    | ~ m1_subset_1(X1,k9_setfam_1(u1_struct_0(X2))) ),
    inference(rw,[status(thm)],[c_0_34,c_0_18])).

cnf(c_0_41,plain,
    ( r2_hidden(k1_xboole_0,u1_pre_topc(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_42,plain,
    ( u1_pre_topc(k6_tmap_1(X1,X2)) = k5_tmap_1(X1,X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_43,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_44,plain,
    ( g1_pre_topc(u1_struct_0(X1),k5_tmap_1(X1,k1_xboole_0)) = k6_tmap_1(X1,k1_xboole_0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_45,plain,
    ( k5_tmap_1(X1,k1_xboole_0) = u1_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_39])).

fof(c_0_46,plain,(
    ! [X17,X18] :
      ( v2_struct_0(X17)
      | ~ v2_pre_topc(X17)
      | ~ l1_pre_topc(X17)
      | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))
      | r2_hidden(X18,k5_tmap_1(X17,X18)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t102_tmap_1])])])])).

cnf(c_0_47,plain,
    ( u1_pre_topc(k6_tmap_1(X1,X2)) = k5_tmap_1(X1,X2)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X2,k9_setfam_1(u1_struct_0(X1))) ),
    inference(rw,[status(thm)],[c_0_42,c_0_18])).

cnf(c_0_48,negated_conjecture,
    ( m1_subset_1(esk3_0,k9_setfam_1(u1_struct_0(esk2_0))) ),
    inference(rw,[status(thm)],[c_0_43,c_0_18])).

cnf(c_0_49,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_50,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_51,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_52,negated_conjecture,
    ( v3_pre_topc(esk3_0,esk2_0)
    | g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)) = k6_tmap_1(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_53,plain,
    ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k6_tmap_1(X1,k1_xboole_0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_54,plain,
    ( v2_struct_0(X1)
    | r2_hidden(X2,k5_tmap_1(X1,X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_55,negated_conjecture,
    ( u1_pre_topc(k6_tmap_1(esk2_0,esk3_0)) = k5_tmap_1(esk2_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_49]),c_0_50])]),c_0_51])).

cnf(c_0_56,negated_conjecture,
    ( k6_tmap_1(esk2_0,esk3_0) = k6_tmap_1(esk2_0,k1_xboole_0)
    | v3_pre_topc(esk3_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_49]),c_0_50])]),c_0_51])).

fof(c_0_57,plain,(
    ! [X4,X5] :
      ( ( ~ v3_pre_topc(X5,X4)
        | r2_hidden(X5,u1_pre_topc(X4))
        | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X4)))
        | ~ l1_pre_topc(X4) )
      & ( ~ r2_hidden(X5,u1_pre_topc(X4))
        | v3_pre_topc(X5,X4)
        | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X4)))
        | ~ l1_pre_topc(X4) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_pre_topc])])])])).

cnf(c_0_58,plain,
    ( v2_struct_0(X1)
    | r2_hidden(X2,k5_tmap_1(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X2,k9_setfam_1(u1_struct_0(X1))) ),
    inference(rw,[status(thm)],[c_0_54,c_0_18])).

cnf(c_0_59,plain,
    ( u1_pre_topc(k6_tmap_1(X1,k1_xboole_0)) = k5_tmap_1(X1,k1_xboole_0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_47,c_0_39])).

cnf(c_0_60,negated_conjecture,
    ( u1_pre_topc(k6_tmap_1(esk2_0,k1_xboole_0)) = k5_tmap_1(esk2_0,esk3_0)
    | v3_pre_topc(esk3_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_61,plain,
    ( r2_hidden(X1,u1_pre_topc(X2))
    | ~ v3_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_62,negated_conjecture,
    ( r2_hidden(esk3_0,k5_tmap_1(esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_48]),c_0_49]),c_0_50])]),c_0_51])).

cnf(c_0_63,negated_conjecture,
    ( k5_tmap_1(esk2_0,esk3_0) = k5_tmap_1(esk2_0,k1_xboole_0)
    | v3_pre_topc(esk3_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_49]),c_0_50])]),c_0_51])).

cnf(c_0_64,plain,
    ( r2_hidden(X1,u1_pre_topc(X2))
    | ~ l1_pre_topc(X2)
    | ~ v3_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k9_setfam_1(u1_struct_0(X2))) ),
    inference(rw,[status(thm)],[c_0_61,c_0_18])).

cnf(c_0_65,plain,
    ( v3_pre_topc(X1,X2)
    | ~ r2_hidden(X1,u1_pre_topc(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_66,negated_conjecture,
    ( r2_hidden(esk3_0,k5_tmap_1(esk2_0,k1_xboole_0))
    | v3_pre_topc(esk3_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_67,negated_conjecture,
    ( r2_hidden(esk3_0,u1_pre_topc(esk2_0))
    | ~ v3_pre_topc(esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_48]),c_0_50])])).

cnf(c_0_68,plain,
    ( v3_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ r2_hidden(X1,u1_pre_topc(X2))
    | ~ m1_subset_1(X1,k9_setfam_1(u1_struct_0(X2))) ),
    inference(rw,[status(thm)],[c_0_65,c_0_18])).

cnf(c_0_69,negated_conjecture,
    ( r2_hidden(esk3_0,u1_pre_topc(esk2_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_45]),c_0_49]),c_0_50])]),c_0_51]),c_0_67])).

cnf(c_0_70,negated_conjecture,
    ( ~ v3_pre_topc(esk3_0,esk2_0)
    | g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)) != k6_tmap_1(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_71,negated_conjecture,
    ( v3_pre_topc(esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_48]),c_0_50])])).

cnf(c_0_72,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk2_0),k5_tmap_1(esk2_0,esk3_0)) = k6_tmap_1(esk2_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_48]),c_0_49]),c_0_50])]),c_0_51])).

cnf(c_0_73,negated_conjecture,
    ( k5_tmap_1(esk2_0,esk3_0) = u1_pre_topc(esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_69]),c_0_49]),c_0_48]),c_0_50])]),c_0_51])).

cnf(c_0_74,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)) != k6_tmap_1(esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_70,c_0_71])])).

cnf(c_0_75,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_72,c_0_73]),c_0_74]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:57:32 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_SE_CS_SP_PI_PS_S2S
% 0.13/0.38  # and selection function SelectNewComplexAHP.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.028 s
% 0.13/0.38  # Presaturation interreduction done
% 0.13/0.38  
% 0.13/0.38  # Proof found!
% 0.13/0.38  # SZS status Theorem
% 0.13/0.38  # SZS output start CNFRefutation
% 0.13/0.38  fof(cc1_tops_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v1_xboole_0(X2)=>v3_pre_topc(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_tops_1)).
% 0.13/0.38  fof(redefinition_k9_setfam_1, axiom, ![X1]:k9_setfam_1(X1)=k1_zfmisc_1(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_setfam_1)).
% 0.13/0.38  fof(rc1_connsp_1, axiom, ![X1]:(l1_pre_topc(X1)=>?[X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))&v1_xboole_0(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc1_connsp_1)).
% 0.13/0.38  fof(cc3_tops_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v1_xboole_0(X2)=>v3_tops_1(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc3_tops_1)).
% 0.13/0.38  fof(t97_tops_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>((v3_pre_topc(X2,X1)&v3_tops_1(X2,X1))=>X2=k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_tops_1)).
% 0.13/0.38  fof(d9_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k6_tmap_1(X1,X2)=g1_pre_topc(u1_struct_0(X1),k5_tmap_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_tmap_1)).
% 0.13/0.38  fof(t103_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(r2_hidden(X2,u1_pre_topc(X1))<=>u1_pre_topc(X1)=k5_tmap_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t103_tmap_1)).
% 0.13/0.38  fof(t106_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))=k6_tmap_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_tmap_1)).
% 0.13/0.38  fof(t5_pre_topc, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>r2_hidden(k1_xboole_0,u1_pre_topc(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_pre_topc)).
% 0.13/0.38  fof(t104_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(u1_struct_0(k6_tmap_1(X1,X2))=u1_struct_0(X1)&u1_pre_topc(k6_tmap_1(X1,X2))=k5_tmap_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t104_tmap_1)).
% 0.13/0.38  fof(t102_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>r2_hidden(X2,k5_tmap_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t102_tmap_1)).
% 0.13/0.38  fof(d5_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>r2_hidden(X2,u1_pre_topc(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_pre_topc)).
% 0.13/0.38  fof(c_0_12, plain, ![X7, X8]:(~v2_pre_topc(X7)|~l1_pre_topc(X7)|(~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X7)))|(~v1_xboole_0(X8)|v3_pre_topc(X8,X7)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_tops_1])])])).
% 0.13/0.38  fof(c_0_13, plain, ![X3]:k9_setfam_1(X3)=k1_zfmisc_1(X3), inference(variable_rename,[status(thm)],[redefinition_k9_setfam_1])).
% 0.13/0.38  fof(c_0_14, plain, ![X13]:((m1_subset_1(esk1_1(X13),k1_zfmisc_1(u1_struct_0(X13)))|~l1_pre_topc(X13))&(v1_xboole_0(esk1_1(X13))|~l1_pre_topc(X13))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[rc1_connsp_1])])])])).
% 0.13/0.38  fof(c_0_15, plain, ![X9, X10]:(~v2_pre_topc(X9)|~l1_pre_topc(X9)|(~m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9)))|(~v1_xboole_0(X10)|v3_tops_1(X10,X9)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc3_tops_1])])])).
% 0.13/0.38  fof(c_0_16, plain, ![X11, X12]:(~v2_pre_topc(X11)|~l1_pre_topc(X11)|(~m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X11)))|(~v3_pre_topc(X12,X11)|~v3_tops_1(X12,X11)|X12=k1_xboole_0))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t97_tops_1])])])).
% 0.13/0.38  cnf(c_0_17, plain, (v3_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v1_xboole_0(X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.38  cnf(c_0_18, plain, (k9_setfam_1(X1)=k1_zfmisc_1(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  cnf(c_0_19, plain, (m1_subset_1(esk1_1(X1),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.38  cnf(c_0_20, plain, (v3_tops_1(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v1_xboole_0(X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.38  cnf(c_0_21, plain, (X2=k1_xboole_0|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v3_pre_topc(X2,X1)|~v3_tops_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.38  cnf(c_0_22, plain, (v3_pre_topc(X2,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)|~v1_xboole_0(X2)|~m1_subset_1(X2,k9_setfam_1(u1_struct_0(X1)))), inference(rw,[status(thm)],[c_0_17, c_0_18])).
% 0.13/0.38  cnf(c_0_23, plain, (m1_subset_1(esk1_1(X1),k9_setfam_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(rw,[status(thm)],[c_0_19, c_0_18])).
% 0.13/0.38  cnf(c_0_24, plain, (v1_xboole_0(esk1_1(X1))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.38  cnf(c_0_25, plain, (v3_tops_1(X2,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)|~v1_xboole_0(X2)|~m1_subset_1(X2,k9_setfam_1(u1_struct_0(X1)))), inference(rw,[status(thm)],[c_0_20, c_0_18])).
% 0.13/0.38  fof(c_0_26, plain, ![X15, X16]:(v2_struct_0(X15)|~v2_pre_topc(X15)|~l1_pre_topc(X15)|(~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))|k6_tmap_1(X15,X16)=g1_pre_topc(u1_struct_0(X15),k5_tmap_1(X15,X16)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d9_tmap_1])])])])).
% 0.13/0.38  cnf(c_0_27, plain, (X2=k1_xboole_0|~l1_pre_topc(X1)|~v2_pre_topc(X1)|~v3_pre_topc(X2,X1)|~v3_tops_1(X2,X1)|~m1_subset_1(X2,k9_setfam_1(u1_struct_0(X1)))), inference(rw,[status(thm)],[c_0_21, c_0_18])).
% 0.13/0.38  cnf(c_0_28, plain, (v3_pre_topc(esk1_1(X1),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24])).
% 0.13/0.38  cnf(c_0_29, plain, (v3_tops_1(esk1_1(X1),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_23]), c_0_24])).
% 0.13/0.38  fof(c_0_30, plain, ![X19, X20]:((~r2_hidden(X20,u1_pre_topc(X19))|u1_pre_topc(X19)=k5_tmap_1(X19,X20)|~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))|(v2_struct_0(X19)|~v2_pre_topc(X19)|~l1_pre_topc(X19)))&(u1_pre_topc(X19)!=k5_tmap_1(X19,X20)|r2_hidden(X20,u1_pre_topc(X19))|~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))|(v2_struct_0(X19)|~v2_pre_topc(X19)|~l1_pre_topc(X19)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t103_tmap_1])])])])])).
% 0.13/0.38  fof(c_0_31, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))=k6_tmap_1(X1,X2))))), inference(assume_negation,[status(cth)],[t106_tmap_1])).
% 0.13/0.38  cnf(c_0_32, plain, (v2_struct_0(X1)|k6_tmap_1(X1,X2)=g1_pre_topc(u1_struct_0(X1),k5_tmap_1(X1,X2))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.13/0.38  cnf(c_0_33, plain, (esk1_1(X1)=k1_xboole_0|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_23]), c_0_28]), c_0_29])).
% 0.13/0.38  cnf(c_0_34, plain, (u1_pre_topc(X2)=k5_tmap_1(X2,X1)|v2_struct_0(X2)|~r2_hidden(X1,u1_pre_topc(X2))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.13/0.38  fof(c_0_35, plain, ![X6]:(~v2_pre_topc(X6)|~l1_pre_topc(X6)|r2_hidden(k1_xboole_0,u1_pre_topc(X6))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_pre_topc])])).
% 0.13/0.38  fof(c_0_36, plain, ![X21, X22]:((u1_struct_0(k6_tmap_1(X21,X22))=u1_struct_0(X21)|~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))|(v2_struct_0(X21)|~v2_pre_topc(X21)|~l1_pre_topc(X21)))&(u1_pre_topc(k6_tmap_1(X21,X22))=k5_tmap_1(X21,X22)|~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))|(v2_struct_0(X21)|~v2_pre_topc(X21)|~l1_pre_topc(X21)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t104_tmap_1])])])])])).
% 0.13/0.38  fof(c_0_37, negated_conjecture, (((~v2_struct_0(esk2_0)&v2_pre_topc(esk2_0))&l1_pre_topc(esk2_0))&(m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))&((~v3_pre_topc(esk3_0,esk2_0)|g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))!=k6_tmap_1(esk2_0,esk3_0))&(v3_pre_topc(esk3_0,esk2_0)|g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))=k6_tmap_1(esk2_0,esk3_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_31])])])])).
% 0.13/0.38  cnf(c_0_38, plain, (k6_tmap_1(X1,X2)=g1_pre_topc(u1_struct_0(X1),k5_tmap_1(X1,X2))|v2_struct_0(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)|~m1_subset_1(X2,k9_setfam_1(u1_struct_0(X1)))), inference(rw,[status(thm)],[c_0_32, c_0_18])).
% 0.13/0.38  cnf(c_0_39, plain, (m1_subset_1(k1_xboole_0,k9_setfam_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_23, c_0_33])).
% 0.13/0.38  cnf(c_0_40, plain, (u1_pre_topc(X2)=k5_tmap_1(X2,X1)|v2_struct_0(X2)|~l1_pre_topc(X2)|~v2_pre_topc(X2)|~r2_hidden(X1,u1_pre_topc(X2))|~m1_subset_1(X1,k9_setfam_1(u1_struct_0(X2)))), inference(rw,[status(thm)],[c_0_34, c_0_18])).
% 0.13/0.38  cnf(c_0_41, plain, (r2_hidden(k1_xboole_0,u1_pre_topc(X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.13/0.38  cnf(c_0_42, plain, (u1_pre_topc(k6_tmap_1(X1,X2))=k5_tmap_1(X1,X2)|v2_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.13/0.38  cnf(c_0_43, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.13/0.38  cnf(c_0_44, plain, (g1_pre_topc(u1_struct_0(X1),k5_tmap_1(X1,k1_xboole_0))=k6_tmap_1(X1,k1_xboole_0)|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.13/0.38  cnf(c_0_45, plain, (k5_tmap_1(X1,k1_xboole_0)=u1_pre_topc(X1)|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_39])).
% 0.13/0.38  fof(c_0_46, plain, ![X17, X18]:(v2_struct_0(X17)|~v2_pre_topc(X17)|~l1_pre_topc(X17)|(~m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))|r2_hidden(X18,k5_tmap_1(X17,X18)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t102_tmap_1])])])])).
% 0.13/0.38  cnf(c_0_47, plain, (u1_pre_topc(k6_tmap_1(X1,X2))=k5_tmap_1(X1,X2)|v2_struct_0(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)|~m1_subset_1(X2,k9_setfam_1(u1_struct_0(X1)))), inference(rw,[status(thm)],[c_0_42, c_0_18])).
% 0.13/0.38  cnf(c_0_48, negated_conjecture, (m1_subset_1(esk3_0,k9_setfam_1(u1_struct_0(esk2_0)))), inference(rw,[status(thm)],[c_0_43, c_0_18])).
% 0.13/0.38  cnf(c_0_49, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.13/0.38  cnf(c_0_50, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.13/0.38  cnf(c_0_51, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.13/0.38  cnf(c_0_52, negated_conjecture, (v3_pre_topc(esk3_0,esk2_0)|g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))=k6_tmap_1(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.13/0.38  cnf(c_0_53, plain, (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))=k6_tmap_1(X1,k1_xboole_0)|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.13/0.38  cnf(c_0_54, plain, (v2_struct_0(X1)|r2_hidden(X2,k5_tmap_1(X1,X2))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.13/0.38  cnf(c_0_55, negated_conjecture, (u1_pre_topc(k6_tmap_1(esk2_0,esk3_0))=k5_tmap_1(esk2_0,esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_49]), c_0_50])]), c_0_51])).
% 0.13/0.38  cnf(c_0_56, negated_conjecture, (k6_tmap_1(esk2_0,esk3_0)=k6_tmap_1(esk2_0,k1_xboole_0)|v3_pre_topc(esk3_0,esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_49]), c_0_50])]), c_0_51])).
% 0.13/0.38  fof(c_0_57, plain, ![X4, X5]:((~v3_pre_topc(X5,X4)|r2_hidden(X5,u1_pre_topc(X4))|~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X4)))|~l1_pre_topc(X4))&(~r2_hidden(X5,u1_pre_topc(X4))|v3_pre_topc(X5,X4)|~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X4)))|~l1_pre_topc(X4))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_pre_topc])])])])).
% 0.13/0.38  cnf(c_0_58, plain, (v2_struct_0(X1)|r2_hidden(X2,k5_tmap_1(X1,X2))|~l1_pre_topc(X1)|~v2_pre_topc(X1)|~m1_subset_1(X2,k9_setfam_1(u1_struct_0(X1)))), inference(rw,[status(thm)],[c_0_54, c_0_18])).
% 0.13/0.38  cnf(c_0_59, plain, (u1_pre_topc(k6_tmap_1(X1,k1_xboole_0))=k5_tmap_1(X1,k1_xboole_0)|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_47, c_0_39])).
% 0.13/0.38  cnf(c_0_60, negated_conjecture, (u1_pre_topc(k6_tmap_1(esk2_0,k1_xboole_0))=k5_tmap_1(esk2_0,esk3_0)|v3_pre_topc(esk3_0,esk2_0)), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.13/0.38  cnf(c_0_61, plain, (r2_hidden(X1,u1_pre_topc(X2))|~v3_pre_topc(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.13/0.38  cnf(c_0_62, negated_conjecture, (r2_hidden(esk3_0,k5_tmap_1(esk2_0,esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_48]), c_0_49]), c_0_50])]), c_0_51])).
% 0.13/0.38  cnf(c_0_63, negated_conjecture, (k5_tmap_1(esk2_0,esk3_0)=k5_tmap_1(esk2_0,k1_xboole_0)|v3_pre_topc(esk3_0,esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_49]), c_0_50])]), c_0_51])).
% 0.13/0.38  cnf(c_0_64, plain, (r2_hidden(X1,u1_pre_topc(X2))|~l1_pre_topc(X2)|~v3_pre_topc(X1,X2)|~m1_subset_1(X1,k9_setfam_1(u1_struct_0(X2)))), inference(rw,[status(thm)],[c_0_61, c_0_18])).
% 0.13/0.38  cnf(c_0_65, plain, (v3_pre_topc(X1,X2)|~r2_hidden(X1,u1_pre_topc(X2))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.13/0.38  cnf(c_0_66, negated_conjecture, (r2_hidden(esk3_0,k5_tmap_1(esk2_0,k1_xboole_0))|v3_pre_topc(esk3_0,esk2_0)), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 0.13/0.38  cnf(c_0_67, negated_conjecture, (r2_hidden(esk3_0,u1_pre_topc(esk2_0))|~v3_pre_topc(esk3_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_48]), c_0_50])])).
% 0.13/0.38  cnf(c_0_68, plain, (v3_pre_topc(X1,X2)|~l1_pre_topc(X2)|~r2_hidden(X1,u1_pre_topc(X2))|~m1_subset_1(X1,k9_setfam_1(u1_struct_0(X2)))), inference(rw,[status(thm)],[c_0_65, c_0_18])).
% 0.13/0.38  cnf(c_0_69, negated_conjecture, (r2_hidden(esk3_0,u1_pre_topc(esk2_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_45]), c_0_49]), c_0_50])]), c_0_51]), c_0_67])).
% 0.13/0.38  cnf(c_0_70, negated_conjecture, (~v3_pre_topc(esk3_0,esk2_0)|g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))!=k6_tmap_1(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.13/0.38  cnf(c_0_71, negated_conjecture, (v3_pre_topc(esk3_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_48]), c_0_50])])).
% 0.13/0.38  cnf(c_0_72, negated_conjecture, (g1_pre_topc(u1_struct_0(esk2_0),k5_tmap_1(esk2_0,esk3_0))=k6_tmap_1(esk2_0,esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_48]), c_0_49]), c_0_50])]), c_0_51])).
% 0.13/0.38  cnf(c_0_73, negated_conjecture, (k5_tmap_1(esk2_0,esk3_0)=u1_pre_topc(esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_69]), c_0_49]), c_0_48]), c_0_50])]), c_0_51])).
% 0.13/0.38  cnf(c_0_74, negated_conjecture, (g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))!=k6_tmap_1(esk2_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_70, c_0_71])])).
% 0.13/0.38  cnf(c_0_75, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_72, c_0_73]), c_0_74]), ['proof']).
% 0.13/0.38  # SZS output end CNFRefutation
% 0.13/0.38  # Proof object total steps             : 76
% 0.13/0.38  # Proof object clause steps            : 51
% 0.13/0.38  # Proof object formula steps           : 25
% 0.13/0.38  # Proof object conjectures             : 23
% 0.13/0.38  # Proof object clause conjectures      : 20
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 19
% 0.13/0.38  # Proof object initial formulas used   : 12
% 0.13/0.38  # Proof object generating inferences   : 19
% 0.13/0.38  # Proof object simplifying inferences  : 55
% 0.13/0.38  # Training examples: 0 positive, 0 negative
% 0.13/0.38  # Parsed axioms                        : 14
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 23
% 0.13/0.38  # Removed in clause preprocessing      : 1
% 0.13/0.38  # Initial clauses in saturation        : 22
% 0.13/0.38  # Processed clauses                    : 117
% 0.13/0.38  # ...of these trivial                  : 0
% 0.13/0.38  # ...subsumed                          : 17
% 0.13/0.38  # ...remaining for further processing  : 100
% 0.13/0.38  # Other redundant clauses eliminated   : 0
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 2
% 0.13/0.38  # Backward-rewritten                   : 18
% 0.13/0.38  # Generated clauses                    : 146
% 0.13/0.38  # ...of the previous two non-trivial   : 152
% 0.13/0.38  # Contextual simplify-reflections      : 7
% 0.13/0.38  # Paramodulations                      : 146
% 0.13/0.38  # Factorizations                       : 0
% 0.13/0.38  # Equation resolutions                 : 0
% 0.13/0.38  # Propositional unsat checks           : 0
% 0.13/0.38  #    Propositional check models        : 0
% 0.13/0.38  #    Propositional check unsatisfiable : 0
% 0.13/0.38  #    Propositional clauses             : 0
% 0.13/0.38  #    Propositional clauses after purity: 0
% 0.13/0.38  #    Propositional unsat core size     : 0
% 0.13/0.38  #    Propositional preprocessing time  : 0.000
% 0.13/0.38  #    Propositional encoding time       : 0.000
% 0.13/0.38  #    Propositional solver time         : 0.000
% 0.13/0.38  #    Success case prop preproc time    : 0.000
% 0.13/0.38  #    Success case prop encoding time   : 0.000
% 0.13/0.38  #    Success case prop solver time     : 0.000
% 0.13/0.38  # Current number of processed clauses  : 58
% 0.13/0.38  #    Positive orientable unit clauses  : 9
% 0.13/0.38  #    Positive unorientable unit clauses: 0
% 0.13/0.38  #    Negative unit clauses             : 3
% 0.13/0.38  #    Non-unit-clauses                  : 46
% 0.13/0.38  # Current number of unprocessed clauses: 74
% 0.13/0.38  # ...number of literals in the above   : 451
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 43
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 863
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 263
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 26
% 0.13/0.38  # Unit Clause-clause subsumption calls : 40
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 3
% 0.13/0.38  # BW rewrite match successes           : 3
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 6011
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.039 s
% 0.13/0.38  # System time              : 0.001 s
% 0.13/0.38  # Total time               : 0.040 s
% 0.13/0.38  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
