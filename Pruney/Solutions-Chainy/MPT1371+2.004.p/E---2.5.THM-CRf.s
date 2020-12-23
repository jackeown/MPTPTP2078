%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:14:16 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 272 expanded)
%              Number of clauses        :   38 (  84 expanded)
%              Number of leaves         :   10 (  71 expanded)
%              Depth                    :    9
%              Number of atoms          :  363 (2839 expanded)
%              Number of equality atoms :   26 ( 298 expanded)
%              Maximal formula depth    :   20 (   6 average)
%              Maximal clause size      :   46 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t26_compts_1,conjecture,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v2_pre_topc(X2)
            & l1_pre_topc(X2) )
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
             => ( ( v1_compts_1(X1)
                  & v8_pre_topc(X2)
                  & k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) = k2_struct_0(X1)
                  & k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) = k2_struct_0(X2)
                  & v2_funct_1(X3)
                  & v5_pre_topc(X3,X1,X2) )
               => v3_tops_2(X3,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_compts_1)).

fof(t24_compts_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( ( ~ v2_struct_0(X3)
                & l1_pre_topc(X3) )
             => ! [X4] :
                  ( ( v1_funct_1(X4)
                    & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X3))
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3)))) )
                 => ( ( v5_pre_topc(X4,X1,X3)
                      & k2_relset_1(u1_struct_0(X1),u1_struct_0(X3),X4) = k2_struct_0(X3)
                      & v2_compts_1(X2,X1) )
                   => v2_compts_1(k7_relset_1(u1_struct_0(X1),u1_struct_0(X3),X4,X2),X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_compts_1)).

fof(d12_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( l1_pre_topc(X2)
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
             => ( v5_pre_topc(X3,X1,X2)
              <=> ! [X4] :
                    ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
                   => ( v4_pre_topc(X4,X2)
                     => v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4),X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_pre_topc)).

fof(dt_k2_tops_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( v1_funct_1(k2_tops_2(X1,X2,X3))
        & v1_funct_2(k2_tops_2(X1,X2,X3),X2,X1)
        & m1_subset_1(k2_tops_2(X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_2)).

fof(t67_tops_2,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ! [X2] :
          ( l1_struct_0(X2)
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
             => ! [X4] :
                  ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) = k2_struct_0(X2)
                      & v2_funct_1(X3) )
                   => k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4) = k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3),X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_tops_2)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(t16_compts_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( ( v8_pre_topc(X1)
              & v2_compts_1(X2,X1) )
           => v4_pre_topc(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_compts_1)).

fof(dt_k7_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => m1_subset_1(k7_relset_1(X1,X2,X3,X4),k1_zfmisc_1(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relset_1)).

fof(t17_compts_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( ( v1_compts_1(X1)
              & v4_pre_topc(X2,X1) )
           => v2_compts_1(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_compts_1)).

fof(d5_tops_2,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( l1_pre_topc(X2)
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
             => ( v3_tops_2(X3,X1,X2)
              <=> ( k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) = k2_struct_0(X1)
                  & k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) = k2_struct_0(X2)
                  & v2_funct_1(X3)
                  & v5_pre_topc(X3,X1,X2)
                  & v5_pre_topc(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3),X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tops_2)).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1] :
        ( ( v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & v2_pre_topc(X2)
              & l1_pre_topc(X2) )
           => ! [X3] :
                ( ( v1_funct_1(X3)
                  & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
               => ( ( v1_compts_1(X1)
                    & v8_pre_topc(X2)
                    & k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) = k2_struct_0(X1)
                    & k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) = k2_struct_0(X2)
                    & v2_funct_1(X3)
                    & v5_pre_topc(X3,X1,X2) )
                 => v3_tops_2(X3,X1,X2) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t26_compts_1])).

fof(c_0_11,plain,(
    ! [X29,X30,X31,X32] :
      ( ~ l1_pre_topc(X29)
      | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))
      | v2_struct_0(X31)
      | ~ l1_pre_topc(X31)
      | ~ v1_funct_1(X32)
      | ~ v1_funct_2(X32,u1_struct_0(X29),u1_struct_0(X31))
      | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X29),u1_struct_0(X31))))
      | ~ v5_pre_topc(X32,X29,X31)
      | k2_relset_1(u1_struct_0(X29),u1_struct_0(X31),X32) != k2_struct_0(X31)
      | ~ v2_compts_1(X30,X29)
      | v2_compts_1(k7_relset_1(u1_struct_0(X29),u1_struct_0(X31),X32,X30),X31) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t24_compts_1])])])])).

fof(c_0_12,negated_conjecture,
    ( v2_pre_topc(esk2_0)
    & l1_pre_topc(esk2_0)
    & ~ v2_struct_0(esk3_0)
    & v2_pre_topc(esk3_0)
    & l1_pre_topc(esk3_0)
    & v1_funct_1(esk4_0)
    & v1_funct_2(esk4_0,u1_struct_0(esk2_0),u1_struct_0(esk3_0))
    & m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0))))
    & v1_compts_1(esk2_0)
    & v8_pre_topc(esk3_0)
    & k1_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0) = k2_struct_0(esk2_0)
    & k2_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0) = k2_struct_0(esk3_0)
    & v2_funct_1(esk4_0)
    & v5_pre_topc(esk4_0,esk2_0,esk3_0)
    & ~ v3_tops_2(esk4_0,esk2_0,esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])).

fof(c_0_13,plain,(
    ! [X9,X10,X11,X12] :
      ( ( ~ v5_pre_topc(X11,X9,X10)
        | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X10)))
        | ~ v4_pre_topc(X12,X10)
        | v4_pre_topc(k8_relset_1(u1_struct_0(X9),u1_struct_0(X10),X11,X12),X9)
        | ~ v1_funct_1(X11)
        | ~ v1_funct_2(X11,u1_struct_0(X9),u1_struct_0(X10))
        | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X9),u1_struct_0(X10))))
        | ~ l1_pre_topc(X10)
        | ~ l1_pre_topc(X9) )
      & ( m1_subset_1(esk1_3(X9,X10,X11),k1_zfmisc_1(u1_struct_0(X10)))
        | v5_pre_topc(X11,X9,X10)
        | ~ v1_funct_1(X11)
        | ~ v1_funct_2(X11,u1_struct_0(X9),u1_struct_0(X10))
        | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X9),u1_struct_0(X10))))
        | ~ l1_pre_topc(X10)
        | ~ l1_pre_topc(X9) )
      & ( v4_pre_topc(esk1_3(X9,X10,X11),X10)
        | v5_pre_topc(X11,X9,X10)
        | ~ v1_funct_1(X11)
        | ~ v1_funct_2(X11,u1_struct_0(X9),u1_struct_0(X10))
        | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X9),u1_struct_0(X10))))
        | ~ l1_pre_topc(X10)
        | ~ l1_pre_topc(X9) )
      & ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X9),u1_struct_0(X10),X11,esk1_3(X9,X10,X11)),X9)
        | v5_pre_topc(X11,X9,X10)
        | ~ v1_funct_1(X11)
        | ~ v1_funct_2(X11,u1_struct_0(X9),u1_struct_0(X10))
        | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X9),u1_struct_0(X10))))
        | ~ l1_pre_topc(X10)
        | ~ l1_pre_topc(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_pre_topc])])])])])).

fof(c_0_14,plain,(
    ! [X18,X19,X20] :
      ( ( v1_funct_1(k2_tops_2(X18,X19,X20))
        | ~ v1_funct_1(X20)
        | ~ v1_funct_2(X20,X18,X19)
        | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19))) )
      & ( v1_funct_2(k2_tops_2(X18,X19,X20),X19,X18)
        | ~ v1_funct_1(X20)
        | ~ v1_funct_2(X20,X18,X19)
        | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19))) )
      & ( m1_subset_1(k2_tops_2(X18,X19,X20),k1_zfmisc_1(k2_zfmisc_1(X19,X18)))
        | ~ v1_funct_1(X20)
        | ~ v1_funct_2(X20,X18,X19)
        | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_tops_2])])])).

fof(c_0_15,plain,(
    ! [X21,X22,X23,X24] :
      ( ~ l1_struct_0(X21)
      | ~ l1_struct_0(X22)
      | ~ v1_funct_1(X23)
      | ~ v1_funct_2(X23,u1_struct_0(X21),u1_struct_0(X22))
      | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X21),u1_struct_0(X22))))
      | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X21)))
      | k2_relset_1(u1_struct_0(X21),u1_struct_0(X22),X23) != k2_struct_0(X22)
      | ~ v2_funct_1(X23)
      | k7_relset_1(u1_struct_0(X21),u1_struct_0(X22),X23,X24) = k8_relset_1(u1_struct_0(X22),u1_struct_0(X21),k2_tops_2(u1_struct_0(X21),u1_struct_0(X22),X23),X24) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t67_tops_2])])])).

fof(c_0_16,plain,(
    ! [X14] :
      ( ~ l1_pre_topc(X14)
      | l1_struct_0(X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

fof(c_0_17,plain,(
    ! [X25,X26] :
      ( ~ v2_pre_topc(X25)
      | ~ l1_pre_topc(X25)
      | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))
      | ~ v8_pre_topc(X25)
      | ~ v2_compts_1(X26,X25)
      | v4_pre_topc(X26,X25) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t16_compts_1])])])).

cnf(c_0_18,plain,
    ( v2_struct_0(X3)
    | v2_compts_1(k7_relset_1(u1_struct_0(X1),u1_struct_0(X3),X4,X2),X3)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X3)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
    | ~ v5_pre_topc(X4,X1,X3)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X3),X4) != k2_struct_0(X3)
    | ~ v2_compts_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,negated_conjecture,
    ( k2_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0) = k2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_21,negated_conjecture,
    ( v5_pre_topc(esk4_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_22,negated_conjecture,
    ( v1_funct_2(esk4_0,u1_struct_0(esk2_0),u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_23,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_24,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_25,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_26,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_27,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X2)))
    | v5_pre_topc(X3,X1,X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_28,plain,
    ( m1_subset_1(k2_tops_2(X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_29,plain,
    ( v1_funct_1(k2_tops_2(X1,X2,X3))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_30,plain,
    ( v1_funct_2(k2_tops_2(X1,X2,X3),X2,X1)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_31,plain,
    ( v5_pre_topc(X3,X1,X2)
    | ~ v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,esk1_3(X1,X2,X3)),X1)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_32,plain,
    ( k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4) = k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3),X4)
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) != k2_struct_0(X2)
    | ~ v2_funct_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_33,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_34,plain,
    ( v4_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v8_pre_topc(X1)
    | ~ v2_compts_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_35,negated_conjecture,
    ( v2_compts_1(k7_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0,X1),esk3_0)
    | ~ v2_compts_1(X1,esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20]),c_0_21]),c_0_22]),c_0_23]),c_0_24]),c_0_25])]),c_0_26])).

cnf(c_0_36,negated_conjecture,
    ( v8_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_37,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_38,plain,
    ( v5_pre_topc(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3),X2,X1)
    | m1_subset_1(esk1_3(X2,X1,k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3)),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_1(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29]),c_0_30])).

cnf(c_0_39,plain,
    ( v5_pre_topc(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3),X2,X1)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) != k2_struct_0(X2)
    | ~ v2_funct_1(X3)
    | ~ v4_pre_topc(k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,esk1_3(X2,X1,k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3))),X2)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_1(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_27]),c_0_28]),c_0_29]),c_0_30]),c_0_33]),c_0_33])).

cnf(c_0_40,negated_conjecture,
    ( v4_pre_topc(k7_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0,X1),esk3_0)
    | ~ v2_compts_1(X1,esk2_0)
    | ~ m1_subset_1(k7_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0,X1),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36]),c_0_37]),c_0_24])])).

cnf(c_0_41,negated_conjecture,
    ( v2_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_42,negated_conjecture,
    ( v5_pre_topc(k2_tops_2(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0),esk3_0,esk2_0)
    | m1_subset_1(esk1_3(esk3_0,esk2_0,k2_tops_2(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0)),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_19]),c_0_22]),c_0_23]),c_0_25]),c_0_24])])).

fof(c_0_43,plain,(
    ! [X5,X6,X7,X8] :
      ( ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
      | m1_subset_1(k7_relset_1(X5,X6,X7,X8),k1_zfmisc_1(X6)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relset_1])])).

cnf(c_0_44,plain,
    ( v4_pre_topc(esk1_3(X1,X2,X3),X2)
    | v5_pre_topc(X3,X1,X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_45,negated_conjecture,
    ( v5_pre_topc(k2_tops_2(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0),esk3_0,esk2_0)
    | ~ v2_compts_1(esk1_3(esk3_0,esk2_0,k2_tops_2(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0)),esk2_0)
    | ~ m1_subset_1(k7_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0,esk1_3(esk3_0,esk2_0,k2_tops_2(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0))),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_20]),c_0_41]),c_0_22]),c_0_23]),c_0_25]),c_0_24]),c_0_19])]),c_0_42])).

cnf(c_0_46,plain,
    ( m1_subset_1(k7_relset_1(X2,X3,X1,X4),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

fof(c_0_47,plain,(
    ! [X27,X28] :
      ( ~ l1_pre_topc(X27)
      | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))
      | ~ v1_compts_1(X27)
      | ~ v4_pre_topc(X28,X27)
      | v2_compts_1(X28,X27) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t17_compts_1])])])).

cnf(c_0_48,plain,
    ( v4_pre_topc(esk1_3(X1,X2,k2_tops_2(u1_struct_0(X2),u1_struct_0(X1),X3)),X2)
    | v5_pre_topc(k2_tops_2(u1_struct_0(X2),u1_struct_0(X1),X3),X1,X2)
    | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
    | ~ v1_funct_1(X3)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_28]),c_0_29]),c_0_30])).

fof(c_0_49,plain,(
    ! [X15,X16,X17] :
      ( ( k1_relset_1(u1_struct_0(X15),u1_struct_0(X16),X17) = k2_struct_0(X15)
        | ~ v3_tops_2(X17,X15,X16)
        | ~ v1_funct_1(X17)
        | ~ v1_funct_2(X17,u1_struct_0(X15),u1_struct_0(X16))
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),u1_struct_0(X16))))
        | ~ l1_pre_topc(X16)
        | ~ l1_pre_topc(X15) )
      & ( k2_relset_1(u1_struct_0(X15),u1_struct_0(X16),X17) = k2_struct_0(X16)
        | ~ v3_tops_2(X17,X15,X16)
        | ~ v1_funct_1(X17)
        | ~ v1_funct_2(X17,u1_struct_0(X15),u1_struct_0(X16))
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),u1_struct_0(X16))))
        | ~ l1_pre_topc(X16)
        | ~ l1_pre_topc(X15) )
      & ( v2_funct_1(X17)
        | ~ v3_tops_2(X17,X15,X16)
        | ~ v1_funct_1(X17)
        | ~ v1_funct_2(X17,u1_struct_0(X15),u1_struct_0(X16))
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),u1_struct_0(X16))))
        | ~ l1_pre_topc(X16)
        | ~ l1_pre_topc(X15) )
      & ( v5_pre_topc(X17,X15,X16)
        | ~ v3_tops_2(X17,X15,X16)
        | ~ v1_funct_1(X17)
        | ~ v1_funct_2(X17,u1_struct_0(X15),u1_struct_0(X16))
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),u1_struct_0(X16))))
        | ~ l1_pre_topc(X16)
        | ~ l1_pre_topc(X15) )
      & ( v5_pre_topc(k2_tops_2(u1_struct_0(X15),u1_struct_0(X16),X17),X16,X15)
        | ~ v3_tops_2(X17,X15,X16)
        | ~ v1_funct_1(X17)
        | ~ v1_funct_2(X17,u1_struct_0(X15),u1_struct_0(X16))
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),u1_struct_0(X16))))
        | ~ l1_pre_topc(X16)
        | ~ l1_pre_topc(X15) )
      & ( k1_relset_1(u1_struct_0(X15),u1_struct_0(X16),X17) != k2_struct_0(X15)
        | k2_relset_1(u1_struct_0(X15),u1_struct_0(X16),X17) != k2_struct_0(X16)
        | ~ v2_funct_1(X17)
        | ~ v5_pre_topc(X17,X15,X16)
        | ~ v5_pre_topc(k2_tops_2(u1_struct_0(X15),u1_struct_0(X16),X17),X16,X15)
        | v3_tops_2(X17,X15,X16)
        | ~ v1_funct_1(X17)
        | ~ v1_funct_2(X17,u1_struct_0(X15),u1_struct_0(X16))
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),u1_struct_0(X16))))
        | ~ l1_pre_topc(X16)
        | ~ l1_pre_topc(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_tops_2])])])])).

cnf(c_0_50,negated_conjecture,
    ( v5_pre_topc(k2_tops_2(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0),esk3_0,esk2_0)
    | ~ v2_compts_1(esk1_3(esk3_0,esk2_0,k2_tops_2(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0)),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_19])])).

cnf(c_0_51,plain,
    ( v2_compts_1(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_compts_1(X1)
    | ~ v4_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_52,negated_conjecture,
    ( v1_compts_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_53,negated_conjecture,
    ( v4_pre_topc(esk1_3(esk3_0,esk2_0,k2_tops_2(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0)),esk2_0)
    | v5_pre_topc(k2_tops_2(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0),esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_19]),c_0_22]),c_0_23]),c_0_25]),c_0_24])])).

cnf(c_0_54,plain,
    ( v3_tops_2(X3,X1,X2)
    | k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) != k2_struct_0(X1)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) != k2_struct_0(X2)
    | ~ v2_funct_1(X3)
    | ~ v5_pre_topc(X3,X1,X2)
    | ~ v5_pre_topc(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3),X2,X1)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_55,negated_conjecture,
    ( v5_pre_topc(k2_tops_2(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0),esk3_0,esk2_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_52]),c_0_25])]),c_0_42]),c_0_53])).

cnf(c_0_56,negated_conjecture,
    ( k1_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0) = k2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_57,negated_conjecture,
    ( ~ v3_tops_2(esk4_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_58,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_56]),c_0_20]),c_0_41]),c_0_21]),c_0_22]),c_0_23]),c_0_24]),c_0_25]),c_0_19])]),c_0_57]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:41:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_AE_CS_SP_PS_S0V
% 0.19/0.38  # and selection function PSelectComplexExceptRRHorn.
% 0.19/0.38  #
% 0.19/0.38  # Preprocessing time       : 0.029 s
% 0.19/0.38  # Presaturation interreduction done
% 0.19/0.38  
% 0.19/0.38  # Proof found!
% 0.19/0.38  # SZS status Theorem
% 0.19/0.38  # SZS output start CNFRefutation
% 0.19/0.38  fof(t26_compts_1, conjecture, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>((((((v1_compts_1(X1)&v8_pre_topc(X2))&k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)=k2_struct_0(X1))&k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)=k2_struct_0(X2))&v2_funct_1(X3))&v5_pre_topc(X3,X1,X2))=>v3_tops_2(X3,X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_compts_1)).
% 0.19/0.38  fof(t24_compts_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:((~(v2_struct_0(X3))&l1_pre_topc(X3))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X3)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3)))))=>(((v5_pre_topc(X4,X1,X3)&k2_relset_1(u1_struct_0(X1),u1_struct_0(X3),X4)=k2_struct_0(X3))&v2_compts_1(X2,X1))=>v2_compts_1(k7_relset_1(u1_struct_0(X1),u1_struct_0(X3),X4,X2),X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_compts_1)).
% 0.19/0.38  fof(d12_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(l1_pre_topc(X2)=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>(v5_pre_topc(X3,X1,X2)<=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))=>(v4_pre_topc(X4,X2)=>v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4),X1))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_pre_topc)).
% 0.19/0.38  fof(dt_k2_tops_2, axiom, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((v1_funct_1(k2_tops_2(X1,X2,X3))&v1_funct_2(k2_tops_2(X1,X2,X3),X2,X1))&m1_subset_1(k2_tops_2(X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_2)).
% 0.19/0.38  fof(t67_tops_2, axiom, ![X1]:(l1_struct_0(X1)=>![X2]:(l1_struct_0(X2)=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>((k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)=k2_struct_0(X2)&v2_funct_1(X3))=>k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4)=k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3),X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_tops_2)).
% 0.19/0.38  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.19/0.38  fof(t16_compts_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>((v8_pre_topc(X1)&v2_compts_1(X2,X1))=>v4_pre_topc(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_compts_1)).
% 0.19/0.38  fof(dt_k7_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>m1_subset_1(k7_relset_1(X1,X2,X3,X4),k1_zfmisc_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relset_1)).
% 0.19/0.38  fof(t17_compts_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>((v1_compts_1(X1)&v4_pre_topc(X2,X1))=>v2_compts_1(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_compts_1)).
% 0.19/0.38  fof(d5_tops_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(l1_pre_topc(X2)=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>(v3_tops_2(X3,X1,X2)<=>((((k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)=k2_struct_0(X1)&k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)=k2_struct_0(X2))&v2_funct_1(X3))&v5_pre_topc(X3,X1,X2))&v5_pre_topc(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3),X2,X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tops_2)).
% 0.19/0.38  fof(c_0_10, negated_conjecture, ~(![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>((((((v1_compts_1(X1)&v8_pre_topc(X2))&k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)=k2_struct_0(X1))&k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)=k2_struct_0(X2))&v2_funct_1(X3))&v5_pre_topc(X3,X1,X2))=>v3_tops_2(X3,X1,X2)))))), inference(assume_negation,[status(cth)],[t26_compts_1])).
% 0.19/0.38  fof(c_0_11, plain, ![X29, X30, X31, X32]:(~l1_pre_topc(X29)|(~m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))|(v2_struct_0(X31)|~l1_pre_topc(X31)|(~v1_funct_1(X32)|~v1_funct_2(X32,u1_struct_0(X29),u1_struct_0(X31))|~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X29),u1_struct_0(X31))))|(~v5_pre_topc(X32,X29,X31)|k2_relset_1(u1_struct_0(X29),u1_struct_0(X31),X32)!=k2_struct_0(X31)|~v2_compts_1(X30,X29)|v2_compts_1(k7_relset_1(u1_struct_0(X29),u1_struct_0(X31),X32,X30),X31)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t24_compts_1])])])])).
% 0.19/0.38  fof(c_0_12, negated_conjecture, ((v2_pre_topc(esk2_0)&l1_pre_topc(esk2_0))&(((~v2_struct_0(esk3_0)&v2_pre_topc(esk3_0))&l1_pre_topc(esk3_0))&(((v1_funct_1(esk4_0)&v1_funct_2(esk4_0,u1_struct_0(esk2_0),u1_struct_0(esk3_0)))&m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0)))))&((((((v1_compts_1(esk2_0)&v8_pre_topc(esk3_0))&k1_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0)=k2_struct_0(esk2_0))&k2_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0)=k2_struct_0(esk3_0))&v2_funct_1(esk4_0))&v5_pre_topc(esk4_0,esk2_0,esk3_0))&~v3_tops_2(esk4_0,esk2_0,esk3_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])).
% 0.19/0.38  fof(c_0_13, plain, ![X9, X10, X11, X12]:((~v5_pre_topc(X11,X9,X10)|(~m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X10)))|(~v4_pre_topc(X12,X10)|v4_pre_topc(k8_relset_1(u1_struct_0(X9),u1_struct_0(X10),X11,X12),X9)))|(~v1_funct_1(X11)|~v1_funct_2(X11,u1_struct_0(X9),u1_struct_0(X10))|~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X9),u1_struct_0(X10)))))|~l1_pre_topc(X10)|~l1_pre_topc(X9))&((m1_subset_1(esk1_3(X9,X10,X11),k1_zfmisc_1(u1_struct_0(X10)))|v5_pre_topc(X11,X9,X10)|(~v1_funct_1(X11)|~v1_funct_2(X11,u1_struct_0(X9),u1_struct_0(X10))|~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X9),u1_struct_0(X10)))))|~l1_pre_topc(X10)|~l1_pre_topc(X9))&((v4_pre_topc(esk1_3(X9,X10,X11),X10)|v5_pre_topc(X11,X9,X10)|(~v1_funct_1(X11)|~v1_funct_2(X11,u1_struct_0(X9),u1_struct_0(X10))|~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X9),u1_struct_0(X10)))))|~l1_pre_topc(X10)|~l1_pre_topc(X9))&(~v4_pre_topc(k8_relset_1(u1_struct_0(X9),u1_struct_0(X10),X11,esk1_3(X9,X10,X11)),X9)|v5_pre_topc(X11,X9,X10)|(~v1_funct_1(X11)|~v1_funct_2(X11,u1_struct_0(X9),u1_struct_0(X10))|~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X9),u1_struct_0(X10)))))|~l1_pre_topc(X10)|~l1_pre_topc(X9))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_pre_topc])])])])])).
% 0.19/0.38  fof(c_0_14, plain, ![X18, X19, X20]:(((v1_funct_1(k2_tops_2(X18,X19,X20))|(~v1_funct_1(X20)|~v1_funct_2(X20,X18,X19)|~m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19)))))&(v1_funct_2(k2_tops_2(X18,X19,X20),X19,X18)|(~v1_funct_1(X20)|~v1_funct_2(X20,X18,X19)|~m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19))))))&(m1_subset_1(k2_tops_2(X18,X19,X20),k1_zfmisc_1(k2_zfmisc_1(X19,X18)))|(~v1_funct_1(X20)|~v1_funct_2(X20,X18,X19)|~m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_tops_2])])])).
% 0.19/0.38  fof(c_0_15, plain, ![X21, X22, X23, X24]:(~l1_struct_0(X21)|(~l1_struct_0(X22)|(~v1_funct_1(X23)|~v1_funct_2(X23,u1_struct_0(X21),u1_struct_0(X22))|~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X21),u1_struct_0(X22))))|(~m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X21)))|(k2_relset_1(u1_struct_0(X21),u1_struct_0(X22),X23)!=k2_struct_0(X22)|~v2_funct_1(X23)|k7_relset_1(u1_struct_0(X21),u1_struct_0(X22),X23,X24)=k8_relset_1(u1_struct_0(X22),u1_struct_0(X21),k2_tops_2(u1_struct_0(X21),u1_struct_0(X22),X23),X24)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t67_tops_2])])])).
% 0.19/0.38  fof(c_0_16, plain, ![X14]:(~l1_pre_topc(X14)|l1_struct_0(X14)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.19/0.38  fof(c_0_17, plain, ![X25, X26]:(~v2_pre_topc(X25)|~l1_pre_topc(X25)|(~m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))|(~v8_pre_topc(X25)|~v2_compts_1(X26,X25)|v4_pre_topc(X26,X25)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t16_compts_1])])])).
% 0.19/0.38  cnf(c_0_18, plain, (v2_struct_0(X3)|v2_compts_1(k7_relset_1(u1_struct_0(X1),u1_struct_0(X3),X4,X2),X3)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X3)|~v1_funct_1(X4)|~v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X3))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))|~v5_pre_topc(X4,X1,X3)|k2_relset_1(u1_struct_0(X1),u1_struct_0(X3),X4)!=k2_struct_0(X3)|~v2_compts_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.38  cnf(c_0_19, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0))))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.38  cnf(c_0_20, negated_conjecture, (k2_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0)=k2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.38  cnf(c_0_21, negated_conjecture, (v5_pre_topc(esk4_0,esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.38  cnf(c_0_22, negated_conjecture, (v1_funct_2(esk4_0,u1_struct_0(esk2_0),u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.38  cnf(c_0_23, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.38  cnf(c_0_24, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.38  cnf(c_0_25, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.38  cnf(c_0_26, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.38  cnf(c_0_27, plain, (m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X2)))|v5_pre_topc(X3,X1,X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.38  cnf(c_0_28, plain, (m1_subset_1(k2_tops_2(X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))|~v1_funct_1(X3)|~v1_funct_2(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.38  cnf(c_0_29, plain, (v1_funct_1(k2_tops_2(X1,X2,X3))|~v1_funct_1(X3)|~v1_funct_2(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.38  cnf(c_0_30, plain, (v1_funct_2(k2_tops_2(X1,X2,X3),X2,X1)|~v1_funct_1(X3)|~v1_funct_2(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.38  cnf(c_0_31, plain, (v5_pre_topc(X3,X1,X2)|~v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,esk1_3(X1,X2,X3)),X1)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.38  cnf(c_0_32, plain, (k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4)=k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3),X4)|~l1_struct_0(X1)|~l1_struct_0(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))|k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)!=k2_struct_0(X2)|~v2_funct_1(X3)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.38  cnf(c_0_33, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.38  cnf(c_0_34, plain, (v4_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v8_pre_topc(X1)|~v2_compts_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.38  cnf(c_0_35, negated_conjecture, (v2_compts_1(k7_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0,X1),esk3_0)|~v2_compts_1(X1,esk2_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_20]), c_0_21]), c_0_22]), c_0_23]), c_0_24]), c_0_25])]), c_0_26])).
% 0.19/0.38  cnf(c_0_36, negated_conjecture, (v8_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.38  cnf(c_0_37, negated_conjecture, (v2_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.38  cnf(c_0_38, plain, (v5_pre_topc(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3),X2,X1)|m1_subset_1(esk1_3(X2,X1,k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3)),k1_zfmisc_1(u1_struct_0(X1)))|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~v1_funct_1(X3)|~l1_pre_topc(X1)|~l1_pre_topc(X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_29]), c_0_30])).
% 0.19/0.38  cnf(c_0_39, plain, (v5_pre_topc(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3),X2,X1)|k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)!=k2_struct_0(X2)|~v2_funct_1(X3)|~v4_pre_topc(k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,esk1_3(X2,X1,k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3))),X2)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~v1_funct_1(X3)|~l1_pre_topc(X1)|~l1_pre_topc(X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_27]), c_0_28]), c_0_29]), c_0_30]), c_0_33]), c_0_33])).
% 0.19/0.38  cnf(c_0_40, negated_conjecture, (v4_pre_topc(k7_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0,X1),esk3_0)|~v2_compts_1(X1,esk2_0)|~m1_subset_1(k7_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0,X1),k1_zfmisc_1(u1_struct_0(esk3_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_36]), c_0_37]), c_0_24])])).
% 0.19/0.38  cnf(c_0_41, negated_conjecture, (v2_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.38  cnf(c_0_42, negated_conjecture, (v5_pre_topc(k2_tops_2(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0),esk3_0,esk2_0)|m1_subset_1(esk1_3(esk3_0,esk2_0,k2_tops_2(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0)),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_19]), c_0_22]), c_0_23]), c_0_25]), c_0_24])])).
% 0.19/0.38  fof(c_0_43, plain, ![X5, X6, X7, X8]:(~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))|m1_subset_1(k7_relset_1(X5,X6,X7,X8),k1_zfmisc_1(X6))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relset_1])])).
% 0.19/0.38  cnf(c_0_44, plain, (v4_pre_topc(esk1_3(X1,X2,X3),X2)|v5_pre_topc(X3,X1,X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.38  cnf(c_0_45, negated_conjecture, (v5_pre_topc(k2_tops_2(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0),esk3_0,esk2_0)|~v2_compts_1(esk1_3(esk3_0,esk2_0,k2_tops_2(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0)),esk2_0)|~m1_subset_1(k7_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0,esk1_3(esk3_0,esk2_0,k2_tops_2(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0))),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_20]), c_0_41]), c_0_22]), c_0_23]), c_0_25]), c_0_24]), c_0_19])]), c_0_42])).
% 0.19/0.38  cnf(c_0_46, plain, (m1_subset_1(k7_relset_1(X2,X3,X1,X4),k1_zfmisc_1(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.19/0.38  fof(c_0_47, plain, ![X27, X28]:(~l1_pre_topc(X27)|(~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))|(~v1_compts_1(X27)|~v4_pre_topc(X28,X27)|v2_compts_1(X28,X27)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t17_compts_1])])])).
% 0.19/0.38  cnf(c_0_48, plain, (v4_pre_topc(esk1_3(X1,X2,k2_tops_2(u1_struct_0(X2),u1_struct_0(X1),X3)),X2)|v5_pre_topc(k2_tops_2(u1_struct_0(X2),u1_struct_0(X1),X3),X1,X2)|~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))|~v1_funct_1(X3)|~l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_28]), c_0_29]), c_0_30])).
% 0.19/0.38  fof(c_0_49, plain, ![X15, X16, X17]:((((((k1_relset_1(u1_struct_0(X15),u1_struct_0(X16),X17)=k2_struct_0(X15)|~v3_tops_2(X17,X15,X16)|(~v1_funct_1(X17)|~v1_funct_2(X17,u1_struct_0(X15),u1_struct_0(X16))|~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),u1_struct_0(X16)))))|~l1_pre_topc(X16)|~l1_pre_topc(X15))&(k2_relset_1(u1_struct_0(X15),u1_struct_0(X16),X17)=k2_struct_0(X16)|~v3_tops_2(X17,X15,X16)|(~v1_funct_1(X17)|~v1_funct_2(X17,u1_struct_0(X15),u1_struct_0(X16))|~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),u1_struct_0(X16)))))|~l1_pre_topc(X16)|~l1_pre_topc(X15)))&(v2_funct_1(X17)|~v3_tops_2(X17,X15,X16)|(~v1_funct_1(X17)|~v1_funct_2(X17,u1_struct_0(X15),u1_struct_0(X16))|~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),u1_struct_0(X16)))))|~l1_pre_topc(X16)|~l1_pre_topc(X15)))&(v5_pre_topc(X17,X15,X16)|~v3_tops_2(X17,X15,X16)|(~v1_funct_1(X17)|~v1_funct_2(X17,u1_struct_0(X15),u1_struct_0(X16))|~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),u1_struct_0(X16)))))|~l1_pre_topc(X16)|~l1_pre_topc(X15)))&(v5_pre_topc(k2_tops_2(u1_struct_0(X15),u1_struct_0(X16),X17),X16,X15)|~v3_tops_2(X17,X15,X16)|(~v1_funct_1(X17)|~v1_funct_2(X17,u1_struct_0(X15),u1_struct_0(X16))|~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),u1_struct_0(X16)))))|~l1_pre_topc(X16)|~l1_pre_topc(X15)))&(k1_relset_1(u1_struct_0(X15),u1_struct_0(X16),X17)!=k2_struct_0(X15)|k2_relset_1(u1_struct_0(X15),u1_struct_0(X16),X17)!=k2_struct_0(X16)|~v2_funct_1(X17)|~v5_pre_topc(X17,X15,X16)|~v5_pre_topc(k2_tops_2(u1_struct_0(X15),u1_struct_0(X16),X17),X16,X15)|v3_tops_2(X17,X15,X16)|(~v1_funct_1(X17)|~v1_funct_2(X17,u1_struct_0(X15),u1_struct_0(X16))|~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),u1_struct_0(X16)))))|~l1_pre_topc(X16)|~l1_pre_topc(X15))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_tops_2])])])])).
% 0.19/0.38  cnf(c_0_50, negated_conjecture, (v5_pre_topc(k2_tops_2(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0),esk3_0,esk2_0)|~v2_compts_1(esk1_3(esk3_0,esk2_0,k2_tops_2(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0)),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_19])])).
% 0.19/0.38  cnf(c_0_51, plain, (v2_compts_1(X2,X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v1_compts_1(X1)|~v4_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.19/0.38  cnf(c_0_52, negated_conjecture, (v1_compts_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.38  cnf(c_0_53, negated_conjecture, (v4_pre_topc(esk1_3(esk3_0,esk2_0,k2_tops_2(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0)),esk2_0)|v5_pre_topc(k2_tops_2(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0),esk3_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_19]), c_0_22]), c_0_23]), c_0_25]), c_0_24])])).
% 0.19/0.38  cnf(c_0_54, plain, (v3_tops_2(X3,X1,X2)|k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)!=k2_struct_0(X1)|k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)!=k2_struct_0(X2)|~v2_funct_1(X3)|~v5_pre_topc(X3,X1,X2)|~v5_pre_topc(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3),X2,X1)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.19/0.38  cnf(c_0_55, negated_conjecture, (v5_pre_topc(k2_tops_2(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0),esk3_0,esk2_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_52]), c_0_25])]), c_0_42]), c_0_53])).
% 0.19/0.38  cnf(c_0_56, negated_conjecture, (k1_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0)=k2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.38  cnf(c_0_57, negated_conjecture, (~v3_tops_2(esk4_0,esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.38  cnf(c_0_58, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_56]), c_0_20]), c_0_41]), c_0_21]), c_0_22]), c_0_23]), c_0_24]), c_0_25]), c_0_19])]), c_0_57]), ['proof']).
% 0.19/0.38  # SZS output end CNFRefutation
% 0.19/0.38  # Proof object total steps             : 59
% 0.19/0.38  # Proof object clause steps            : 38
% 0.19/0.38  # Proof object formula steps           : 21
% 0.19/0.38  # Proof object conjectures             : 25
% 0.19/0.38  # Proof object clause conjectures      : 22
% 0.19/0.38  # Proof object formula conjectures     : 3
% 0.19/0.38  # Proof object initial clauses used    : 27
% 0.19/0.38  # Proof object initial formulas used   : 10
% 0.19/0.38  # Proof object generating inferences   : 11
% 0.19/0.38  # Proof object simplifying inferences  : 59
% 0.19/0.38  # Training examples: 0 positive, 0 negative
% 0.19/0.38  # Parsed axioms                        : 10
% 0.19/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.38  # Initial clauses                      : 34
% 0.19/0.38  # Removed in clause preprocessing      : 0
% 0.19/0.38  # Initial clauses in saturation        : 34
% 0.19/0.38  # Processed clauses                    : 97
% 0.19/0.38  # ...of these trivial                  : 0
% 0.19/0.38  # ...subsumed                          : 1
% 0.19/0.38  # ...remaining for further processing  : 96
% 0.19/0.38  # Other redundant clauses eliminated   : 0
% 0.19/0.38  # Clauses deleted for lack of memory   : 0
% 0.19/0.38  # Backward-subsumed                    : 1
% 0.19/0.38  # Backward-rewritten                   : 3
% 0.19/0.38  # Generated clauses                    : 47
% 0.19/0.38  # ...of the previous two non-trivial   : 36
% 0.19/0.38  # Contextual simplify-reflections      : 34
% 0.19/0.38  # Paramodulations                      : 47
% 0.19/0.38  # Factorizations                       : 0
% 0.19/0.38  # Equation resolutions                 : 0
% 0.19/0.38  # Propositional unsat checks           : 0
% 0.19/0.38  #    Propositional check models        : 0
% 0.19/0.38  #    Propositional check unsatisfiable : 0
% 0.19/0.38  #    Propositional clauses             : 0
% 0.19/0.38  #    Propositional clauses after purity: 0
% 0.19/0.38  #    Propositional unsat core size     : 0
% 0.19/0.38  #    Propositional preprocessing time  : 0.000
% 0.19/0.38  #    Propositional encoding time       : 0.000
% 0.19/0.38  #    Propositional solver time         : 0.000
% 0.19/0.38  #    Success case prop preproc time    : 0.000
% 0.19/0.38  #    Success case prop encoding time   : 0.000
% 0.19/0.38  #    Success case prop solver time     : 0.000
% 0.19/0.38  # Current number of processed clauses  : 58
% 0.19/0.38  #    Positive orientable unit clauses  : 14
% 0.19/0.38  #    Positive unorientable unit clauses: 0
% 0.19/0.38  #    Negative unit clauses             : 2
% 0.19/0.38  #    Non-unit-clauses                  : 42
% 0.19/0.38  # Current number of unprocessed clauses: 7
% 0.19/0.38  # ...number of literals in the above   : 53
% 0.19/0.38  # Current number of archived formulas  : 0
% 0.19/0.38  # Current number of archived clauses   : 38
% 0.19/0.38  # Clause-clause subsumption calls (NU) : 1815
% 0.19/0.38  # Rec. Clause-clause subsumption calls : 105
% 0.19/0.38  # Non-unit clause-clause subsumptions  : 36
% 0.19/0.38  # Unit Clause-clause subsumption calls : 4
% 0.19/0.38  # Rewrite failures with RHS unbound    : 0
% 0.19/0.38  # BW rewrite match attempts            : 1
% 0.19/0.38  # BW rewrite match successes           : 1
% 0.19/0.38  # Condensation attempts                : 0
% 0.19/0.38  # Condensation successes               : 0
% 0.19/0.38  # Termbank termtop insertions          : 7741
% 0.19/0.38  
% 0.19/0.38  # -------------------------------------------------
% 0.19/0.38  # User time                : 0.039 s
% 0.19/0.38  # System time              : 0.004 s
% 0.19/0.38  # Total time               : 0.043 s
% 0.19/0.38  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------
