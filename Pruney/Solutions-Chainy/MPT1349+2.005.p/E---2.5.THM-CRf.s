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
% DateTime   : Thu Dec  3 11:14:06 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  121 (58413 expanded)
%              Number of clauses        :   96 (18658 expanded)
%              Number of leaves         :   12 (14507 expanded)
%              Depth                    :   24
%              Number of atoms          :  710 (698088 expanded)
%              Number of equality atoms :  106 (160949 expanded)
%              Maximal formula depth    :   23 (   6 average)
%              Maximal clause size      :   67 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t74_tops_2,conjecture,(
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
             => ( v3_tops_2(X3,X1,X2)
              <=> ( k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) = k2_struct_0(X1)
                  & k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) = k2_struct_0(X2)
                  & v2_funct_1(X3)
                  & ! [X4] :
                      ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                     => k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,k2_pre_topc(X1,X4)) = k2_pre_topc(X2,k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_2)).

fof(t62_tops_2,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & l1_struct_0(X2) )
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
             => ( ( k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) = k2_struct_0(X2)
                  & v2_funct_1(X3) )
               => ( k1_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3)) = k2_struct_0(X2)
                  & k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3)) = k2_struct_0(X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_tops_2)).

fof(t63_tops_2,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ! [X2] :
          ( l1_struct_0(X2)
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
             => ( ( k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) = k2_struct_0(X2)
                  & v2_funct_1(X3) )
               => v2_funct_1(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_tops_2)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_tops_2)).

fof(dt_k2_tops_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( v1_funct_1(k2_tops_2(X1,X2,X3))
        & v1_funct_2(k2_tops_2(X1,X2,X3),X2,X1)
        & m1_subset_1(k2_tops_2(X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_2)).

fof(t73_tops_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( v2_pre_topc(X2)
            & l1_pre_topc(X2) )
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
             => ( v3_tops_2(X3,X1,X2)
              <=> ( k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) = k2_struct_0(X1)
                  & k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) = k2_struct_0(X2)
                  & v2_funct_1(X3)
                  & ! [X4] :
                      ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
                     => k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,k2_pre_topc(X2,X4)) = k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_tops_2)).

fof(dt_k2_pre_topc,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(t68_tops_2,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ! [X2] :
          ( l1_struct_0(X2)
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
             => ! [X4] :
                  ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
                 => ( ( k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) = k2_struct_0(X2)
                      & v2_funct_1(X3) )
                   => k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4) = k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3),X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_tops_2)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tops_2)).

fof(t57_tops_2,axiom,(
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
             => ( v5_pre_topc(X3,X1,X2)
              <=> ! [X4] :
                    ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                   => r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,k2_pre_topc(X1,X4)),k2_pre_topc(X2,k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4))) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_tops_2)).

fof(t70_tops_2,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & l1_pre_topc(X2) )
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
             => ( v3_tops_2(X3,X1,X2)
               => v3_tops_2(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3),X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_tops_2)).

fof(c_0_12,negated_conjecture,(
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
               => ( v3_tops_2(X3,X1,X2)
                <=> ( k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) = k2_struct_0(X1)
                    & k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) = k2_struct_0(X2)
                    & v2_funct_1(X3)
                    & ! [X4] :
                        ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                       => k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,k2_pre_topc(X1,X4)) = k2_pre_topc(X2,k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4)) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t74_tops_2])).

fof(c_0_13,plain,(
    ! [X19,X20,X21] :
      ( ( k1_relset_1(u1_struct_0(X20),u1_struct_0(X19),k2_tops_2(u1_struct_0(X19),u1_struct_0(X20),X21)) = k2_struct_0(X20)
        | k2_relset_1(u1_struct_0(X19),u1_struct_0(X20),X21) != k2_struct_0(X20)
        | ~ v2_funct_1(X21)
        | ~ v1_funct_1(X21)
        | ~ v1_funct_2(X21,u1_struct_0(X19),u1_struct_0(X20))
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X19),u1_struct_0(X20))))
        | v2_struct_0(X20)
        | ~ l1_struct_0(X20)
        | ~ l1_struct_0(X19) )
      & ( k2_relset_1(u1_struct_0(X20),u1_struct_0(X19),k2_tops_2(u1_struct_0(X19),u1_struct_0(X20),X21)) = k2_struct_0(X19)
        | k2_relset_1(u1_struct_0(X19),u1_struct_0(X20),X21) != k2_struct_0(X20)
        | ~ v2_funct_1(X21)
        | ~ v1_funct_1(X21)
        | ~ v1_funct_2(X21,u1_struct_0(X19),u1_struct_0(X20))
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X19),u1_struct_0(X20))))
        | v2_struct_0(X20)
        | ~ l1_struct_0(X20)
        | ~ l1_struct_0(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t62_tops_2])])])])])).

fof(c_0_14,negated_conjecture,(
    ! [X45] :
      ( v2_pre_topc(esk3_0)
      & l1_pre_topc(esk3_0)
      & ~ v2_struct_0(esk4_0)
      & v2_pre_topc(esk4_0)
      & l1_pre_topc(esk4_0)
      & v1_funct_1(esk5_0)
      & v1_funct_2(esk5_0,u1_struct_0(esk3_0),u1_struct_0(esk4_0))
      & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0))))
      & ( m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk3_0)))
        | k1_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0) != k2_struct_0(esk3_0)
        | k2_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0) != k2_struct_0(esk4_0)
        | ~ v2_funct_1(esk5_0)
        | ~ v3_tops_2(esk5_0,esk3_0,esk4_0) )
      & ( k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,k2_pre_topc(esk3_0,esk6_0)) != k2_pre_topc(esk4_0,k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,esk6_0))
        | k1_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0) != k2_struct_0(esk3_0)
        | k2_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0) != k2_struct_0(esk4_0)
        | ~ v2_funct_1(esk5_0)
        | ~ v3_tops_2(esk5_0,esk3_0,esk4_0) )
      & ( k1_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0) = k2_struct_0(esk3_0)
        | v3_tops_2(esk5_0,esk3_0,esk4_0) )
      & ( k2_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0) = k2_struct_0(esk4_0)
        | v3_tops_2(esk5_0,esk3_0,esk4_0) )
      & ( v2_funct_1(esk5_0)
        | v3_tops_2(esk5_0,esk3_0,esk4_0) )
      & ( ~ m1_subset_1(X45,k1_zfmisc_1(u1_struct_0(esk3_0)))
        | k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,k2_pre_topc(esk3_0,X45)) = k2_pre_topc(esk4_0,k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,X45))
        | v3_tops_2(esk5_0,esk3_0,esk4_0) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_12])])])])])])).

fof(c_0_15,plain,(
    ! [X22,X23,X24] :
      ( ~ l1_struct_0(X22)
      | ~ l1_struct_0(X23)
      | ~ v1_funct_1(X24)
      | ~ v1_funct_2(X24,u1_struct_0(X22),u1_struct_0(X23))
      | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X22),u1_struct_0(X23))))
      | k2_relset_1(u1_struct_0(X22),u1_struct_0(X23),X24) != k2_struct_0(X23)
      | ~ v2_funct_1(X24)
      | v2_funct_1(k2_tops_2(u1_struct_0(X22),u1_struct_0(X23),X24)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_tops_2])])])).

cnf(c_0_16,plain,
    ( k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),k2_tops_2(u1_struct_0(X2),u1_struct_0(X1),X3)) = k2_struct_0(X1)
    | v2_struct_0(X1)
    | k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),X3) != k2_struct_0(X1)
    | ~ v2_funct_1(X3)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,negated_conjecture,
    ( k2_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0) = k2_struct_0(esk4_0)
    | v3_tops_2(esk5_0,esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( v1_funct_2(esk5_0,u1_struct_0(esk3_0),u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,negated_conjecture,
    ( v2_funct_1(esk5_0)
    | v3_tops_2(esk5_0,esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_23,plain,(
    ! [X7] :
      ( ~ l1_pre_topc(X7)
      | l1_struct_0(X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_24,plain,
    ( v2_funct_1(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) != k2_struct_0(X2)
    | ~ v2_funct_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_25,plain,
    ( k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),k2_tops_2(u1_struct_0(X2),u1_struct_0(X1),X3)) = k2_struct_0(X2)
    | v2_struct_0(X1)
    | k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),X3) != k2_struct_0(X1)
    | ~ v2_funct_1(X3)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_26,plain,(
    ! [X25,X26,X27,X28] :
      ( ~ l1_struct_0(X25)
      | ~ l1_struct_0(X26)
      | ~ v1_funct_1(X27)
      | ~ v1_funct_2(X27,u1_struct_0(X25),u1_struct_0(X26))
      | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X25),u1_struct_0(X26))))
      | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X25)))
      | k2_relset_1(u1_struct_0(X25),u1_struct_0(X26),X27) != k2_struct_0(X26)
      | ~ v2_funct_1(X27)
      | k7_relset_1(u1_struct_0(X25),u1_struct_0(X26),X27,X28) = k8_relset_1(u1_struct_0(X26),u1_struct_0(X25),k2_tops_2(u1_struct_0(X25),u1_struct_0(X26),X27),X28) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t67_tops_2])])])).

cnf(c_0_27,negated_conjecture,
    ( k1_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0)) = k2_struct_0(esk4_0)
    | v3_tops_2(esk5_0,esk3_0,esk4_0)
    | ~ l1_struct_0(esk3_0)
    | ~ l1_struct_0(esk4_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18]),c_0_19]),c_0_20])]),c_0_21]),c_0_22])).

cnf(c_0_28,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_30,plain,(
    ! [X11,X12,X13] :
      ( ( v1_funct_1(k2_tops_2(X11,X12,X13))
        | ~ v1_funct_1(X13)
        | ~ v1_funct_2(X13,X11,X12)
        | ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X11,X12))) )
      & ( v1_funct_2(k2_tops_2(X11,X12,X13),X12,X11)
        | ~ v1_funct_1(X13)
        | ~ v1_funct_2(X13,X11,X12)
        | ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X11,X12))) )
      & ( m1_subset_1(k2_tops_2(X11,X12,X13),k1_zfmisc_1(k2_zfmisc_1(X12,X11)))
        | ~ v1_funct_1(X13)
        | ~ v1_funct_2(X13,X11,X12)
        | ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X11,X12))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_tops_2])])])).

cnf(c_0_31,negated_conjecture,
    ( v2_funct_1(k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0))
    | v3_tops_2(esk5_0,esk3_0,esk4_0)
    | ~ l1_struct_0(esk4_0)
    | ~ l1_struct_0(esk3_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_17]),c_0_18]),c_0_19]),c_0_20])]),c_0_22])).

cnf(c_0_32,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_33,negated_conjecture,
    ( k2_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0)) = k2_struct_0(esk3_0)
    | v3_tops_2(esk5_0,esk3_0,esk4_0)
    | ~ l1_struct_0(esk3_0)
    | ~ l1_struct_0(esk4_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_17]),c_0_18]),c_0_19]),c_0_20])]),c_0_21]),c_0_22])).

cnf(c_0_34,plain,
    ( k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4) = k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3),X4)
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) != k2_struct_0(X2)
    | ~ v2_funct_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_35,plain,(
    ! [X36,X37,X38,X39] :
      ( ( k1_relset_1(u1_struct_0(X36),u1_struct_0(X37),X38) = k2_struct_0(X36)
        | ~ v3_tops_2(X38,X36,X37)
        | ~ v1_funct_1(X38)
        | ~ v1_funct_2(X38,u1_struct_0(X36),u1_struct_0(X37))
        | ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X36),u1_struct_0(X37))))
        | ~ v2_pre_topc(X37)
        | ~ l1_pre_topc(X37)
        | v2_struct_0(X36)
        | ~ v2_pre_topc(X36)
        | ~ l1_pre_topc(X36) )
      & ( k2_relset_1(u1_struct_0(X36),u1_struct_0(X37),X38) = k2_struct_0(X37)
        | ~ v3_tops_2(X38,X36,X37)
        | ~ v1_funct_1(X38)
        | ~ v1_funct_2(X38,u1_struct_0(X36),u1_struct_0(X37))
        | ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X36),u1_struct_0(X37))))
        | ~ v2_pre_topc(X37)
        | ~ l1_pre_topc(X37)
        | v2_struct_0(X36)
        | ~ v2_pre_topc(X36)
        | ~ l1_pre_topc(X36) )
      & ( v2_funct_1(X38)
        | ~ v3_tops_2(X38,X36,X37)
        | ~ v1_funct_1(X38)
        | ~ v1_funct_2(X38,u1_struct_0(X36),u1_struct_0(X37))
        | ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X36),u1_struct_0(X37))))
        | ~ v2_pre_topc(X37)
        | ~ l1_pre_topc(X37)
        | v2_struct_0(X36)
        | ~ v2_pre_topc(X36)
        | ~ l1_pre_topc(X36) )
      & ( ~ m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(X37)))
        | k8_relset_1(u1_struct_0(X36),u1_struct_0(X37),X38,k2_pre_topc(X37,X39)) = k2_pre_topc(X36,k8_relset_1(u1_struct_0(X36),u1_struct_0(X37),X38,X39))
        | ~ v3_tops_2(X38,X36,X37)
        | ~ v1_funct_1(X38)
        | ~ v1_funct_2(X38,u1_struct_0(X36),u1_struct_0(X37))
        | ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X36),u1_struct_0(X37))))
        | ~ v2_pre_topc(X37)
        | ~ l1_pre_topc(X37)
        | v2_struct_0(X36)
        | ~ v2_pre_topc(X36)
        | ~ l1_pre_topc(X36) )
      & ( m1_subset_1(esk2_3(X36,X37,X38),k1_zfmisc_1(u1_struct_0(X37)))
        | k1_relset_1(u1_struct_0(X36),u1_struct_0(X37),X38) != k2_struct_0(X36)
        | k2_relset_1(u1_struct_0(X36),u1_struct_0(X37),X38) != k2_struct_0(X37)
        | ~ v2_funct_1(X38)
        | v3_tops_2(X38,X36,X37)
        | ~ v1_funct_1(X38)
        | ~ v1_funct_2(X38,u1_struct_0(X36),u1_struct_0(X37))
        | ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X36),u1_struct_0(X37))))
        | ~ v2_pre_topc(X37)
        | ~ l1_pre_topc(X37)
        | v2_struct_0(X36)
        | ~ v2_pre_topc(X36)
        | ~ l1_pre_topc(X36) )
      & ( k8_relset_1(u1_struct_0(X36),u1_struct_0(X37),X38,k2_pre_topc(X37,esk2_3(X36,X37,X38))) != k2_pre_topc(X36,k8_relset_1(u1_struct_0(X36),u1_struct_0(X37),X38,esk2_3(X36,X37,X38)))
        | k1_relset_1(u1_struct_0(X36),u1_struct_0(X37),X38) != k2_struct_0(X36)
        | k2_relset_1(u1_struct_0(X36),u1_struct_0(X37),X38) != k2_struct_0(X37)
        | ~ v2_funct_1(X38)
        | v3_tops_2(X38,X36,X37)
        | ~ v1_funct_1(X38)
        | ~ v1_funct_2(X38,u1_struct_0(X36),u1_struct_0(X37))
        | ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X36),u1_struct_0(X37))))
        | ~ v2_pre_topc(X37)
        | ~ l1_pre_topc(X37)
        | v2_struct_0(X36)
        | ~ v2_pre_topc(X36)
        | ~ l1_pre_topc(X36) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t73_tops_2])])])])])])).

cnf(c_0_36,negated_conjecture,
    ( k1_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0)) = k2_struct_0(esk4_0)
    | v3_tops_2(esk5_0,esk3_0,esk4_0)
    | ~ l1_struct_0(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29])])).

cnf(c_0_37,plain,
    ( v1_funct_2(k2_tops_2(X1,X2,X3),X2,X1)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_38,plain,
    ( v1_funct_1(k2_tops_2(X1,X2,X3))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_39,plain,
    ( m1_subset_1(k2_tops_2(X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_40,negated_conjecture,
    ( v2_funct_1(k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0))
    | v3_tops_2(esk5_0,esk3_0,esk4_0)
    | ~ l1_struct_0(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_28]),c_0_32])])).

cnf(c_0_41,negated_conjecture,
    ( k2_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0)) = k2_struct_0(esk3_0)
    | v3_tops_2(esk5_0,esk3_0,esk4_0)
    | ~ l1_struct_0(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_28]),c_0_29])])).

cnf(c_0_42,negated_conjecture,
    ( k8_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),X1) = k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,X1)
    | v3_tops_2(esk5_0,esk3_0,esk4_0)
    | ~ l1_struct_0(esk4_0)
    | ~ l1_struct_0(esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_17]),c_0_18]),c_0_19]),c_0_20])]),c_0_22])).

fof(c_0_43,plain,(
    ! [X5,X6] :
      ( ~ l1_pre_topc(X5)
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5)))
      | m1_subset_1(k2_pre_topc(X5,X6),k1_zfmisc_1(u1_struct_0(X5))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).

cnf(c_0_44,plain,
    ( m1_subset_1(esk2_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X2)))
    | v3_tops_2(X3,X1,X2)
    | v2_struct_0(X1)
    | k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) != k2_struct_0(X1)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) != k2_struct_0(X2)
    | ~ v2_funct_1(X3)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_45,negated_conjecture,
    ( k1_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0)) = k2_struct_0(esk4_0)
    | v3_tops_2(esk5_0,esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_28]),c_0_32])])).

cnf(c_0_46,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_47,negated_conjecture,
    ( v2_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_48,negated_conjecture,
    ( v1_funct_2(k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),u1_struct_0(esk4_0),u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_18]),c_0_19]),c_0_20])])).

cnf(c_0_49,negated_conjecture,
    ( v1_funct_1(k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_18]),c_0_19]),c_0_20])])).

cnf(c_0_50,negated_conjecture,
    ( m1_subset_1(k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_18]),c_0_19]),c_0_20])])).

cnf(c_0_51,negated_conjecture,
    ( v2_funct_1(k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0))
    | v3_tops_2(esk5_0,esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_28]),c_0_29])])).

cnf(c_0_52,negated_conjecture,
    ( k2_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0)) = k2_struct_0(esk3_0)
    | v3_tops_2(esk5_0,esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_28]),c_0_32])])).

cnf(c_0_53,negated_conjecture,
    ( k8_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),X1) = k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,X1)
    | v3_tops_2(esk5_0,esk3_0,esk4_0)
    | ~ l1_struct_0(esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_28]),c_0_32])])).

cnf(c_0_54,plain,
    ( m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_55,negated_conjecture,
    ( v3_tops_2(k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),esk4_0,esk3_0)
    | v3_tops_2(esk5_0,esk3_0,esk4_0)
    | m1_subset_1(esk2_3(esk4_0,esk3_0,k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0)),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_46]),c_0_47]),c_0_48]),c_0_49]),c_0_50]),c_0_29]),c_0_32])]),c_0_21]),c_0_51]),c_0_52])).

cnf(c_0_56,negated_conjecture,
    ( k8_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),X1) = k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,X1)
    | v3_tops_2(esk5_0,esk3_0,esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_28]),c_0_29])])).

cnf(c_0_57,negated_conjecture,
    ( v3_tops_2(k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),esk4_0,esk3_0)
    | v3_tops_2(esk5_0,esk3_0,esk4_0)
    | m1_subset_1(k2_pre_topc(esk3_0,esk2_3(esk4_0,esk3_0,k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0))),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_29])])).

fof(c_0_58,plain,(
    ! [X29,X30,X31,X32] :
      ( ~ l1_struct_0(X29)
      | ~ l1_struct_0(X30)
      | ~ v1_funct_1(X31)
      | ~ v1_funct_2(X31,u1_struct_0(X29),u1_struct_0(X30))
      | ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X29),u1_struct_0(X30))))
      | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X30)))
      | k2_relset_1(u1_struct_0(X29),u1_struct_0(X30),X31) != k2_struct_0(X30)
      | ~ v2_funct_1(X31)
      | k8_relset_1(u1_struct_0(X29),u1_struct_0(X30),X31,X32) = k7_relset_1(u1_struct_0(X30),u1_struct_0(X29),k2_tops_2(u1_struct_0(X29),u1_struct_0(X30),X31),X32) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t68_tops_2])])])).

cnf(c_0_59,plain,
    ( v3_tops_2(X3,X1,X2)
    | v2_struct_0(X1)
    | k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,k2_pre_topc(X2,esk2_3(X1,X2,X3))) != k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,esk2_3(X1,X2,X3)))
    | k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) != k2_struct_0(X1)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) != k2_struct_0(X2)
    | ~ v2_funct_1(X3)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_60,negated_conjecture,
    ( k8_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),k2_pre_topc(esk3_0,esk2_3(esk4_0,esk3_0,k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0)))) = k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,k2_pre_topc(esk3_0,esk2_3(esk4_0,esk3_0,k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0))))
    | v3_tops_2(k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),esk4_0,esk3_0)
    | v3_tops_2(esk5_0,esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_61,negated_conjecture,
    ( k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,k2_pre_topc(esk3_0,X1)) = k2_pre_topc(esk4_0,k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,X1))
    | v3_tops_2(esk5_0,esk3_0,esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_62,plain,
    ( k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4) = k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3),X4)
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) != k2_struct_0(X2)
    | ~ v2_funct_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

fof(c_0_63,plain,(
    ! [X8,X9,X10] :
      ( ( k1_relset_1(u1_struct_0(X8),u1_struct_0(X9),X10) = k2_struct_0(X8)
        | ~ v3_tops_2(X10,X8,X9)
        | ~ v1_funct_1(X10)
        | ~ v1_funct_2(X10,u1_struct_0(X8),u1_struct_0(X9))
        | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X8),u1_struct_0(X9))))
        | ~ l1_pre_topc(X9)
        | ~ l1_pre_topc(X8) )
      & ( k2_relset_1(u1_struct_0(X8),u1_struct_0(X9),X10) = k2_struct_0(X9)
        | ~ v3_tops_2(X10,X8,X9)
        | ~ v1_funct_1(X10)
        | ~ v1_funct_2(X10,u1_struct_0(X8),u1_struct_0(X9))
        | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X8),u1_struct_0(X9))))
        | ~ l1_pre_topc(X9)
        | ~ l1_pre_topc(X8) )
      & ( v2_funct_1(X10)
        | ~ v3_tops_2(X10,X8,X9)
        | ~ v1_funct_1(X10)
        | ~ v1_funct_2(X10,u1_struct_0(X8),u1_struct_0(X9))
        | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X8),u1_struct_0(X9))))
        | ~ l1_pre_topc(X9)
        | ~ l1_pre_topc(X8) )
      & ( v5_pre_topc(X10,X8,X9)
        | ~ v3_tops_2(X10,X8,X9)
        | ~ v1_funct_1(X10)
        | ~ v1_funct_2(X10,u1_struct_0(X8),u1_struct_0(X9))
        | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X8),u1_struct_0(X9))))
        | ~ l1_pre_topc(X9)
        | ~ l1_pre_topc(X8) )
      & ( v5_pre_topc(k2_tops_2(u1_struct_0(X8),u1_struct_0(X9),X10),X9,X8)
        | ~ v3_tops_2(X10,X8,X9)
        | ~ v1_funct_1(X10)
        | ~ v1_funct_2(X10,u1_struct_0(X8),u1_struct_0(X9))
        | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X8),u1_struct_0(X9))))
        | ~ l1_pre_topc(X9)
        | ~ l1_pre_topc(X8) )
      & ( k1_relset_1(u1_struct_0(X8),u1_struct_0(X9),X10) != k2_struct_0(X8)
        | k2_relset_1(u1_struct_0(X8),u1_struct_0(X9),X10) != k2_struct_0(X9)
        | ~ v2_funct_1(X10)
        | ~ v5_pre_topc(X10,X8,X9)
        | ~ v5_pre_topc(k2_tops_2(u1_struct_0(X8),u1_struct_0(X9),X10),X9,X8)
        | v3_tops_2(X10,X8,X9)
        | ~ v1_funct_1(X10)
        | ~ v1_funct_2(X10,u1_struct_0(X8),u1_struct_0(X9))
        | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X8),u1_struct_0(X9))))
        | ~ l1_pre_topc(X9)
        | ~ l1_pre_topc(X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_tops_2])])])])).

cnf(c_0_64,negated_conjecture,
    ( v3_tops_2(k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),esk4_0,esk3_0)
    | v3_tops_2(esk5_0,esk3_0,esk4_0)
    | k2_pre_topc(esk4_0,k8_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),esk2_3(esk4_0,esk3_0,k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0)))) != k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,k2_pre_topc(esk3_0,esk2_3(esk4_0,esk3_0,k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0)))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_46]),c_0_47]),c_0_48]),c_0_49]),c_0_50]),c_0_29]),c_0_32])]),c_0_21]),c_0_51]),c_0_52]),c_0_45])).

cnf(c_0_65,negated_conjecture,
    ( k8_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),esk2_3(esk4_0,esk3_0,k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0))) = k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,esk2_3(esk4_0,esk3_0,k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0)))
    | v3_tops_2(k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),esk4_0,esk3_0)
    | v3_tops_2(esk5_0,esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_55])).

cnf(c_0_66,negated_conjecture,
    ( k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,k2_pre_topc(esk3_0,esk2_3(esk4_0,esk3_0,k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0)))) = k2_pre_topc(esk4_0,k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,esk2_3(esk4_0,esk3_0,k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0))))
    | v3_tops_2(k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),esk4_0,esk3_0)
    | v3_tops_2(esk5_0,esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_61,c_0_55])).

cnf(c_0_67,negated_conjecture,
    ( k8_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),X1) = k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0)),X1)
    | v3_tops_2(esk5_0,esk3_0,esk4_0)
    | ~ l1_struct_0(esk3_0)
    | ~ l1_struct_0(esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_52]),c_0_48]),c_0_49]),c_0_50])]),c_0_51])).

fof(c_0_68,plain,(
    ! [X14,X15,X16,X17] :
      ( ( ~ v5_pre_topc(X16,X14,X15)
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X14)))
        | r1_tarski(k7_relset_1(u1_struct_0(X14),u1_struct_0(X15),X16,k2_pre_topc(X14,X17)),k2_pre_topc(X15,k7_relset_1(u1_struct_0(X14),u1_struct_0(X15),X16,X17)))
        | ~ v1_funct_1(X16)
        | ~ v1_funct_2(X16,u1_struct_0(X14),u1_struct_0(X15))
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X14),u1_struct_0(X15))))
        | v2_struct_0(X15)
        | ~ v2_pre_topc(X15)
        | ~ l1_pre_topc(X15)
        | ~ v2_pre_topc(X14)
        | ~ l1_pre_topc(X14) )
      & ( m1_subset_1(esk1_3(X14,X15,X16),k1_zfmisc_1(u1_struct_0(X14)))
        | v5_pre_topc(X16,X14,X15)
        | ~ v1_funct_1(X16)
        | ~ v1_funct_2(X16,u1_struct_0(X14),u1_struct_0(X15))
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X14),u1_struct_0(X15))))
        | v2_struct_0(X15)
        | ~ v2_pre_topc(X15)
        | ~ l1_pre_topc(X15)
        | ~ v2_pre_topc(X14)
        | ~ l1_pre_topc(X14) )
      & ( ~ r1_tarski(k7_relset_1(u1_struct_0(X14),u1_struct_0(X15),X16,k2_pre_topc(X14,esk1_3(X14,X15,X16))),k2_pre_topc(X15,k7_relset_1(u1_struct_0(X14),u1_struct_0(X15),X16,esk1_3(X14,X15,X16))))
        | v5_pre_topc(X16,X14,X15)
        | ~ v1_funct_1(X16)
        | ~ v1_funct_2(X16,u1_struct_0(X14),u1_struct_0(X15))
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X14),u1_struct_0(X15))))
        | v2_struct_0(X15)
        | ~ v2_pre_topc(X15)
        | ~ l1_pre_topc(X15)
        | ~ v2_pre_topc(X14)
        | ~ l1_pre_topc(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t57_tops_2])])])])])])).

cnf(c_0_69,plain,
    ( v5_pre_topc(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3),X2,X1)
    | ~ v3_tops_2(X3,X1,X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_70,negated_conjecture,
    ( v3_tops_2(k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),esk4_0,esk3_0)
    | v3_tops_2(esk5_0,esk3_0,esk4_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_66])).

cnf(c_0_71,negated_conjecture,
    ( v1_funct_1(k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0)))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_48]),c_0_49])])).

cnf(c_0_72,negated_conjecture,
    ( k8_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),X1) = k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0)),X1)
    | v3_tops_2(esk5_0,esk3_0,esk4_0)
    | ~ l1_struct_0(esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_28]),c_0_29])])).

cnf(c_0_73,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | v5_pre_topc(X3,X1,X2)
    | v2_struct_0(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_74,plain,
    ( r1_tarski(k7_relset_1(u1_struct_0(X2),u1_struct_0(X3),X1,k2_pre_topc(X2,X4)),k2_pre_topc(X3,k7_relset_1(u1_struct_0(X2),u1_struct_0(X3),X1,X4)))
    | v2_struct_0(X3)
    | ~ v5_pre_topc(X1,X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_75,negated_conjecture,
    ( v5_pre_topc(k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0)),esk3_0,esk4_0)
    | v3_tops_2(esk5_0,esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_48]),c_0_49]),c_0_50]),c_0_29]),c_0_32])])).

cnf(c_0_76,negated_conjecture,
    ( v1_funct_2(k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0)),u1_struct_0(esk3_0),u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_48]),c_0_49])]),c_0_50])])).

cnf(c_0_77,negated_conjecture,
    ( v1_funct_1(k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_71,c_0_50])])).

cnf(c_0_78,negated_conjecture,
    ( m1_subset_1(k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_48]),c_0_49])]),c_0_50])])).

cnf(c_0_79,negated_conjecture,
    ( k8_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),X1) = k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0)),X1)
    | v3_tops_2(esk5_0,esk3_0,esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_28]),c_0_32])])).

cnf(c_0_80,negated_conjecture,
    ( v5_pre_topc(esk5_0,esk3_0,esk4_0)
    | m1_subset_1(esk1_3(esk3_0,esk4_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_18]),c_0_47]),c_0_46]),c_0_19]),c_0_20]),c_0_32]),c_0_29])]),c_0_21])).

cnf(c_0_81,negated_conjecture,
    ( r1_tarski(k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0)),k2_pre_topc(esk3_0,X1)),k2_pre_topc(esk4_0,k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0)),X1)))
    | v3_tops_2(esk5_0,esk3_0,esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_47]),c_0_46]),c_0_76]),c_0_77]),c_0_78]),c_0_32]),c_0_29])]),c_0_21])).

cnf(c_0_82,negated_conjecture,
    ( k8_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),esk1_3(esk3_0,esk4_0,esk5_0)) = k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0)),esk1_3(esk3_0,esk4_0,esk5_0))
    | v5_pre_topc(esk5_0,esk3_0,esk4_0)
    | v3_tops_2(esk5_0,esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_79,c_0_80])).

cnf(c_0_83,negated_conjecture,
    ( k8_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),esk1_3(esk3_0,esk4_0,esk5_0)) = k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,esk1_3(esk3_0,esk4_0,esk5_0))
    | v5_pre_topc(esk5_0,esk3_0,esk4_0)
    | v3_tops_2(esk5_0,esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_80])).

cnf(c_0_84,negated_conjecture,
    ( v5_pre_topc(esk5_0,esk3_0,esk4_0)
    | m1_subset_1(k2_pre_topc(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0)),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_80]),c_0_29])])).

cnf(c_0_85,negated_conjecture,
    ( r1_tarski(k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0)),k2_pre_topc(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0))),k2_pre_topc(esk4_0,k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0)),esk1_3(esk3_0,esk4_0,esk5_0))))
    | v5_pre_topc(esk5_0,esk3_0,esk4_0)
    | v3_tops_2(esk5_0,esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_81,c_0_80])).

cnf(c_0_86,negated_conjecture,
    ( k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0)),esk1_3(esk3_0,esk4_0,esk5_0)) = k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,esk1_3(esk3_0,esk4_0,esk5_0))
    | v5_pre_topc(esk5_0,esk3_0,esk4_0)
    | v3_tops_2(esk5_0,esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_82,c_0_83])).

cnf(c_0_87,negated_conjecture,
    ( k8_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),k2_pre_topc(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0))) = k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,k2_pre_topc(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0)))
    | v5_pre_topc(esk5_0,esk3_0,esk4_0)
    | v3_tops_2(esk5_0,esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_84])).

cnf(c_0_88,negated_conjecture,
    ( k8_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),k2_pre_topc(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0))) = k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0)),k2_pre_topc(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0)))
    | v5_pre_topc(esk5_0,esk3_0,esk4_0)
    | v3_tops_2(esk5_0,esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_79,c_0_84])).

cnf(c_0_89,negated_conjecture,
    ( r1_tarski(k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0)),k2_pre_topc(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0))),k2_pre_topc(esk4_0,k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,esk1_3(esk3_0,esk4_0,esk5_0))))
    | v5_pre_topc(esk5_0,esk3_0,esk4_0)
    | v3_tops_2(esk5_0,esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_85,c_0_86])).

cnf(c_0_90,negated_conjecture,
    ( k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0)),k2_pre_topc(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0))) = k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,k2_pre_topc(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0)))
    | v5_pre_topc(esk5_0,esk3_0,esk4_0)
    | v3_tops_2(esk5_0,esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_87,c_0_88])).

cnf(c_0_91,plain,
    ( v5_pre_topc(X3,X1,X2)
    | v2_struct_0(X2)
    | ~ r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,k2_pre_topc(X1,esk1_3(X1,X2,X3))),k2_pre_topc(X2,k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,esk1_3(X1,X2,X3))))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_92,negated_conjecture,
    ( r1_tarski(k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,k2_pre_topc(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0))),k2_pre_topc(esk4_0,k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,esk1_3(esk3_0,esk4_0,esk5_0))))
    | v5_pre_topc(esk5_0,esk3_0,esk4_0)
    | v3_tops_2(esk5_0,esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_89,c_0_90])).

cnf(c_0_93,plain,
    ( v5_pre_topc(X1,X2,X3)
    | ~ v3_tops_2(X1,X2,X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_94,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_95,negated_conjecture,
    ( v5_pre_topc(esk5_0,esk3_0,esk4_0)
    | v3_tops_2(esk5_0,esk3_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_92]),c_0_47]),c_0_46]),c_0_18]),c_0_19]),c_0_20]),c_0_32]),c_0_29])]),c_0_21])).

cnf(c_0_96,negated_conjecture,
    ( v5_pre_topc(k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),esk4_0,esk3_0)
    | v3_tops_2(esk5_0,esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_70]),c_0_48]),c_0_49]),c_0_50]),c_0_29]),c_0_32])])).

cnf(c_0_97,negated_conjecture,
    ( k1_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0) = k2_struct_0(esk3_0)
    | v3_tops_2(esk5_0,esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_98,plain,
    ( k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) = k2_struct_0(X2)
    | ~ v3_tops_2(X3,X1,X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_99,negated_conjecture,
    ( v3_tops_2(esk5_0,esk3_0,esk4_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_95]),c_0_18]),c_0_19]),c_0_20]),c_0_32]),c_0_29])]),c_0_22]),c_0_96]),c_0_17]),c_0_97])).

cnf(c_0_100,plain,
    ( v2_funct_1(X1)
    | ~ v3_tops_2(X1,X2,X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_101,negated_conjecture,
    ( k2_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0) = k2_struct_0(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_99]),c_0_18]),c_0_19]),c_0_20]),c_0_32]),c_0_29])])).

cnf(c_0_102,negated_conjecture,
    ( v2_funct_1(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_99]),c_0_18]),c_0_19]),c_0_20]),c_0_32]),c_0_29])])).

cnf(c_0_103,plain,
    ( k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) = k2_struct_0(X1)
    | ~ v3_tops_2(X3,X1,X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

fof(c_0_104,plain,(
    ! [X33,X34,X35] :
      ( ~ l1_pre_topc(X33)
      | v2_struct_0(X34)
      | ~ l1_pre_topc(X34)
      | ~ v1_funct_1(X35)
      | ~ v1_funct_2(X35,u1_struct_0(X33),u1_struct_0(X34))
      | ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X33),u1_struct_0(X34))))
      | ~ v3_tops_2(X35,X33,X34)
      | v3_tops_2(k2_tops_2(u1_struct_0(X33),u1_struct_0(X34),X35),X34,X33) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t70_tops_2])])])])).

cnf(c_0_105,negated_conjecture,
    ( k8_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),X1) = k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,X1)
    | ~ l1_struct_0(esk4_0)
    | ~ l1_struct_0(esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_101]),c_0_102]),c_0_18]),c_0_19]),c_0_20])])).

cnf(c_0_106,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | k1_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0) != k2_struct_0(esk3_0)
    | k2_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0) != k2_struct_0(esk4_0)
    | ~ v2_funct_1(esk5_0)
    | ~ v3_tops_2(esk5_0,esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_107,negated_conjecture,
    ( k1_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0) = k2_struct_0(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_99]),c_0_18]),c_0_19]),c_0_20]),c_0_32]),c_0_29])])).

cnf(c_0_108,plain,
    ( v2_struct_0(X2)
    | v3_tops_2(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3),X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v3_tops_2(X3,X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_104])).

cnf(c_0_109,negated_conjecture,
    ( k8_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),X1) = k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,X1)
    | ~ l1_struct_0(esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_28]),c_0_32])])).

cnf(c_0_110,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_106,c_0_99])]),c_0_107]),c_0_101]),c_0_102])])).

cnf(c_0_111,plain,
    ( k8_relset_1(u1_struct_0(X3),u1_struct_0(X2),X4,k2_pre_topc(X2,X1)) = k2_pre_topc(X3,k8_relset_1(u1_struct_0(X3),u1_struct_0(X2),X4,X1))
    | v2_struct_0(X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v3_tops_2(X4,X3,X2)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X2))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_112,negated_conjecture,
    ( v3_tops_2(k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),esk4_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_99]),c_0_18]),c_0_19]),c_0_20]),c_0_32]),c_0_29])]),c_0_21])).

cnf(c_0_113,negated_conjecture,
    ( k8_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),X1) = k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_28]),c_0_29])])).

cnf(c_0_114,negated_conjecture,
    ( m1_subset_1(k2_pre_topc(esk3_0,esk6_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_110]),c_0_29])])).

cnf(c_0_115,negated_conjecture,
    ( k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,k2_pre_topc(esk3_0,esk6_0)) != k2_pre_topc(esk4_0,k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,esk6_0))
    | k1_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0) != k2_struct_0(esk3_0)
    | k2_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0) != k2_struct_0(esk4_0)
    | ~ v2_funct_1(esk5_0)
    | ~ v3_tops_2(esk5_0,esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_116,negated_conjecture,
    ( k8_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),k2_pre_topc(esk3_0,X1)) = k2_pre_topc(esk4_0,k8_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111,c_0_112]),c_0_47]),c_0_46]),c_0_48]),c_0_49]),c_0_50]),c_0_32]),c_0_29])]),c_0_21])).

cnf(c_0_117,negated_conjecture,
    ( k8_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),k2_pre_topc(esk3_0,esk6_0)) = k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,k2_pre_topc(esk3_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_113,c_0_114])).

cnf(c_0_118,negated_conjecture,
    ( k8_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),esk6_0) = k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_113,c_0_110])).

cnf(c_0_119,negated_conjecture,
    ( k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,k2_pre_topc(esk3_0,esk6_0)) != k2_pre_topc(esk4_0,k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_115,c_0_99])]),c_0_107]),c_0_101]),c_0_102])])).

cnf(c_0_120,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116,c_0_110]),c_0_117]),c_0_118]),c_0_119]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:07:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.21/0.53  # AutoSched0-Mode selected heuristic G_E___208_B07_F1_SE_CS_SP_PS_S4d
% 0.21/0.53  # and selection function SelectCQIPrecWNTNp.
% 0.21/0.53  #
% 0.21/0.53  # Preprocessing time       : 0.032 s
% 0.21/0.53  # Presaturation interreduction done
% 0.21/0.53  
% 0.21/0.53  # Proof found!
% 0.21/0.53  # SZS status Theorem
% 0.21/0.53  # SZS output start CNFRefutation
% 0.21/0.53  fof(t74_tops_2, conjecture, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>(v3_tops_2(X3,X1,X2)<=>(((k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)=k2_struct_0(X1)&k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)=k2_struct_0(X2))&v2_funct_1(X3))&![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,k2_pre_topc(X1,X4))=k2_pre_topc(X2,k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_tops_2)).
% 0.21/0.53  fof(t62_tops_2, axiom, ![X1]:(l1_struct_0(X1)=>![X2]:((~(v2_struct_0(X2))&l1_struct_0(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>((k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)=k2_struct_0(X2)&v2_funct_1(X3))=>(k1_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3))=k2_struct_0(X2)&k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3))=k2_struct_0(X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_tops_2)).
% 0.21/0.53  fof(t63_tops_2, axiom, ![X1]:(l1_struct_0(X1)=>![X2]:(l1_struct_0(X2)=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>((k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)=k2_struct_0(X2)&v2_funct_1(X3))=>v2_funct_1(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_tops_2)).
% 0.21/0.53  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.21/0.53  fof(t67_tops_2, axiom, ![X1]:(l1_struct_0(X1)=>![X2]:(l1_struct_0(X2)=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>((k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)=k2_struct_0(X2)&v2_funct_1(X3))=>k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4)=k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3),X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_tops_2)).
% 0.21/0.53  fof(dt_k2_tops_2, axiom, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((v1_funct_1(k2_tops_2(X1,X2,X3))&v1_funct_2(k2_tops_2(X1,X2,X3),X2,X1))&m1_subset_1(k2_tops_2(X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tops_2)).
% 0.21/0.53  fof(t73_tops_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((v2_pre_topc(X2)&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>(v3_tops_2(X3,X1,X2)<=>(((k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)=k2_struct_0(X1)&k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)=k2_struct_0(X2))&v2_funct_1(X3))&![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))=>k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,k2_pre_topc(X2,X4))=k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_tops_2)).
% 0.21/0.53  fof(dt_k2_pre_topc, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 0.21/0.53  fof(t68_tops_2, axiom, ![X1]:(l1_struct_0(X1)=>![X2]:(l1_struct_0(X2)=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))=>((k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)=k2_struct_0(X2)&v2_funct_1(X3))=>k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4)=k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3),X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t68_tops_2)).
% 0.21/0.53  fof(d5_tops_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(l1_pre_topc(X2)=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>(v3_tops_2(X3,X1,X2)<=>((((k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)=k2_struct_0(X1)&k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)=k2_struct_0(X2))&v2_funct_1(X3))&v5_pre_topc(X3,X1,X2))&v5_pre_topc(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3),X2,X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tops_2)).
% 0.21/0.53  fof(t57_tops_2, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>(v5_pre_topc(X3,X1,X2)<=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,k2_pre_topc(X1,X4)),k2_pre_topc(X2,k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_tops_2)).
% 0.21/0.53  fof(t70_tops_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:((~(v2_struct_0(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>(v3_tops_2(X3,X1,X2)=>v3_tops_2(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3),X2,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_tops_2)).
% 0.21/0.53  fof(c_0_12, negated_conjecture, ~(![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>(v3_tops_2(X3,X1,X2)<=>(((k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)=k2_struct_0(X1)&k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)=k2_struct_0(X2))&v2_funct_1(X3))&![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,k2_pre_topc(X1,X4))=k2_pre_topc(X2,k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4))))))))), inference(assume_negation,[status(cth)],[t74_tops_2])).
% 0.21/0.53  fof(c_0_13, plain, ![X19, X20, X21]:((k1_relset_1(u1_struct_0(X20),u1_struct_0(X19),k2_tops_2(u1_struct_0(X19),u1_struct_0(X20),X21))=k2_struct_0(X20)|(k2_relset_1(u1_struct_0(X19),u1_struct_0(X20),X21)!=k2_struct_0(X20)|~v2_funct_1(X21))|(~v1_funct_1(X21)|~v1_funct_2(X21,u1_struct_0(X19),u1_struct_0(X20))|~m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X19),u1_struct_0(X20)))))|(v2_struct_0(X20)|~l1_struct_0(X20))|~l1_struct_0(X19))&(k2_relset_1(u1_struct_0(X20),u1_struct_0(X19),k2_tops_2(u1_struct_0(X19),u1_struct_0(X20),X21))=k2_struct_0(X19)|(k2_relset_1(u1_struct_0(X19),u1_struct_0(X20),X21)!=k2_struct_0(X20)|~v2_funct_1(X21))|(~v1_funct_1(X21)|~v1_funct_2(X21,u1_struct_0(X19),u1_struct_0(X20))|~m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X19),u1_struct_0(X20)))))|(v2_struct_0(X20)|~l1_struct_0(X20))|~l1_struct_0(X19))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t62_tops_2])])])])])).
% 0.21/0.53  fof(c_0_14, negated_conjecture, ![X45]:((v2_pre_topc(esk3_0)&l1_pre_topc(esk3_0))&(((~v2_struct_0(esk4_0)&v2_pre_topc(esk4_0))&l1_pre_topc(esk4_0))&(((v1_funct_1(esk5_0)&v1_funct_2(esk5_0,u1_struct_0(esk3_0),u1_struct_0(esk4_0)))&m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0)))))&(((m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk3_0)))|(k1_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0)!=k2_struct_0(esk3_0)|k2_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0)!=k2_struct_0(esk4_0)|~v2_funct_1(esk5_0))|~v3_tops_2(esk5_0,esk3_0,esk4_0))&(k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,k2_pre_topc(esk3_0,esk6_0))!=k2_pre_topc(esk4_0,k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,esk6_0))|(k1_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0)!=k2_struct_0(esk3_0)|k2_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0)!=k2_struct_0(esk4_0)|~v2_funct_1(esk5_0))|~v3_tops_2(esk5_0,esk3_0,esk4_0)))&((((k1_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0)=k2_struct_0(esk3_0)|v3_tops_2(esk5_0,esk3_0,esk4_0))&(k2_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0)=k2_struct_0(esk4_0)|v3_tops_2(esk5_0,esk3_0,esk4_0)))&(v2_funct_1(esk5_0)|v3_tops_2(esk5_0,esk3_0,esk4_0)))&(~m1_subset_1(X45,k1_zfmisc_1(u1_struct_0(esk3_0)))|k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,k2_pre_topc(esk3_0,X45))=k2_pre_topc(esk4_0,k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,X45))|v3_tops_2(esk5_0,esk3_0,esk4_0))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_12])])])])])])).
% 0.21/0.53  fof(c_0_15, plain, ![X22, X23, X24]:(~l1_struct_0(X22)|(~l1_struct_0(X23)|(~v1_funct_1(X24)|~v1_funct_2(X24,u1_struct_0(X22),u1_struct_0(X23))|~m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X22),u1_struct_0(X23))))|(k2_relset_1(u1_struct_0(X22),u1_struct_0(X23),X24)!=k2_struct_0(X23)|~v2_funct_1(X24)|v2_funct_1(k2_tops_2(u1_struct_0(X22),u1_struct_0(X23),X24)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_tops_2])])])).
% 0.21/0.53  cnf(c_0_16, plain, (k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),k2_tops_2(u1_struct_0(X2),u1_struct_0(X1),X3))=k2_struct_0(X1)|v2_struct_0(X1)|k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),X3)!=k2_struct_0(X1)|~v2_funct_1(X3)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))|~l1_struct_0(X1)|~l1_struct_0(X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.21/0.53  cnf(c_0_17, negated_conjecture, (k2_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0)=k2_struct_0(esk4_0)|v3_tops_2(esk5_0,esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.53  cnf(c_0_18, negated_conjecture, (v1_funct_2(esk5_0,u1_struct_0(esk3_0),u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.53  cnf(c_0_19, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.53  cnf(c_0_20, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0))))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.53  cnf(c_0_21, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.53  cnf(c_0_22, negated_conjecture, (v2_funct_1(esk5_0)|v3_tops_2(esk5_0,esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.53  fof(c_0_23, plain, ![X7]:(~l1_pre_topc(X7)|l1_struct_0(X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.21/0.53  cnf(c_0_24, plain, (v2_funct_1(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3))|~l1_struct_0(X1)|~l1_struct_0(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)!=k2_struct_0(X2)|~v2_funct_1(X3)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.53  cnf(c_0_25, plain, (k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),k2_tops_2(u1_struct_0(X2),u1_struct_0(X1),X3))=k2_struct_0(X2)|v2_struct_0(X1)|k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),X3)!=k2_struct_0(X1)|~v2_funct_1(X3)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))|~l1_struct_0(X1)|~l1_struct_0(X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.21/0.53  fof(c_0_26, plain, ![X25, X26, X27, X28]:(~l1_struct_0(X25)|(~l1_struct_0(X26)|(~v1_funct_1(X27)|~v1_funct_2(X27,u1_struct_0(X25),u1_struct_0(X26))|~m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X25),u1_struct_0(X26))))|(~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X25)))|(k2_relset_1(u1_struct_0(X25),u1_struct_0(X26),X27)!=k2_struct_0(X26)|~v2_funct_1(X27)|k7_relset_1(u1_struct_0(X25),u1_struct_0(X26),X27,X28)=k8_relset_1(u1_struct_0(X26),u1_struct_0(X25),k2_tops_2(u1_struct_0(X25),u1_struct_0(X26),X27),X28)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t67_tops_2])])])).
% 0.21/0.53  cnf(c_0_27, negated_conjecture, (k1_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0))=k2_struct_0(esk4_0)|v3_tops_2(esk5_0,esk3_0,esk4_0)|~l1_struct_0(esk3_0)|~l1_struct_0(esk4_0)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_17]), c_0_18]), c_0_19]), c_0_20])]), c_0_21]), c_0_22])).
% 0.21/0.53  cnf(c_0_28, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.21/0.53  cnf(c_0_29, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.53  fof(c_0_30, plain, ![X11, X12, X13]:(((v1_funct_1(k2_tops_2(X11,X12,X13))|(~v1_funct_1(X13)|~v1_funct_2(X13,X11,X12)|~m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X11,X12)))))&(v1_funct_2(k2_tops_2(X11,X12,X13),X12,X11)|(~v1_funct_1(X13)|~v1_funct_2(X13,X11,X12)|~m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X11,X12))))))&(m1_subset_1(k2_tops_2(X11,X12,X13),k1_zfmisc_1(k2_zfmisc_1(X12,X11)))|(~v1_funct_1(X13)|~v1_funct_2(X13,X11,X12)|~m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X11,X12)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_tops_2])])])).
% 0.21/0.53  cnf(c_0_31, negated_conjecture, (v2_funct_1(k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0))|v3_tops_2(esk5_0,esk3_0,esk4_0)|~l1_struct_0(esk4_0)|~l1_struct_0(esk3_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_17]), c_0_18]), c_0_19]), c_0_20])]), c_0_22])).
% 0.21/0.53  cnf(c_0_32, negated_conjecture, (l1_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.53  cnf(c_0_33, negated_conjecture, (k2_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0))=k2_struct_0(esk3_0)|v3_tops_2(esk5_0,esk3_0,esk4_0)|~l1_struct_0(esk3_0)|~l1_struct_0(esk4_0)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_17]), c_0_18]), c_0_19]), c_0_20])]), c_0_21]), c_0_22])).
% 0.21/0.53  cnf(c_0_34, plain, (k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4)=k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3),X4)|~l1_struct_0(X1)|~l1_struct_0(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))|k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)!=k2_struct_0(X2)|~v2_funct_1(X3)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.21/0.53  fof(c_0_35, plain, ![X36, X37, X38, X39]:(((((k1_relset_1(u1_struct_0(X36),u1_struct_0(X37),X38)=k2_struct_0(X36)|~v3_tops_2(X38,X36,X37)|(~v1_funct_1(X38)|~v1_funct_2(X38,u1_struct_0(X36),u1_struct_0(X37))|~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X36),u1_struct_0(X37)))))|(~v2_pre_topc(X37)|~l1_pre_topc(X37))|(v2_struct_0(X36)|~v2_pre_topc(X36)|~l1_pre_topc(X36)))&(k2_relset_1(u1_struct_0(X36),u1_struct_0(X37),X38)=k2_struct_0(X37)|~v3_tops_2(X38,X36,X37)|(~v1_funct_1(X38)|~v1_funct_2(X38,u1_struct_0(X36),u1_struct_0(X37))|~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X36),u1_struct_0(X37)))))|(~v2_pre_topc(X37)|~l1_pre_topc(X37))|(v2_struct_0(X36)|~v2_pre_topc(X36)|~l1_pre_topc(X36))))&(v2_funct_1(X38)|~v3_tops_2(X38,X36,X37)|(~v1_funct_1(X38)|~v1_funct_2(X38,u1_struct_0(X36),u1_struct_0(X37))|~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X36),u1_struct_0(X37)))))|(~v2_pre_topc(X37)|~l1_pre_topc(X37))|(v2_struct_0(X36)|~v2_pre_topc(X36)|~l1_pre_topc(X36))))&(~m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(X37)))|k8_relset_1(u1_struct_0(X36),u1_struct_0(X37),X38,k2_pre_topc(X37,X39))=k2_pre_topc(X36,k8_relset_1(u1_struct_0(X36),u1_struct_0(X37),X38,X39))|~v3_tops_2(X38,X36,X37)|(~v1_funct_1(X38)|~v1_funct_2(X38,u1_struct_0(X36),u1_struct_0(X37))|~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X36),u1_struct_0(X37)))))|(~v2_pre_topc(X37)|~l1_pre_topc(X37))|(v2_struct_0(X36)|~v2_pre_topc(X36)|~l1_pre_topc(X36))))&((m1_subset_1(esk2_3(X36,X37,X38),k1_zfmisc_1(u1_struct_0(X37)))|(k1_relset_1(u1_struct_0(X36),u1_struct_0(X37),X38)!=k2_struct_0(X36)|k2_relset_1(u1_struct_0(X36),u1_struct_0(X37),X38)!=k2_struct_0(X37)|~v2_funct_1(X38))|v3_tops_2(X38,X36,X37)|(~v1_funct_1(X38)|~v1_funct_2(X38,u1_struct_0(X36),u1_struct_0(X37))|~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X36),u1_struct_0(X37)))))|(~v2_pre_topc(X37)|~l1_pre_topc(X37))|(v2_struct_0(X36)|~v2_pre_topc(X36)|~l1_pre_topc(X36)))&(k8_relset_1(u1_struct_0(X36),u1_struct_0(X37),X38,k2_pre_topc(X37,esk2_3(X36,X37,X38)))!=k2_pre_topc(X36,k8_relset_1(u1_struct_0(X36),u1_struct_0(X37),X38,esk2_3(X36,X37,X38)))|(k1_relset_1(u1_struct_0(X36),u1_struct_0(X37),X38)!=k2_struct_0(X36)|k2_relset_1(u1_struct_0(X36),u1_struct_0(X37),X38)!=k2_struct_0(X37)|~v2_funct_1(X38))|v3_tops_2(X38,X36,X37)|(~v1_funct_1(X38)|~v1_funct_2(X38,u1_struct_0(X36),u1_struct_0(X37))|~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X36),u1_struct_0(X37)))))|(~v2_pre_topc(X37)|~l1_pre_topc(X37))|(v2_struct_0(X36)|~v2_pre_topc(X36)|~l1_pre_topc(X36))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t73_tops_2])])])])])])).
% 0.21/0.53  cnf(c_0_36, negated_conjecture, (k1_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0))=k2_struct_0(esk4_0)|v3_tops_2(esk5_0,esk3_0,esk4_0)|~l1_struct_0(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_29])])).
% 0.21/0.53  cnf(c_0_37, plain, (v1_funct_2(k2_tops_2(X1,X2,X3),X2,X1)|~v1_funct_1(X3)|~v1_funct_2(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.21/0.53  cnf(c_0_38, plain, (v1_funct_1(k2_tops_2(X1,X2,X3))|~v1_funct_1(X3)|~v1_funct_2(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.21/0.53  cnf(c_0_39, plain, (m1_subset_1(k2_tops_2(X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))|~v1_funct_1(X3)|~v1_funct_2(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.21/0.53  cnf(c_0_40, negated_conjecture, (v2_funct_1(k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0))|v3_tops_2(esk5_0,esk3_0,esk4_0)|~l1_struct_0(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_28]), c_0_32])])).
% 0.21/0.53  cnf(c_0_41, negated_conjecture, (k2_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0))=k2_struct_0(esk3_0)|v3_tops_2(esk5_0,esk3_0,esk4_0)|~l1_struct_0(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_28]), c_0_29])])).
% 0.21/0.53  cnf(c_0_42, negated_conjecture, (k8_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),X1)=k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,X1)|v3_tops_2(esk5_0,esk3_0,esk4_0)|~l1_struct_0(esk4_0)|~l1_struct_0(esk3_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_17]), c_0_18]), c_0_19]), c_0_20])]), c_0_22])).
% 0.21/0.53  fof(c_0_43, plain, ![X5, X6]:(~l1_pre_topc(X5)|~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5)))|m1_subset_1(k2_pre_topc(X5,X6),k1_zfmisc_1(u1_struct_0(X5)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).
% 0.21/0.53  cnf(c_0_44, plain, (m1_subset_1(esk2_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X2)))|v3_tops_2(X3,X1,X2)|v2_struct_0(X1)|k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)!=k2_struct_0(X1)|k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)!=k2_struct_0(X2)|~v2_funct_1(X3)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.21/0.53  cnf(c_0_45, negated_conjecture, (k1_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0))=k2_struct_0(esk4_0)|v3_tops_2(esk5_0,esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_28]), c_0_32])])).
% 0.21/0.53  cnf(c_0_46, negated_conjecture, (v2_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.53  cnf(c_0_47, negated_conjecture, (v2_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.53  cnf(c_0_48, negated_conjecture, (v1_funct_2(k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),u1_struct_0(esk4_0),u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_18]), c_0_19]), c_0_20])])).
% 0.21/0.53  cnf(c_0_49, negated_conjecture, (v1_funct_1(k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_18]), c_0_19]), c_0_20])])).
% 0.21/0.53  cnf(c_0_50, negated_conjecture, (m1_subset_1(k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_18]), c_0_19]), c_0_20])])).
% 0.21/0.53  cnf(c_0_51, negated_conjecture, (v2_funct_1(k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0))|v3_tops_2(esk5_0,esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_28]), c_0_29])])).
% 0.21/0.53  cnf(c_0_52, negated_conjecture, (k2_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0))=k2_struct_0(esk3_0)|v3_tops_2(esk5_0,esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_28]), c_0_32])])).
% 0.21/0.53  cnf(c_0_53, negated_conjecture, (k8_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),X1)=k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,X1)|v3_tops_2(esk5_0,esk3_0,esk4_0)|~l1_struct_0(esk3_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_28]), c_0_32])])).
% 0.21/0.53  cnf(c_0_54, plain, (m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.21/0.53  cnf(c_0_55, negated_conjecture, (v3_tops_2(k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),esk4_0,esk3_0)|v3_tops_2(esk5_0,esk3_0,esk4_0)|m1_subset_1(esk2_3(esk4_0,esk3_0,k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0)),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_46]), c_0_47]), c_0_48]), c_0_49]), c_0_50]), c_0_29]), c_0_32])]), c_0_21]), c_0_51]), c_0_52])).
% 0.21/0.53  cnf(c_0_56, negated_conjecture, (k8_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),X1)=k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,X1)|v3_tops_2(esk5_0,esk3_0,esk4_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_28]), c_0_29])])).
% 0.21/0.53  cnf(c_0_57, negated_conjecture, (v3_tops_2(k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),esk4_0,esk3_0)|v3_tops_2(esk5_0,esk3_0,esk4_0)|m1_subset_1(k2_pre_topc(esk3_0,esk2_3(esk4_0,esk3_0,k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0))),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_29])])).
% 0.21/0.53  fof(c_0_58, plain, ![X29, X30, X31, X32]:(~l1_struct_0(X29)|(~l1_struct_0(X30)|(~v1_funct_1(X31)|~v1_funct_2(X31,u1_struct_0(X29),u1_struct_0(X30))|~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X29),u1_struct_0(X30))))|(~m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X30)))|(k2_relset_1(u1_struct_0(X29),u1_struct_0(X30),X31)!=k2_struct_0(X30)|~v2_funct_1(X31)|k8_relset_1(u1_struct_0(X29),u1_struct_0(X30),X31,X32)=k7_relset_1(u1_struct_0(X30),u1_struct_0(X29),k2_tops_2(u1_struct_0(X29),u1_struct_0(X30),X31),X32)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t68_tops_2])])])).
% 0.21/0.53  cnf(c_0_59, plain, (v3_tops_2(X3,X1,X2)|v2_struct_0(X1)|k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,k2_pre_topc(X2,esk2_3(X1,X2,X3)))!=k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,esk2_3(X1,X2,X3)))|k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)!=k2_struct_0(X1)|k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)!=k2_struct_0(X2)|~v2_funct_1(X3)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.21/0.53  cnf(c_0_60, negated_conjecture, (k8_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),k2_pre_topc(esk3_0,esk2_3(esk4_0,esk3_0,k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0))))=k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,k2_pre_topc(esk3_0,esk2_3(esk4_0,esk3_0,k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0))))|v3_tops_2(k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),esk4_0,esk3_0)|v3_tops_2(esk5_0,esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.21/0.53  cnf(c_0_61, negated_conjecture, (k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,k2_pre_topc(esk3_0,X1))=k2_pre_topc(esk4_0,k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,X1))|v3_tops_2(esk5_0,esk3_0,esk4_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.53  cnf(c_0_62, plain, (k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4)=k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3),X4)|~l1_struct_0(X1)|~l1_struct_0(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))|k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)!=k2_struct_0(X2)|~v2_funct_1(X3)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.21/0.53  fof(c_0_63, plain, ![X8, X9, X10]:((((((k1_relset_1(u1_struct_0(X8),u1_struct_0(X9),X10)=k2_struct_0(X8)|~v3_tops_2(X10,X8,X9)|(~v1_funct_1(X10)|~v1_funct_2(X10,u1_struct_0(X8),u1_struct_0(X9))|~m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X8),u1_struct_0(X9)))))|~l1_pre_topc(X9)|~l1_pre_topc(X8))&(k2_relset_1(u1_struct_0(X8),u1_struct_0(X9),X10)=k2_struct_0(X9)|~v3_tops_2(X10,X8,X9)|(~v1_funct_1(X10)|~v1_funct_2(X10,u1_struct_0(X8),u1_struct_0(X9))|~m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X8),u1_struct_0(X9)))))|~l1_pre_topc(X9)|~l1_pre_topc(X8)))&(v2_funct_1(X10)|~v3_tops_2(X10,X8,X9)|(~v1_funct_1(X10)|~v1_funct_2(X10,u1_struct_0(X8),u1_struct_0(X9))|~m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X8),u1_struct_0(X9)))))|~l1_pre_topc(X9)|~l1_pre_topc(X8)))&(v5_pre_topc(X10,X8,X9)|~v3_tops_2(X10,X8,X9)|(~v1_funct_1(X10)|~v1_funct_2(X10,u1_struct_0(X8),u1_struct_0(X9))|~m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X8),u1_struct_0(X9)))))|~l1_pre_topc(X9)|~l1_pre_topc(X8)))&(v5_pre_topc(k2_tops_2(u1_struct_0(X8),u1_struct_0(X9),X10),X9,X8)|~v3_tops_2(X10,X8,X9)|(~v1_funct_1(X10)|~v1_funct_2(X10,u1_struct_0(X8),u1_struct_0(X9))|~m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X8),u1_struct_0(X9)))))|~l1_pre_topc(X9)|~l1_pre_topc(X8)))&(k1_relset_1(u1_struct_0(X8),u1_struct_0(X9),X10)!=k2_struct_0(X8)|k2_relset_1(u1_struct_0(X8),u1_struct_0(X9),X10)!=k2_struct_0(X9)|~v2_funct_1(X10)|~v5_pre_topc(X10,X8,X9)|~v5_pre_topc(k2_tops_2(u1_struct_0(X8),u1_struct_0(X9),X10),X9,X8)|v3_tops_2(X10,X8,X9)|(~v1_funct_1(X10)|~v1_funct_2(X10,u1_struct_0(X8),u1_struct_0(X9))|~m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X8),u1_struct_0(X9)))))|~l1_pre_topc(X9)|~l1_pre_topc(X8))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_tops_2])])])])).
% 0.21/0.53  cnf(c_0_64, negated_conjecture, (v3_tops_2(k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),esk4_0,esk3_0)|v3_tops_2(esk5_0,esk3_0,esk4_0)|k2_pre_topc(esk4_0,k8_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),esk2_3(esk4_0,esk3_0,k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0))))!=k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,k2_pre_topc(esk3_0,esk2_3(esk4_0,esk3_0,k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0))))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_46]), c_0_47]), c_0_48]), c_0_49]), c_0_50]), c_0_29]), c_0_32])]), c_0_21]), c_0_51]), c_0_52]), c_0_45])).
% 0.21/0.53  cnf(c_0_65, negated_conjecture, (k8_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),esk2_3(esk4_0,esk3_0,k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0)))=k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,esk2_3(esk4_0,esk3_0,k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0)))|v3_tops_2(k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),esk4_0,esk3_0)|v3_tops_2(esk5_0,esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_56, c_0_55])).
% 0.21/0.53  cnf(c_0_66, negated_conjecture, (k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,k2_pre_topc(esk3_0,esk2_3(esk4_0,esk3_0,k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0))))=k2_pre_topc(esk4_0,k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,esk2_3(esk4_0,esk3_0,k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0))))|v3_tops_2(k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),esk4_0,esk3_0)|v3_tops_2(esk5_0,esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_61, c_0_55])).
% 0.21/0.53  cnf(c_0_67, negated_conjecture, (k8_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),X1)=k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0)),X1)|v3_tops_2(esk5_0,esk3_0,esk4_0)|~l1_struct_0(esk3_0)|~l1_struct_0(esk4_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_52]), c_0_48]), c_0_49]), c_0_50])]), c_0_51])).
% 0.21/0.53  fof(c_0_68, plain, ![X14, X15, X16, X17]:((~v5_pre_topc(X16,X14,X15)|(~m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X14)))|r1_tarski(k7_relset_1(u1_struct_0(X14),u1_struct_0(X15),X16,k2_pre_topc(X14,X17)),k2_pre_topc(X15,k7_relset_1(u1_struct_0(X14),u1_struct_0(X15),X16,X17))))|(~v1_funct_1(X16)|~v1_funct_2(X16,u1_struct_0(X14),u1_struct_0(X15))|~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X14),u1_struct_0(X15)))))|(v2_struct_0(X15)|~v2_pre_topc(X15)|~l1_pre_topc(X15))|(~v2_pre_topc(X14)|~l1_pre_topc(X14)))&((m1_subset_1(esk1_3(X14,X15,X16),k1_zfmisc_1(u1_struct_0(X14)))|v5_pre_topc(X16,X14,X15)|(~v1_funct_1(X16)|~v1_funct_2(X16,u1_struct_0(X14),u1_struct_0(X15))|~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X14),u1_struct_0(X15)))))|(v2_struct_0(X15)|~v2_pre_topc(X15)|~l1_pre_topc(X15))|(~v2_pre_topc(X14)|~l1_pre_topc(X14)))&(~r1_tarski(k7_relset_1(u1_struct_0(X14),u1_struct_0(X15),X16,k2_pre_topc(X14,esk1_3(X14,X15,X16))),k2_pre_topc(X15,k7_relset_1(u1_struct_0(X14),u1_struct_0(X15),X16,esk1_3(X14,X15,X16))))|v5_pre_topc(X16,X14,X15)|(~v1_funct_1(X16)|~v1_funct_2(X16,u1_struct_0(X14),u1_struct_0(X15))|~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X14),u1_struct_0(X15)))))|(v2_struct_0(X15)|~v2_pre_topc(X15)|~l1_pre_topc(X15))|(~v2_pre_topc(X14)|~l1_pre_topc(X14))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t57_tops_2])])])])])])).
% 0.21/0.53  cnf(c_0_69, plain, (v5_pre_topc(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3),X2,X1)|~v3_tops_2(X3,X1,X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.21/0.53  cnf(c_0_70, negated_conjecture, (v3_tops_2(k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),esk4_0,esk3_0)|v3_tops_2(esk5_0,esk3_0,esk4_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_66])).
% 0.21/0.53  cnf(c_0_71, negated_conjecture, (v1_funct_1(k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0)))|~m1_subset_1(k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_48]), c_0_49])])).
% 0.21/0.53  cnf(c_0_72, negated_conjecture, (k8_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),X1)=k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0)),X1)|v3_tops_2(esk5_0,esk3_0,esk4_0)|~l1_struct_0(esk4_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_28]), c_0_29])])).
% 0.21/0.53  cnf(c_0_73, plain, (m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))|v5_pre_topc(X3,X1,X2)|v2_struct_0(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.21/0.53  cnf(c_0_74, plain, (r1_tarski(k7_relset_1(u1_struct_0(X2),u1_struct_0(X3),X1,k2_pre_topc(X2,X4)),k2_pre_topc(X3,k7_relset_1(u1_struct_0(X2),u1_struct_0(X3),X1,X4)))|v2_struct_0(X3)|~v5_pre_topc(X1,X2,X3)|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))|~v1_funct_1(X1)|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))|~v2_pre_topc(X3)|~l1_pre_topc(X3)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.21/0.53  cnf(c_0_75, negated_conjecture, (v5_pre_topc(k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0)),esk3_0,esk4_0)|v3_tops_2(esk5_0,esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_48]), c_0_49]), c_0_50]), c_0_29]), c_0_32])])).
% 0.21/0.53  cnf(c_0_76, negated_conjecture, (v1_funct_2(k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0)),u1_struct_0(esk3_0),u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_48]), c_0_49])]), c_0_50])])).
% 0.21/0.53  cnf(c_0_77, negated_conjecture, (v1_funct_1(k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_71, c_0_50])])).
% 0.21/0.53  cnf(c_0_78, negated_conjecture, (m1_subset_1(k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_48]), c_0_49])]), c_0_50])])).
% 0.21/0.53  cnf(c_0_79, negated_conjecture, (k8_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),X1)=k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0)),X1)|v3_tops_2(esk5_0,esk3_0,esk4_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_28]), c_0_32])])).
% 0.21/0.53  cnf(c_0_80, negated_conjecture, (v5_pre_topc(esk5_0,esk3_0,esk4_0)|m1_subset_1(esk1_3(esk3_0,esk4_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_18]), c_0_47]), c_0_46]), c_0_19]), c_0_20]), c_0_32]), c_0_29])]), c_0_21])).
% 0.21/0.53  cnf(c_0_81, negated_conjecture, (r1_tarski(k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0)),k2_pre_topc(esk3_0,X1)),k2_pre_topc(esk4_0,k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0)),X1)))|v3_tops_2(esk5_0,esk3_0,esk4_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_75]), c_0_47]), c_0_46]), c_0_76]), c_0_77]), c_0_78]), c_0_32]), c_0_29])]), c_0_21])).
% 0.21/0.53  cnf(c_0_82, negated_conjecture, (k8_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),esk1_3(esk3_0,esk4_0,esk5_0))=k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0)),esk1_3(esk3_0,esk4_0,esk5_0))|v5_pre_topc(esk5_0,esk3_0,esk4_0)|v3_tops_2(esk5_0,esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_79, c_0_80])).
% 0.21/0.53  cnf(c_0_83, negated_conjecture, (k8_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),esk1_3(esk3_0,esk4_0,esk5_0))=k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,esk1_3(esk3_0,esk4_0,esk5_0))|v5_pre_topc(esk5_0,esk3_0,esk4_0)|v3_tops_2(esk5_0,esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_56, c_0_80])).
% 0.21/0.53  cnf(c_0_84, negated_conjecture, (v5_pre_topc(esk5_0,esk3_0,esk4_0)|m1_subset_1(k2_pre_topc(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0)),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_80]), c_0_29])])).
% 0.21/0.53  cnf(c_0_85, negated_conjecture, (r1_tarski(k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0)),k2_pre_topc(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0))),k2_pre_topc(esk4_0,k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0)),esk1_3(esk3_0,esk4_0,esk5_0))))|v5_pre_topc(esk5_0,esk3_0,esk4_0)|v3_tops_2(esk5_0,esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_81, c_0_80])).
% 0.21/0.53  cnf(c_0_86, negated_conjecture, (k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0)),esk1_3(esk3_0,esk4_0,esk5_0))=k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,esk1_3(esk3_0,esk4_0,esk5_0))|v5_pre_topc(esk5_0,esk3_0,esk4_0)|v3_tops_2(esk5_0,esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_82, c_0_83])).
% 0.21/0.53  cnf(c_0_87, negated_conjecture, (k8_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),k2_pre_topc(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0)))=k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,k2_pre_topc(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0)))|v5_pre_topc(esk5_0,esk3_0,esk4_0)|v3_tops_2(esk5_0,esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_56, c_0_84])).
% 0.21/0.53  cnf(c_0_88, negated_conjecture, (k8_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),k2_pre_topc(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0)))=k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0)),k2_pre_topc(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0)))|v5_pre_topc(esk5_0,esk3_0,esk4_0)|v3_tops_2(esk5_0,esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_79, c_0_84])).
% 0.21/0.53  cnf(c_0_89, negated_conjecture, (r1_tarski(k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0)),k2_pre_topc(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0))),k2_pre_topc(esk4_0,k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,esk1_3(esk3_0,esk4_0,esk5_0))))|v5_pre_topc(esk5_0,esk3_0,esk4_0)|v3_tops_2(esk5_0,esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_85, c_0_86])).
% 0.21/0.53  cnf(c_0_90, negated_conjecture, (k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0)),k2_pre_topc(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0)))=k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,k2_pre_topc(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0)))|v5_pre_topc(esk5_0,esk3_0,esk4_0)|v3_tops_2(esk5_0,esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_87, c_0_88])).
% 0.21/0.53  cnf(c_0_91, plain, (v5_pre_topc(X3,X1,X2)|v2_struct_0(X2)|~r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,k2_pre_topc(X1,esk1_3(X1,X2,X3))),k2_pre_topc(X2,k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,esk1_3(X1,X2,X3))))|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.21/0.53  cnf(c_0_92, negated_conjecture, (r1_tarski(k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,k2_pre_topc(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0))),k2_pre_topc(esk4_0,k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,esk1_3(esk3_0,esk4_0,esk5_0))))|v5_pre_topc(esk5_0,esk3_0,esk4_0)|v3_tops_2(esk5_0,esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_89, c_0_90])).
% 0.21/0.53  cnf(c_0_93, plain, (v5_pre_topc(X1,X2,X3)|~v3_tops_2(X1,X2,X3)|~v1_funct_1(X1)|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))|~l1_pre_topc(X3)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.21/0.53  cnf(c_0_94, plain, (v3_tops_2(X3,X1,X2)|k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)!=k2_struct_0(X1)|k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)!=k2_struct_0(X2)|~v2_funct_1(X3)|~v5_pre_topc(X3,X1,X2)|~v5_pre_topc(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3),X2,X1)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.21/0.53  cnf(c_0_95, negated_conjecture, (v5_pre_topc(esk5_0,esk3_0,esk4_0)|v3_tops_2(esk5_0,esk3_0,esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_92]), c_0_47]), c_0_46]), c_0_18]), c_0_19]), c_0_20]), c_0_32]), c_0_29])]), c_0_21])).
% 0.21/0.53  cnf(c_0_96, negated_conjecture, (v5_pre_topc(k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),esk4_0,esk3_0)|v3_tops_2(esk5_0,esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_70]), c_0_48]), c_0_49]), c_0_50]), c_0_29]), c_0_32])])).
% 0.21/0.53  cnf(c_0_97, negated_conjecture, (k1_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0)=k2_struct_0(esk3_0)|v3_tops_2(esk5_0,esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.53  cnf(c_0_98, plain, (k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)=k2_struct_0(X2)|~v3_tops_2(X3,X1,X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.21/0.53  cnf(c_0_99, negated_conjecture, (v3_tops_2(esk5_0,esk3_0,esk4_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_95]), c_0_18]), c_0_19]), c_0_20]), c_0_32]), c_0_29])]), c_0_22]), c_0_96]), c_0_17]), c_0_97])).
% 0.21/0.53  cnf(c_0_100, plain, (v2_funct_1(X1)|~v3_tops_2(X1,X2,X3)|~v1_funct_1(X1)|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))|~l1_pre_topc(X3)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.21/0.53  cnf(c_0_101, negated_conjecture, (k2_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0)=k2_struct_0(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_99]), c_0_18]), c_0_19]), c_0_20]), c_0_32]), c_0_29])])).
% 0.21/0.53  cnf(c_0_102, negated_conjecture, (v2_funct_1(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_99]), c_0_18]), c_0_19]), c_0_20]), c_0_32]), c_0_29])])).
% 0.21/0.53  cnf(c_0_103, plain, (k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)=k2_struct_0(X1)|~v3_tops_2(X3,X1,X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.21/0.53  fof(c_0_104, plain, ![X33, X34, X35]:(~l1_pre_topc(X33)|(v2_struct_0(X34)|~l1_pre_topc(X34)|(~v1_funct_1(X35)|~v1_funct_2(X35,u1_struct_0(X33),u1_struct_0(X34))|~m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X33),u1_struct_0(X34))))|(~v3_tops_2(X35,X33,X34)|v3_tops_2(k2_tops_2(u1_struct_0(X33),u1_struct_0(X34),X35),X34,X33))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t70_tops_2])])])])).
% 0.21/0.53  cnf(c_0_105, negated_conjecture, (k8_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),X1)=k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,X1)|~l1_struct_0(esk4_0)|~l1_struct_0(esk3_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_101]), c_0_102]), c_0_18]), c_0_19]), c_0_20])])).
% 0.21/0.53  cnf(c_0_106, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk3_0)))|k1_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0)!=k2_struct_0(esk3_0)|k2_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0)!=k2_struct_0(esk4_0)|~v2_funct_1(esk5_0)|~v3_tops_2(esk5_0,esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.53  cnf(c_0_107, negated_conjecture, (k1_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0)=k2_struct_0(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103, c_0_99]), c_0_18]), c_0_19]), c_0_20]), c_0_32]), c_0_29])])).
% 0.21/0.53  cnf(c_0_108, plain, (v2_struct_0(X2)|v3_tops_2(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3),X2,X1)|~l1_pre_topc(X1)|~l1_pre_topc(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~v3_tops_2(X3,X1,X2)), inference(split_conjunct,[status(thm)],[c_0_104])).
% 0.21/0.53  cnf(c_0_109, negated_conjecture, (k8_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),X1)=k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,X1)|~l1_struct_0(esk3_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105, c_0_28]), c_0_32])])).
% 0.21/0.53  cnf(c_0_110, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_106, c_0_99])]), c_0_107]), c_0_101]), c_0_102])])).
% 0.21/0.53  cnf(c_0_111, plain, (k8_relset_1(u1_struct_0(X3),u1_struct_0(X2),X4,k2_pre_topc(X2,X1))=k2_pre_topc(X3,k8_relset_1(u1_struct_0(X3),u1_struct_0(X2),X4,X1))|v2_struct_0(X3)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v3_tops_2(X4,X3,X2)|~v1_funct_1(X4)|~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v2_pre_topc(X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.21/0.53  cnf(c_0_112, negated_conjecture, (v3_tops_2(k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),esk4_0,esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108, c_0_99]), c_0_18]), c_0_19]), c_0_20]), c_0_32]), c_0_29])]), c_0_21])).
% 0.21/0.53  cnf(c_0_113, negated_conjecture, (k8_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),X1)=k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,X1)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109, c_0_28]), c_0_29])])).
% 0.21/0.53  cnf(c_0_114, negated_conjecture, (m1_subset_1(k2_pre_topc(esk3_0,esk6_0),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_110]), c_0_29])])).
% 0.21/0.53  cnf(c_0_115, negated_conjecture, (k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,k2_pre_topc(esk3_0,esk6_0))!=k2_pre_topc(esk4_0,k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,esk6_0))|k1_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0)!=k2_struct_0(esk3_0)|k2_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0)!=k2_struct_0(esk4_0)|~v2_funct_1(esk5_0)|~v3_tops_2(esk5_0,esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.53  cnf(c_0_116, negated_conjecture, (k8_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),k2_pre_topc(esk3_0,X1))=k2_pre_topc(esk4_0,k8_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),X1))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111, c_0_112]), c_0_47]), c_0_46]), c_0_48]), c_0_49]), c_0_50]), c_0_32]), c_0_29])]), c_0_21])).
% 0.21/0.53  cnf(c_0_117, negated_conjecture, (k8_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),k2_pre_topc(esk3_0,esk6_0))=k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,k2_pre_topc(esk3_0,esk6_0))), inference(spm,[status(thm)],[c_0_113, c_0_114])).
% 0.21/0.53  cnf(c_0_118, negated_conjecture, (k8_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),esk6_0)=k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,esk6_0)), inference(spm,[status(thm)],[c_0_113, c_0_110])).
% 0.21/0.53  cnf(c_0_119, negated_conjecture, (k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,k2_pre_topc(esk3_0,esk6_0))!=k2_pre_topc(esk4_0,k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_115, c_0_99])]), c_0_107]), c_0_101]), c_0_102])])).
% 0.21/0.53  cnf(c_0_120, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116, c_0_110]), c_0_117]), c_0_118]), c_0_119]), ['proof']).
% 0.21/0.53  # SZS output end CNFRefutation
% 0.21/0.53  # Proof object total steps             : 121
% 0.21/0.53  # Proof object clause steps            : 96
% 0.21/0.53  # Proof object formula steps           : 25
% 0.21/0.53  # Proof object conjectures             : 76
% 0.21/0.53  # Proof object clause conjectures      : 73
% 0.21/0.53  # Proof object formula conjectures     : 3
% 0.21/0.53  # Proof object initial clauses used    : 37
% 0.21/0.53  # Proof object initial formulas used   : 12
% 0.21/0.53  # Proof object generating inferences   : 56
% 0.21/0.53  # Proof object simplifying inferences  : 204
% 0.21/0.53  # Training examples: 0 positive, 0 negative
% 0.21/0.53  # Parsed axioms                        : 12
% 0.21/0.53  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.53  # Initial clauses                      : 40
% 0.21/0.53  # Removed in clause preprocessing      : 0
% 0.21/0.53  # Initial clauses in saturation        : 40
% 0.21/0.53  # Processed clauses                    : 1471
% 0.21/0.53  # ...of these trivial                  : 1
% 0.21/0.53  # ...subsumed                          : 755
% 0.21/0.53  # ...remaining for further processing  : 715
% 0.21/0.53  # Other redundant clauses eliminated   : 0
% 0.21/0.53  # Clauses deleted for lack of memory   : 0
% 0.21/0.53  # Backward-subsumed                    : 455
% 0.21/0.53  # Backward-rewritten                   : 131
% 0.21/0.53  # Generated clauses                    : 2444
% 0.21/0.53  # ...of the previous two non-trivial   : 2414
% 0.21/0.53  # Contextual simplify-reflections      : 53
% 0.21/0.53  # Paramodulations                      : 2444
% 0.21/0.53  # Factorizations                       : 0
% 0.21/0.53  # Equation resolutions                 : 0
% 0.21/0.53  # Propositional unsat checks           : 0
% 0.21/0.53  #    Propositional check models        : 0
% 0.21/0.53  #    Propositional check unsatisfiable : 0
% 0.21/0.53  #    Propositional clauses             : 0
% 0.21/0.53  #    Propositional clauses after purity: 0
% 0.21/0.53  #    Propositional unsat core size     : 0
% 0.21/0.53  #    Propositional preprocessing time  : 0.000
% 0.21/0.53  #    Propositional encoding time       : 0.000
% 0.21/0.53  #    Propositional solver time         : 0.000
% 0.21/0.53  #    Success case prop preproc time    : 0.000
% 0.21/0.53  #    Success case prop encoding time   : 0.000
% 0.21/0.53  #    Success case prop solver time     : 0.000
% 0.21/0.53  # Current number of processed clauses  : 92
% 0.21/0.53  #    Positive orientable unit clauses  : 60
% 0.21/0.53  #    Positive unorientable unit clauses: 0
% 0.21/0.53  #    Negative unit clauses             : 2
% 0.21/0.53  #    Non-unit-clauses                  : 30
% 0.21/0.53  # Current number of unprocessed clauses: 81
% 0.21/0.53  # ...number of literals in the above   : 176
% 0.21/0.53  # Current number of archived formulas  : 0
% 0.21/0.53  # Current number of archived clauses   : 623
% 0.21/0.53  # Clause-clause subsumption calls (NU) : 85152
% 0.21/0.53  # Rec. Clause-clause subsumption calls : 23122
% 0.21/0.53  # Non-unit clause-clause subsumptions  : 1263
% 0.21/0.53  # Unit Clause-clause subsumption calls : 810
% 0.21/0.53  # Rewrite failures with RHS unbound    : 0
% 0.21/0.53  # BW rewrite match attempts            : 252
% 0.21/0.53  # BW rewrite match successes           : 8
% 0.21/0.53  # Condensation attempts                : 0
% 0.21/0.53  # Condensation successes               : 0
% 0.21/0.53  # Termbank termtop insertions          : 207633
% 0.21/0.53  
% 0.21/0.53  # -------------------------------------------------
% 0.21/0.53  # User time                : 0.191 s
% 0.21/0.53  # System time              : 0.005 s
% 0.21/0.53  # Total time               : 0.196 s
% 0.21/0.53  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------
