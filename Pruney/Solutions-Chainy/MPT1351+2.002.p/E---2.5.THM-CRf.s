%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:14:07 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   44 ( 159 expanded)
%              Number of clauses        :   31 (  49 expanded)
%              Number of leaves         :    6 (  40 expanded)
%              Depth                    :   10
%              Number of atoms          :  275 (1579 expanded)
%              Number of equality atoms :   15 (  27 expanded)
%              Maximal formula depth    :   20 (   6 average)
%              Maximal clause size      :   46 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t75_tops_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v2_pre_topc(X2)
            & l1_pre_topc(X2) )
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
             => ! [X4] :
                  ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( v5_pre_topc(X3,X1,X2)
                      & v2_connsp_1(X4,X1) )
                   => v2_connsp_1(k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4),X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_tops_2)).

fof(dt_k2_tops_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( v1_funct_1(k2_tops_2(X1,X2,X3))
        & v1_funct_2(k2_tops_2(X1,X2,X3),X2,X1)
        & m1_subset_1(k2_tops_2(X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_2)).

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

fof(t76_tops_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v2_pre_topc(X2)
            & l1_pre_topc(X2) )
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
             => ! [X4] :
                  ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
                 => ( ( v3_tops_2(X3,X1,X2)
                      & v2_connsp_1(X4,X2) )
                   => v2_connsp_1(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4),X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tops_2)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_tops_2)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(c_0_6,plain,(
    ! [X16,X17,X18,X19] :
      ( v2_struct_0(X16)
      | ~ v2_pre_topc(X16)
      | ~ l1_pre_topc(X16)
      | v2_struct_0(X17)
      | ~ v2_pre_topc(X17)
      | ~ l1_pre_topc(X17)
      | ~ v1_funct_1(X18)
      | ~ v1_funct_2(X18,u1_struct_0(X16),u1_struct_0(X17))
      | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X16),u1_struct_0(X17))))
      | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X16)))
      | ~ v5_pre_topc(X18,X16,X17)
      | ~ v2_connsp_1(X19,X16)
      | v2_connsp_1(k7_relset_1(u1_struct_0(X16),u1_struct_0(X17),X18,X19),X17) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t75_tops_2])])])])).

fof(c_0_7,plain,(
    ! [X9,X10,X11] :
      ( ( v1_funct_1(k2_tops_2(X9,X10,X11))
        | ~ v1_funct_1(X11)
        | ~ v1_funct_2(X11,X9,X10)
        | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X9,X10))) )
      & ( v1_funct_2(k2_tops_2(X9,X10,X11),X10,X9)
        | ~ v1_funct_1(X11)
        | ~ v1_funct_2(X11,X9,X10)
        | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X9,X10))) )
      & ( m1_subset_1(k2_tops_2(X9,X10,X11),k1_zfmisc_1(k2_zfmisc_1(X10,X9)))
        | ~ v1_funct_1(X11)
        | ~ v1_funct_2(X11,X9,X10)
        | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X9,X10))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_tops_2])])])).

cnf(c_0_8,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_connsp_1(k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4),X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v5_pre_topc(X3,X1,X2)
    | ~ v2_connsp_1(X4,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_9,plain,
    ( m1_subset_1(k2_tops_2(X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_10,plain,
    ( v1_funct_1(k2_tops_2(X1,X2,X3))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,plain,
    ( v1_funct_2(k2_tops_2(X1,X2,X3),X2,X1)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_12,plain,(
    ! [X6,X7,X8] :
      ( ( k1_relset_1(u1_struct_0(X6),u1_struct_0(X7),X8) = k2_struct_0(X6)
        | ~ v3_tops_2(X8,X6,X7)
        | ~ v1_funct_1(X8)
        | ~ v1_funct_2(X8,u1_struct_0(X6),u1_struct_0(X7))
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),u1_struct_0(X7))))
        | ~ l1_pre_topc(X7)
        | ~ l1_pre_topc(X6) )
      & ( k2_relset_1(u1_struct_0(X6),u1_struct_0(X7),X8) = k2_struct_0(X7)
        | ~ v3_tops_2(X8,X6,X7)
        | ~ v1_funct_1(X8)
        | ~ v1_funct_2(X8,u1_struct_0(X6),u1_struct_0(X7))
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),u1_struct_0(X7))))
        | ~ l1_pre_topc(X7)
        | ~ l1_pre_topc(X6) )
      & ( v2_funct_1(X8)
        | ~ v3_tops_2(X8,X6,X7)
        | ~ v1_funct_1(X8)
        | ~ v1_funct_2(X8,u1_struct_0(X6),u1_struct_0(X7))
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),u1_struct_0(X7))))
        | ~ l1_pre_topc(X7)
        | ~ l1_pre_topc(X6) )
      & ( v5_pre_topc(X8,X6,X7)
        | ~ v3_tops_2(X8,X6,X7)
        | ~ v1_funct_1(X8)
        | ~ v1_funct_2(X8,u1_struct_0(X6),u1_struct_0(X7))
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),u1_struct_0(X7))))
        | ~ l1_pre_topc(X7)
        | ~ l1_pre_topc(X6) )
      & ( v5_pre_topc(k2_tops_2(u1_struct_0(X6),u1_struct_0(X7),X8),X7,X6)
        | ~ v3_tops_2(X8,X6,X7)
        | ~ v1_funct_1(X8)
        | ~ v1_funct_2(X8,u1_struct_0(X6),u1_struct_0(X7))
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),u1_struct_0(X7))))
        | ~ l1_pre_topc(X7)
        | ~ l1_pre_topc(X6) )
      & ( k1_relset_1(u1_struct_0(X6),u1_struct_0(X7),X8) != k2_struct_0(X6)
        | k2_relset_1(u1_struct_0(X6),u1_struct_0(X7),X8) != k2_struct_0(X7)
        | ~ v2_funct_1(X8)
        | ~ v5_pre_topc(X8,X6,X7)
        | ~ v5_pre_topc(k2_tops_2(u1_struct_0(X6),u1_struct_0(X7),X8),X7,X6)
        | v3_tops_2(X8,X6,X7)
        | ~ v1_funct_1(X8)
        | ~ v1_funct_2(X8,u1_struct_0(X6),u1_struct_0(X7))
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),u1_struct_0(X7))))
        | ~ l1_pre_topc(X7)
        | ~ l1_pre_topc(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_tops_2])])])])).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & v2_pre_topc(X2)
              & l1_pre_topc(X2) )
           => ! [X3] :
                ( ( v1_funct_1(X3)
                  & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
               => ! [X4] :
                    ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
                   => ( ( v3_tops_2(X3,X1,X2)
                        & v2_connsp_1(X4,X2) )
                     => v2_connsp_1(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4),X1) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t76_tops_2])).

cnf(c_0_14,plain,
    ( v2_connsp_1(k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),k2_tops_2(u1_struct_0(X2),u1_struct_0(X1),X3),X4),X2)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_connsp_1(X4,X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v5_pre_topc(k2_tops_2(u1_struct_0(X2),u1_struct_0(X1),X3),X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
    | ~ v1_funct_1(X3)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_8,c_0_9]),c_0_10]),c_0_11])).

cnf(c_0_15,plain,
    ( v5_pre_topc(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3),X2,X1)
    | ~ v3_tops_2(X3,X1,X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_16,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & ~ v2_struct_0(esk2_0)
    & v2_pre_topc(esk2_0)
    & l1_pre_topc(esk2_0)
    & v1_funct_1(esk3_0)
    & v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0))
    & m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))
    & m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
    & v3_tops_2(esk3_0,esk1_0,esk2_0)
    & v2_connsp_1(esk4_0,esk2_0)
    & ~ v2_connsp_1(k8_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,esk4_0),esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])).

cnf(c_0_17,plain,
    ( v2_connsp_1(k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),k2_tops_2(u1_struct_0(X2),u1_struct_0(X1),X3),X4),X2)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v2_connsp_1(X4,X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v3_tops_2(X3,X2,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
    | ~ v1_funct_1(X3)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_18,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_19,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( v3_tops_2(esk3_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_26,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_27,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_28,plain,(
    ! [X12,X13,X14,X15] :
      ( ~ l1_struct_0(X12)
      | ~ l1_struct_0(X13)
      | ~ v1_funct_1(X14)
      | ~ v1_funct_2(X14,u1_struct_0(X12),u1_struct_0(X13))
      | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X12),u1_struct_0(X13))))
      | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
      | k2_relset_1(u1_struct_0(X12),u1_struct_0(X13),X14) != k2_struct_0(X13)
      | ~ v2_funct_1(X14)
      | k8_relset_1(u1_struct_0(X12),u1_struct_0(X13),X14,X15) = k7_relset_1(u1_struct_0(X13),u1_struct_0(X12),k2_tops_2(u1_struct_0(X12),u1_struct_0(X13),X14),X15) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t68_tops_2])])])).

cnf(c_0_29,plain,
    ( v2_funct_1(X1)
    | ~ v3_tops_2(X1,X2,X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_30,negated_conjecture,
    ( v2_connsp_1(k7_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0),X1),esk1_0)
    | ~ v2_connsp_1(X1,esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19]),c_0_20]),c_0_21]),c_0_22]),c_0_23]),c_0_24]),c_0_25])]),c_0_26]),c_0_27])).

cnf(c_0_31,plain,
    ( k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4) = k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3),X4)
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) != k2_struct_0(X2)
    | ~ v2_funct_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_32,negated_conjecture,
    ( v2_funct_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_18]),c_0_21]),c_0_22]),c_0_23]),c_0_25]),c_0_24])])).

cnf(c_0_33,negated_conjecture,
    ( ~ v2_connsp_1(k8_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,esk4_0),esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_34,negated_conjecture,
    ( v2_connsp_1(k8_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,X1),esk1_0)
    | k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0) != k2_struct_0(esk2_0)
    | ~ v2_connsp_1(X1,esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ l1_struct_0(esk2_0)
    | ~ l1_struct_0(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32]),c_0_18]),c_0_22]),c_0_23])])).

cnf(c_0_35,negated_conjecture,
    ( v2_connsp_1(esk4_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_36,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_37,negated_conjecture,
    ( k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0) != k2_struct_0(esk2_0)
    | ~ l1_struct_0(esk2_0)
    | ~ l1_struct_0(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35]),c_0_36])])).

cnf(c_0_38,plain,
    ( k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) = k2_struct_0(X2)
    | ~ v3_tops_2(X3,X1,X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_39,plain,(
    ! [X5] :
      ( ~ l1_pre_topc(X5)
      | l1_struct_0(X5) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_40,negated_conjecture,
    ( ~ l1_struct_0(esk2_0)
    | ~ l1_struct_0(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_21]),c_0_18]),c_0_22]),c_0_23]),c_0_25]),c_0_24])])).

cnf(c_0_41,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_42,negated_conjecture,
    ( ~ l1_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_24])])).

cnf(c_0_43,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_41]),c_0_25])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:16:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_AE_CS_SP_PS_S0V
% 0.13/0.37  # and selection function PSelectComplexExceptRRHorn.
% 0.13/0.37  #
% 0.13/0.37  # Preprocessing time       : 0.028 s
% 0.13/0.37  # Presaturation interreduction done
% 0.13/0.37  
% 0.13/0.37  # Proof found!
% 0.13/0.37  # SZS status Theorem
% 0.13/0.37  # SZS output start CNFRefutation
% 0.13/0.37  fof(t75_tops_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>((v5_pre_topc(X3,X1,X2)&v2_connsp_1(X4,X1))=>v2_connsp_1(k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4),X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_tops_2)).
% 0.13/0.37  fof(dt_k2_tops_2, axiom, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((v1_funct_1(k2_tops_2(X1,X2,X3))&v1_funct_2(k2_tops_2(X1,X2,X3),X2,X1))&m1_subset_1(k2_tops_2(X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_2)).
% 0.13/0.37  fof(d5_tops_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(l1_pre_topc(X2)=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>(v3_tops_2(X3,X1,X2)<=>((((k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)=k2_struct_0(X1)&k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)=k2_struct_0(X2))&v2_funct_1(X3))&v5_pre_topc(X3,X1,X2))&v5_pre_topc(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3),X2,X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tops_2)).
% 0.13/0.37  fof(t76_tops_2, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))=>((v3_tops_2(X3,X1,X2)&v2_connsp_1(X4,X2))=>v2_connsp_1(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4),X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_tops_2)).
% 0.13/0.37  fof(t68_tops_2, axiom, ![X1]:(l1_struct_0(X1)=>![X2]:(l1_struct_0(X2)=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))=>((k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)=k2_struct_0(X2)&v2_funct_1(X3))=>k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4)=k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3),X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t68_tops_2)).
% 0.13/0.37  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.13/0.37  fof(c_0_6, plain, ![X16, X17, X18, X19]:(v2_struct_0(X16)|~v2_pre_topc(X16)|~l1_pre_topc(X16)|(v2_struct_0(X17)|~v2_pre_topc(X17)|~l1_pre_topc(X17)|(~v1_funct_1(X18)|~v1_funct_2(X18,u1_struct_0(X16),u1_struct_0(X17))|~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X16),u1_struct_0(X17))))|(~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X16)))|(~v5_pre_topc(X18,X16,X17)|~v2_connsp_1(X19,X16)|v2_connsp_1(k7_relset_1(u1_struct_0(X16),u1_struct_0(X17),X18,X19),X17)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t75_tops_2])])])])).
% 0.13/0.37  fof(c_0_7, plain, ![X9, X10, X11]:(((v1_funct_1(k2_tops_2(X9,X10,X11))|(~v1_funct_1(X11)|~v1_funct_2(X11,X9,X10)|~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))))&(v1_funct_2(k2_tops_2(X9,X10,X11),X10,X9)|(~v1_funct_1(X11)|~v1_funct_2(X11,X9,X10)|~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X9,X10))))))&(m1_subset_1(k2_tops_2(X9,X10,X11),k1_zfmisc_1(k2_zfmisc_1(X10,X9)))|(~v1_funct_1(X11)|~v1_funct_2(X11,X9,X10)|~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_tops_2])])])).
% 0.13/0.37  cnf(c_0_8, plain, (v2_struct_0(X1)|v2_struct_0(X2)|v2_connsp_1(k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4),X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))|~v5_pre_topc(X3,X1,X2)|~v2_connsp_1(X4,X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.37  cnf(c_0_9, plain, (m1_subset_1(k2_tops_2(X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))|~v1_funct_1(X3)|~v1_funct_2(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.37  cnf(c_0_10, plain, (v1_funct_1(k2_tops_2(X1,X2,X3))|~v1_funct_1(X3)|~v1_funct_2(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.37  cnf(c_0_11, plain, (v1_funct_2(k2_tops_2(X1,X2,X3),X2,X1)|~v1_funct_1(X3)|~v1_funct_2(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.37  fof(c_0_12, plain, ![X6, X7, X8]:((((((k1_relset_1(u1_struct_0(X6),u1_struct_0(X7),X8)=k2_struct_0(X6)|~v3_tops_2(X8,X6,X7)|(~v1_funct_1(X8)|~v1_funct_2(X8,u1_struct_0(X6),u1_struct_0(X7))|~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),u1_struct_0(X7)))))|~l1_pre_topc(X7)|~l1_pre_topc(X6))&(k2_relset_1(u1_struct_0(X6),u1_struct_0(X7),X8)=k2_struct_0(X7)|~v3_tops_2(X8,X6,X7)|(~v1_funct_1(X8)|~v1_funct_2(X8,u1_struct_0(X6),u1_struct_0(X7))|~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),u1_struct_0(X7)))))|~l1_pre_topc(X7)|~l1_pre_topc(X6)))&(v2_funct_1(X8)|~v3_tops_2(X8,X6,X7)|(~v1_funct_1(X8)|~v1_funct_2(X8,u1_struct_0(X6),u1_struct_0(X7))|~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),u1_struct_0(X7)))))|~l1_pre_topc(X7)|~l1_pre_topc(X6)))&(v5_pre_topc(X8,X6,X7)|~v3_tops_2(X8,X6,X7)|(~v1_funct_1(X8)|~v1_funct_2(X8,u1_struct_0(X6),u1_struct_0(X7))|~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),u1_struct_0(X7)))))|~l1_pre_topc(X7)|~l1_pre_topc(X6)))&(v5_pre_topc(k2_tops_2(u1_struct_0(X6),u1_struct_0(X7),X8),X7,X6)|~v3_tops_2(X8,X6,X7)|(~v1_funct_1(X8)|~v1_funct_2(X8,u1_struct_0(X6),u1_struct_0(X7))|~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),u1_struct_0(X7)))))|~l1_pre_topc(X7)|~l1_pre_topc(X6)))&(k1_relset_1(u1_struct_0(X6),u1_struct_0(X7),X8)!=k2_struct_0(X6)|k2_relset_1(u1_struct_0(X6),u1_struct_0(X7),X8)!=k2_struct_0(X7)|~v2_funct_1(X8)|~v5_pre_topc(X8,X6,X7)|~v5_pre_topc(k2_tops_2(u1_struct_0(X6),u1_struct_0(X7),X8),X7,X6)|v3_tops_2(X8,X6,X7)|(~v1_funct_1(X8)|~v1_funct_2(X8,u1_struct_0(X6),u1_struct_0(X7))|~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),u1_struct_0(X7)))))|~l1_pre_topc(X7)|~l1_pre_topc(X6))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_tops_2])])])])).
% 0.13/0.37  fof(c_0_13, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))=>((v3_tops_2(X3,X1,X2)&v2_connsp_1(X4,X2))=>v2_connsp_1(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4),X1))))))), inference(assume_negation,[status(cth)],[t76_tops_2])).
% 0.13/0.37  cnf(c_0_14, plain, (v2_connsp_1(k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),k2_tops_2(u1_struct_0(X2),u1_struct_0(X1),X3),X4),X2)|v2_struct_0(X1)|v2_struct_0(X2)|~v2_connsp_1(X4,X1)|~v2_pre_topc(X2)|~v2_pre_topc(X1)|~v5_pre_topc(k2_tops_2(u1_struct_0(X2),u1_struct_0(X1),X3),X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))|~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))|~v1_funct_1(X3)|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_8, c_0_9]), c_0_10]), c_0_11])).
% 0.13/0.37  cnf(c_0_15, plain, (v5_pre_topc(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3),X2,X1)|~v3_tops_2(X3,X1,X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.37  fof(c_0_16, negated_conjecture, (((~v2_struct_0(esk1_0)&v2_pre_topc(esk1_0))&l1_pre_topc(esk1_0))&(((~v2_struct_0(esk2_0)&v2_pre_topc(esk2_0))&l1_pre_topc(esk2_0))&(((v1_funct_1(esk3_0)&v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0)))&m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))))&(m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0)))&((v3_tops_2(esk3_0,esk1_0,esk2_0)&v2_connsp_1(esk4_0,esk2_0))&~v2_connsp_1(k8_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,esk4_0),esk1_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])).
% 0.13/0.37  cnf(c_0_17, plain, (v2_connsp_1(k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),k2_tops_2(u1_struct_0(X2),u1_struct_0(X1),X3),X4),X2)|v2_struct_0(X2)|v2_struct_0(X1)|~v2_connsp_1(X4,X1)|~v2_pre_topc(X2)|~v2_pre_topc(X1)|~v3_tops_2(X3,X2,X1)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))|~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))|~v1_funct_1(X3)|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.13/0.37  cnf(c_0_18, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.37  cnf(c_0_19, negated_conjecture, (v2_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.37  cnf(c_0_20, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.37  cnf(c_0_21, negated_conjecture, (v3_tops_2(esk3_0,esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.37  cnf(c_0_22, negated_conjecture, (v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.37  cnf(c_0_23, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.37  cnf(c_0_24, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.37  cnf(c_0_25, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.37  cnf(c_0_26, negated_conjecture, (~v2_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.37  cnf(c_0_27, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.37  fof(c_0_28, plain, ![X12, X13, X14, X15]:(~l1_struct_0(X12)|(~l1_struct_0(X13)|(~v1_funct_1(X14)|~v1_funct_2(X14,u1_struct_0(X12),u1_struct_0(X13))|~m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X12),u1_struct_0(X13))))|(~m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))|(k2_relset_1(u1_struct_0(X12),u1_struct_0(X13),X14)!=k2_struct_0(X13)|~v2_funct_1(X14)|k8_relset_1(u1_struct_0(X12),u1_struct_0(X13),X14,X15)=k7_relset_1(u1_struct_0(X13),u1_struct_0(X12),k2_tops_2(u1_struct_0(X12),u1_struct_0(X13),X14),X15)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t68_tops_2])])])).
% 0.13/0.37  cnf(c_0_29, plain, (v2_funct_1(X1)|~v3_tops_2(X1,X2,X3)|~v1_funct_1(X1)|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))|~l1_pre_topc(X3)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.37  cnf(c_0_30, negated_conjecture, (v2_connsp_1(k7_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0),X1),esk1_0)|~v2_connsp_1(X1,esk2_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_19]), c_0_20]), c_0_21]), c_0_22]), c_0_23]), c_0_24]), c_0_25])]), c_0_26]), c_0_27])).
% 0.13/0.37  cnf(c_0_31, plain, (k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4)=k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3),X4)|~l1_struct_0(X1)|~l1_struct_0(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))|k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)!=k2_struct_0(X2)|~v2_funct_1(X3)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.13/0.37  cnf(c_0_32, negated_conjecture, (v2_funct_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_18]), c_0_21]), c_0_22]), c_0_23]), c_0_25]), c_0_24])])).
% 0.13/0.37  cnf(c_0_33, negated_conjecture, (~v2_connsp_1(k8_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,esk4_0),esk1_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.37  cnf(c_0_34, negated_conjecture, (v2_connsp_1(k8_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,X1),esk1_0)|k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0)!=k2_struct_0(esk2_0)|~v2_connsp_1(X1,esk2_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))|~l1_struct_0(esk2_0)|~l1_struct_0(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32]), c_0_18]), c_0_22]), c_0_23])])).
% 0.13/0.37  cnf(c_0_35, negated_conjecture, (v2_connsp_1(esk4_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.37  cnf(c_0_36, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.37  cnf(c_0_37, negated_conjecture, (k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0)!=k2_struct_0(esk2_0)|~l1_struct_0(esk2_0)|~l1_struct_0(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35]), c_0_36])])).
% 0.13/0.37  cnf(c_0_38, plain, (k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)=k2_struct_0(X2)|~v3_tops_2(X3,X1,X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.37  fof(c_0_39, plain, ![X5]:(~l1_pre_topc(X5)|l1_struct_0(X5)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.13/0.37  cnf(c_0_40, negated_conjecture, (~l1_struct_0(esk2_0)|~l1_struct_0(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_21]), c_0_18]), c_0_22]), c_0_23]), c_0_25]), c_0_24])])).
% 0.13/0.37  cnf(c_0_41, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.13/0.37  cnf(c_0_42, negated_conjecture, (~l1_struct_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_24])])).
% 0.13/0.37  cnf(c_0_43, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_41]), c_0_25])]), ['proof']).
% 0.13/0.37  # SZS output end CNFRefutation
% 0.13/0.37  # Proof object total steps             : 44
% 0.13/0.37  # Proof object clause steps            : 31
% 0.13/0.37  # Proof object formula steps           : 13
% 0.13/0.37  # Proof object conjectures             : 23
% 0.13/0.37  # Proof object clause conjectures      : 20
% 0.13/0.37  # Proof object formula conjectures     : 3
% 0.13/0.37  # Proof object initial clauses used    : 22
% 0.13/0.37  # Proof object initial formulas used   : 6
% 0.13/0.37  # Proof object generating inferences   : 9
% 0.13/0.37  # Proof object simplifying inferences  : 37
% 0.13/0.37  # Training examples: 0 positive, 0 negative
% 0.13/0.37  # Parsed axioms                        : 6
% 0.13/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.37  # Initial clauses                      : 25
% 0.13/0.37  # Removed in clause preprocessing      : 0
% 0.13/0.37  # Initial clauses in saturation        : 25
% 0.13/0.37  # Processed clauses                    : 65
% 0.13/0.37  # ...of these trivial                  : 0
% 0.13/0.37  # ...subsumed                          : 0
% 0.13/0.37  # ...remaining for further processing  : 65
% 0.13/0.37  # Other redundant clauses eliminated   : 0
% 0.13/0.37  # Clauses deleted for lack of memory   : 0
% 0.13/0.37  # Backward-subsumed                    : 2
% 0.13/0.37  # Backward-rewritten                   : 0
% 0.13/0.37  # Generated clauses                    : 24
% 0.13/0.37  # ...of the previous two non-trivial   : 22
% 0.13/0.37  # Contextual simplify-reflections      : 13
% 0.13/0.37  # Paramodulations                      : 24
% 0.13/0.37  # Factorizations                       : 0
% 0.13/0.37  # Equation resolutions                 : 0
% 0.13/0.37  # Propositional unsat checks           : 0
% 0.13/0.37  #    Propositional check models        : 0
% 0.13/0.37  #    Propositional check unsatisfiable : 0
% 0.13/0.37  #    Propositional clauses             : 0
% 0.13/0.37  #    Propositional clauses after purity: 0
% 0.13/0.37  #    Propositional unsat core size     : 0
% 0.13/0.37  #    Propositional preprocessing time  : 0.000
% 0.13/0.37  #    Propositional encoding time       : 0.000
% 0.13/0.37  #    Propositional solver time         : 0.000
% 0.13/0.37  #    Success case prop preproc time    : 0.000
% 0.13/0.37  #    Success case prop encoding time   : 0.000
% 0.13/0.37  #    Success case prop solver time     : 0.000
% 0.13/0.37  # Current number of processed clauses  : 38
% 0.13/0.37  #    Positive orientable unit clauses  : 12
% 0.13/0.37  #    Positive unorientable unit clauses: 0
% 0.13/0.37  #    Negative unit clauses             : 4
% 0.13/0.37  #    Non-unit-clauses                  : 22
% 0.13/0.37  # Current number of unprocessed clauses: 7
% 0.13/0.37  # ...number of literals in the above   : 95
% 0.13/0.37  # Current number of archived formulas  : 0
% 0.13/0.37  # Current number of archived clauses   : 27
% 0.13/0.37  # Clause-clause subsumption calls (NU) : 948
% 0.13/0.37  # Rec. Clause-clause subsumption calls : 36
% 0.13/0.37  # Non-unit clause-clause subsumptions  : 15
% 0.13/0.37  # Unit Clause-clause subsumption calls : 21
% 0.13/0.37  # Rewrite failures with RHS unbound    : 0
% 0.13/0.37  # BW rewrite match attempts            : 0
% 0.13/0.37  # BW rewrite match successes           : 0
% 0.13/0.37  # Condensation attempts                : 0
% 0.13/0.37  # Condensation successes               : 0
% 0.13/0.37  # Termbank termtop insertions          : 4766
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.034 s
% 0.13/0.38  # System time              : 0.003 s
% 0.13/0.38  # Total time               : 0.037 s
% 0.13/0.38  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
