%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:14:05 EST 2020

% Result     : Theorem 0.16s
% Output     : CNFRefutation 0.16s
% Verified   : 
% Statistics : Number of formulae       :   75 (1010 expanded)
%              Number of clauses        :   54 ( 310 expanded)
%              Number of leaves         :   10 ( 256 expanded)
%              Depth                    :   15
%              Number of atoms          :  437 (7488 expanded)
%              Number of equality atoms :   73 ( 398 expanded)
%              Maximal formula depth    :   20 (   6 average)
%              Maximal clause size      :   46 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(d4_tops_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( ( k2_relset_1(X1,X2,X3) = X2
          & v2_funct_1(X3) )
       => k2_tops_2(X1,X2,X3) = k2_funct_1(X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).

fof(t65_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => k2_funct_1(k2_funct_1(X1)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).

fof(t31_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( ( v2_funct_1(X3)
          & k2_relset_1(X1,X2,X3) = X2 )
       => ( v1_funct_1(k2_funct_1(X3))
          & v1_funct_2(k2_funct_1(X3),X2,X1)
          & m1_subset_1(k2_funct_1(X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(d3_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => k2_struct_0(X1) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(t70_tops_2,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_tops_2)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_tops_2)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_tops_2)).

fof(c_0_10,plain,(
    ! [X16,X17,X18] :
      ( ( k1_relset_1(u1_struct_0(X16),u1_struct_0(X17),X18) = k2_struct_0(X16)
        | ~ v3_tops_2(X18,X16,X17)
        | ~ v1_funct_1(X18)
        | ~ v1_funct_2(X18,u1_struct_0(X16),u1_struct_0(X17))
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X16),u1_struct_0(X17))))
        | ~ l1_pre_topc(X17)
        | ~ l1_pre_topc(X16) )
      & ( k2_relset_1(u1_struct_0(X16),u1_struct_0(X17),X18) = k2_struct_0(X17)
        | ~ v3_tops_2(X18,X16,X17)
        | ~ v1_funct_1(X18)
        | ~ v1_funct_2(X18,u1_struct_0(X16),u1_struct_0(X17))
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X16),u1_struct_0(X17))))
        | ~ l1_pre_topc(X17)
        | ~ l1_pre_topc(X16) )
      & ( v2_funct_1(X18)
        | ~ v3_tops_2(X18,X16,X17)
        | ~ v1_funct_1(X18)
        | ~ v1_funct_2(X18,u1_struct_0(X16),u1_struct_0(X17))
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X16),u1_struct_0(X17))))
        | ~ l1_pre_topc(X17)
        | ~ l1_pre_topc(X16) )
      & ( v5_pre_topc(X18,X16,X17)
        | ~ v3_tops_2(X18,X16,X17)
        | ~ v1_funct_1(X18)
        | ~ v1_funct_2(X18,u1_struct_0(X16),u1_struct_0(X17))
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X16),u1_struct_0(X17))))
        | ~ l1_pre_topc(X17)
        | ~ l1_pre_topc(X16) )
      & ( v5_pre_topc(k2_tops_2(u1_struct_0(X16),u1_struct_0(X17),X18),X17,X16)
        | ~ v3_tops_2(X18,X16,X17)
        | ~ v1_funct_1(X18)
        | ~ v1_funct_2(X18,u1_struct_0(X16),u1_struct_0(X17))
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X16),u1_struct_0(X17))))
        | ~ l1_pre_topc(X17)
        | ~ l1_pre_topc(X16) )
      & ( k1_relset_1(u1_struct_0(X16),u1_struct_0(X17),X18) != k2_struct_0(X16)
        | k2_relset_1(u1_struct_0(X16),u1_struct_0(X17),X18) != k2_struct_0(X17)
        | ~ v2_funct_1(X18)
        | ~ v5_pre_topc(X18,X16,X17)
        | ~ v5_pre_topc(k2_tops_2(u1_struct_0(X16),u1_struct_0(X17),X18),X17,X16)
        | v3_tops_2(X18,X16,X17)
        | ~ v1_funct_1(X18)
        | ~ v1_funct_2(X18,u1_struct_0(X16),u1_struct_0(X17))
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X16),u1_struct_0(X17))))
        | ~ l1_pre_topc(X17)
        | ~ l1_pre_topc(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_tops_2])])])])).

fof(c_0_11,plain,(
    ! [X13,X14,X15] :
      ( ~ v1_funct_1(X15)
      | ~ v1_funct_2(X15,X13,X14)
      | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14)))
      | k2_relset_1(X13,X14,X15) != X14
      | ~ v2_funct_1(X15)
      | k2_tops_2(X13,X14,X15) = k2_funct_1(X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tops_2])])).

cnf(c_0_12,plain,
    ( v5_pre_topc(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3),X2,X1)
    | ~ v3_tops_2(X3,X1,X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_13,plain,
    ( k2_tops_2(X2,X3,X1) = k2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | k2_relset_1(X2,X3,X1) != X3
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_14,plain,
    ( v2_funct_1(X1)
    | ~ v3_tops_2(X1,X2,X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_15,plain,(
    ! [X4] :
      ( ~ v1_relat_1(X4)
      | ~ v1_funct_1(X4)
      | ~ v2_funct_1(X4)
      | k2_funct_1(k2_funct_1(X4)) = X4 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_funct_1])])).

cnf(c_0_16,plain,
    ( v5_pre_topc(k2_funct_1(X1),X2,X3)
    | k2_relset_1(u1_struct_0(X3),u1_struct_0(X2),X1) != u1_struct_0(X2)
    | ~ v3_tops_2(X1,X3,X2)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | ~ v1_funct_2(X1,u1_struct_0(X3),u1_struct_0(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ v1_funct_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_14])).

cnf(c_0_17,plain,
    ( k2_funct_1(k2_funct_1(X1)) = X1
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_18,plain,(
    ! [X8,X9,X10] :
      ( ( v1_funct_1(k2_funct_1(X10))
        | ~ v2_funct_1(X10)
        | k2_relset_1(X8,X9,X10) != X9
        | ~ v1_funct_1(X10)
        | ~ v1_funct_2(X10,X8,X9)
        | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X8,X9))) )
      & ( v1_funct_2(k2_funct_1(X10),X9,X8)
        | ~ v2_funct_1(X10)
        | k2_relset_1(X8,X9,X10) != X9
        | ~ v1_funct_1(X10)
        | ~ v1_funct_2(X10,X8,X9)
        | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X8,X9))) )
      & ( m1_subset_1(k2_funct_1(X10),k1_zfmisc_1(k2_zfmisc_1(X9,X8)))
        | ~ v2_funct_1(X10)
        | k2_relset_1(X8,X9,X10) != X9
        | ~ v1_funct_1(X10)
        | ~ v1_funct_2(X10,X8,X9)
        | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X8,X9))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_funct_2])])])).

fof(c_0_19,plain,(
    ! [X5,X6,X7] :
      ( ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
      | v1_relat_1(X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_20,plain,(
    ! [X11] :
      ( ~ l1_struct_0(X11)
      | k2_struct_0(X11) = u1_struct_0(X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

fof(c_0_21,plain,(
    ! [X12] :
      ( ~ l1_pre_topc(X12)
      | l1_struct_0(X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

fof(c_0_22,negated_conjecture,(
    ~ ! [X1] :
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
    inference(assume_negation,[status(cth)],[t70_tops_2])).

cnf(c_0_23,plain,
    ( v5_pre_topc(X1,X2,X3)
    | k2_relset_1(u1_struct_0(X3),u1_struct_0(X2),k2_funct_1(X1)) != u1_struct_0(X2)
    | ~ v3_tops_2(k2_funct_1(X1),X3,X2)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | ~ v1_funct_2(k2_funct_1(X1),u1_struct_0(X3),u1_struct_0(X2))
    | ~ m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_24,plain,
    ( m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v2_funct_1(X1)
    | k2_relset_1(X3,X2,X1) != X2
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( v1_funct_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | k2_relset_1(X2,X3,X1) != X3
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,plain,
    ( v1_funct_2(k2_funct_1(X1),X2,X3)
    | ~ v2_funct_1(X1)
    | k2_relset_1(X3,X2,X1) != X2
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_28,plain,
    ( k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) = k2_struct_0(X2)
    | ~ v3_tops_2(X3,X1,X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_29,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_30,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_31,negated_conjecture,
    ( l1_pre_topc(esk1_0)
    & ~ v2_struct_0(esk2_0)
    & l1_pre_topc(esk2_0)
    & v1_funct_1(esk3_0)
    & v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0))
    & m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))
    & v3_tops_2(esk3_0,esk1_0,esk2_0)
    & ~ v3_tops_2(k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0),esk2_0,esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_22])])])])).

cnf(c_0_32,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_33,plain,
    ( v5_pre_topc(X1,X2,X3)
    | k2_relset_1(u1_struct_0(X3),u1_struct_0(X2),k2_funct_1(X1)) != u1_struct_0(X2)
    | k2_relset_1(u1_struct_0(X2),u1_struct_0(X3),X1) != u1_struct_0(X3)
    | ~ v3_tops_2(k2_funct_1(X1),X3,X2)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25]),c_0_26]),c_0_27])).

cnf(c_0_34,plain,
    ( k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),k2_funct_1(X3)) = k2_struct_0(X2)
    | k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),X3) != u1_struct_0(X1)
    | ~ v3_tops_2(k2_funct_1(X3),X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ v2_funct_1(X3)
    | ~ v1_funct_1(X3) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_24]),c_0_26]),c_0_27])).

cnf(c_0_35,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

fof(c_0_36,plain,(
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

cnf(c_0_37,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_38,negated_conjecture,
    ( v3_tops_2(esk3_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_39,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_40,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_41,negated_conjecture,
    ( v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_42,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_43,plain,(
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

cnf(c_0_44,plain,
    ( v3_tops_2(X1,X2,X3)
    | k2_relset_1(u1_struct_0(X2),u1_struct_0(X3),X1) != k2_struct_0(X3)
    | k1_relset_1(u1_struct_0(X2),u1_struct_0(X3),X1) != k2_struct_0(X2)
    | k2_relset_1(u1_struct_0(X2),u1_struct_0(X3),X1) != u1_struct_0(X3)
    | ~ v5_pre_topc(k2_funct_1(X1),X3,X2)
    | ~ v5_pre_topc(X1,X2,X3)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(spm,[status(thm)],[c_0_32,c_0_13])).

cnf(c_0_45,plain,
    ( v5_pre_topc(X1,X2,X3)
    | ~ v3_tops_2(X1,X2,X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_46,plain,
    ( v5_pre_topc(X1,X2,X3)
    | k2_relset_1(u1_struct_0(X2),u1_struct_0(X3),X1) != u1_struct_0(X3)
    | ~ v3_tops_2(k2_funct_1(X1),X3,X2)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35])).

cnf(c_0_47,plain,
    ( k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),k2_tops_2(u1_struct_0(X2),u1_struct_0(X1),X3)) = k2_struct_0(X1)
    | v2_struct_0(X1)
    | k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),X3) != k2_struct_0(X1)
    | ~ v2_funct_1(X3)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_48,negated_conjecture,
    ( k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0) = k2_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_37]),c_0_38]),c_0_39]),c_0_40]),c_0_41]),c_0_42])])).

cnf(c_0_49,negated_conjecture,
    ( v2_funct_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_37]),c_0_38]),c_0_39]),c_0_40]),c_0_41]),c_0_42])])).

cnf(c_0_50,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_51,plain,
    ( v2_funct_1(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) != k2_struct_0(X2)
    | ~ v2_funct_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_52,plain,
    ( k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),k2_tops_2(u1_struct_0(X2),u1_struct_0(X1),X3)) = k2_struct_0(X2)
    | v2_struct_0(X1)
    | k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),X3) != k2_struct_0(X1)
    | ~ v2_funct_1(X3)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_53,plain,
    ( v3_tops_2(X1,X2,X3)
    | k2_relset_1(u1_struct_0(X2),u1_struct_0(X3),X1) != k2_struct_0(X3)
    | k1_relset_1(u1_struct_0(X2),u1_struct_0(X3),X1) != k2_struct_0(X2)
    | k2_relset_1(u1_struct_0(X2),u1_struct_0(X3),X1) != u1_struct_0(X3)
    | ~ v3_tops_2(k2_funct_1(X1),X3,X2)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_26]),c_0_24]),c_0_27]),c_0_46])).

cnf(c_0_54,negated_conjecture,
    ( k1_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0)) = k2_struct_0(esk2_0)
    | ~ l1_struct_0(esk1_0)
    | ~ l1_struct_0(esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_37]),c_0_48]),c_0_41]),c_0_49]),c_0_42])]),c_0_50])).

cnf(c_0_55,plain,
    ( v2_funct_1(k2_funct_1(X1))
    | k2_relset_1(u1_struct_0(X2),u1_struct_0(X3),X1) != k2_struct_0(X3)
    | k2_relset_1(u1_struct_0(X2),u1_struct_0(X3),X1) != u1_struct_0(X3)
    | ~ l1_struct_0(X3)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(spm,[status(thm)],[c_0_51,c_0_13])).

cnf(c_0_56,negated_conjecture,
    ( k2_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0)) = k2_struct_0(esk1_0)
    | ~ l1_struct_0(esk1_0)
    | ~ l1_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_37]),c_0_41]),c_0_49]),c_0_42])]),c_0_50]),c_0_48])])).

cnf(c_0_57,negated_conjecture,
    ( ~ v3_tops_2(k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0),esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_58,plain,
    ( v3_tops_2(k2_funct_1(X1),X2,X3)
    | k2_relset_1(u1_struct_0(X2),u1_struct_0(X3),k2_funct_1(X1)) != k2_struct_0(X3)
    | k1_relset_1(u1_struct_0(X2),u1_struct_0(X3),k2_funct_1(X1)) != k2_struct_0(X2)
    | k2_relset_1(u1_struct_0(X2),u1_struct_0(X3),k2_funct_1(X1)) != u1_struct_0(X3)
    | ~ v3_tops_2(X1,X3,X2)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_2(k2_funct_1(X1),u1_struct_0(X2),u1_struct_0(X3))
    | ~ m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
    | ~ v2_funct_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_53,c_0_17])).

cnf(c_0_59,negated_conjecture,
    ( k1_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k2_funct_1(esk3_0)) = k2_struct_0(esk2_0)
    | ~ l1_struct_0(esk1_0)
    | ~ l1_struct_0(esk2_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_13]),c_0_48]),c_0_41]),c_0_37]),c_0_49]),c_0_42])]),c_0_29])).

cnf(c_0_60,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_37])).

cnf(c_0_61,negated_conjecture,
    ( v2_funct_1(k2_funct_1(esk3_0))
    | ~ l1_struct_0(esk2_0)
    | ~ l1_struct_0(esk1_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_37]),c_0_48]),c_0_48]),c_0_41]),c_0_49]),c_0_42])]),c_0_29])).

cnf(c_0_62,negated_conjecture,
    ( k2_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k2_funct_1(esk3_0)) = k2_struct_0(esk1_0)
    | ~ l1_struct_0(esk1_0)
    | ~ l1_struct_0(esk2_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_13]),c_0_48]),c_0_41]),c_0_37]),c_0_49]),c_0_42])]),c_0_29])).

cnf(c_0_63,negated_conjecture,
    ( v1_funct_1(k2_funct_1(esk3_0))
    | k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0) != u1_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_37]),c_0_41]),c_0_42])]),c_0_49])])).

cnf(c_0_64,negated_conjecture,
    ( k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0) != u1_struct_0(esk2_0)
    | ~ v3_tops_2(k2_funct_1(esk3_0),esk2_0,esk1_0)
    | ~ v2_funct_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_13]),c_0_41]),c_0_37]),c_0_42])])).

cnf(c_0_65,negated_conjecture,
    ( v3_tops_2(k2_funct_1(esk3_0),esk2_0,esk1_0)
    | k2_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k2_funct_1(esk3_0)) != u1_struct_0(esk1_0)
    | ~ l1_struct_0(esk1_0)
    | ~ l1_struct_0(esk2_0)
    | ~ v1_funct_2(k2_funct_1(esk3_0),u1_struct_0(esk2_0),u1_struct_0(esk1_0))
    | ~ m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0))))
    | ~ v1_funct_1(k2_funct_1(esk3_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_38]),c_0_40]),c_0_39]),c_0_49]),c_0_42]),c_0_60])]),c_0_61]),c_0_62])).

cnf(c_0_66,negated_conjecture,
    ( v1_funct_1(k2_funct_1(esk3_0))
    | k2_struct_0(esk2_0) != u1_struct_0(esk2_0) ),
    inference(rw,[status(thm)],[c_0_63,c_0_48])).

cnf(c_0_67,negated_conjecture,
    ( k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0) != u1_struct_0(esk2_0)
    | ~ v3_tops_2(k2_funct_1(esk3_0),esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_64,c_0_49])])).

cnf(c_0_68,negated_conjecture,
    ( v3_tops_2(k2_funct_1(esk3_0),esk2_0,esk1_0)
    | k2_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k2_funct_1(esk3_0)) != u1_struct_0(esk1_0)
    | ~ l1_struct_0(esk1_0)
    | ~ l1_struct_0(esk2_0)
    | ~ v1_funct_2(k2_funct_1(esk3_0),u1_struct_0(esk2_0),u1_struct_0(esk1_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_24]),c_0_48]),c_0_41]),c_0_37]),c_0_49]),c_0_42])]),c_0_66]),c_0_29])).

cnf(c_0_69,negated_conjecture,
    ( k2_struct_0(esk2_0) != u1_struct_0(esk2_0)
    | ~ v3_tops_2(k2_funct_1(esk3_0),esk2_0,esk1_0) ),
    inference(rw,[status(thm)],[c_0_67,c_0_48])).

cnf(c_0_70,negated_conjecture,
    ( v3_tops_2(k2_funct_1(esk3_0),esk2_0,esk1_0)
    | ~ l1_struct_0(esk1_0)
    | ~ l1_struct_0(esk2_0)
    | ~ v1_funct_2(k2_funct_1(esk3_0),u1_struct_0(esk2_0),u1_struct_0(esk1_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_62]),c_0_29])).

cnf(c_0_71,negated_conjecture,
    ( ~ l1_struct_0(esk1_0)
    | ~ l1_struct_0(esk2_0)
    | ~ v1_funct_2(k2_funct_1(esk3_0),u1_struct_0(esk2_0),u1_struct_0(esk1_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_29])).

cnf(c_0_72,negated_conjecture,
    ( ~ l1_struct_0(esk1_0)
    | ~ l1_struct_0(esk2_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_27]),c_0_48]),c_0_41]),c_0_37]),c_0_49]),c_0_42])]),c_0_29])).

cnf(c_0_73,negated_conjecture,
    ( ~ l1_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_30]),c_0_40])])).

cnf(c_0_74,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_30]),c_0_39])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.11  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.31  % Computer   : n023.cluster.edu
% 0.12/0.31  % Model      : x86_64 x86_64
% 0.12/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.31  % Memory     : 8042.1875MB
% 0.12/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.31  % CPULimit   : 60
% 0.12/0.31  % WCLimit    : 600
% 0.12/0.31  % DateTime   : Tue Dec  1 11:49:51 EST 2020
% 0.12/0.31  % CPUTime    : 
% 0.12/0.31  # Version: 2.5pre002
% 0.12/0.31  # No SInE strategy applied
% 0.12/0.31  # Trying AutoSched0 for 299 seconds
% 0.16/0.35  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.16/0.35  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.16/0.35  #
% 0.16/0.35  # Preprocessing time       : 0.024 s
% 0.16/0.35  # Presaturation interreduction done
% 0.16/0.35  
% 0.16/0.35  # Proof found!
% 0.16/0.35  # SZS status Theorem
% 0.16/0.35  # SZS output start CNFRefutation
% 0.16/0.35  fof(d5_tops_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(l1_pre_topc(X2)=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>(v3_tops_2(X3,X1,X2)<=>((((k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)=k2_struct_0(X1)&k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)=k2_struct_0(X2))&v2_funct_1(X3))&v5_pre_topc(X3,X1,X2))&v5_pre_topc(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3),X2,X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tops_2)).
% 0.16/0.35  fof(d4_tops_2, axiom, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((k2_relset_1(X1,X2,X3)=X2&v2_funct_1(X3))=>k2_tops_2(X1,X2,X3)=k2_funct_1(X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tops_2)).
% 0.16/0.35  fof(t65_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>k2_funct_1(k2_funct_1(X1))=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_1)).
% 0.16/0.35  fof(t31_funct_2, axiom, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((v2_funct_1(X3)&k2_relset_1(X1,X2,X3)=X2)=>((v1_funct_1(k2_funct_1(X3))&v1_funct_2(k2_funct_1(X3),X2,X1))&m1_subset_1(k2_funct_1(X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 0.16/0.35  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.16/0.35  fof(d3_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>k2_struct_0(X1)=u1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 0.16/0.35  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.16/0.35  fof(t70_tops_2, conjecture, ![X1]:(l1_pre_topc(X1)=>![X2]:((~(v2_struct_0(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>(v3_tops_2(X3,X1,X2)=>v3_tops_2(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3),X2,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_tops_2)).
% 0.16/0.35  fof(t62_tops_2, axiom, ![X1]:(l1_struct_0(X1)=>![X2]:((~(v2_struct_0(X2))&l1_struct_0(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>((k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)=k2_struct_0(X2)&v2_funct_1(X3))=>(k1_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3))=k2_struct_0(X2)&k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3))=k2_struct_0(X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_tops_2)).
% 0.16/0.35  fof(t63_tops_2, axiom, ![X1]:(l1_struct_0(X1)=>![X2]:(l1_struct_0(X2)=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>((k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)=k2_struct_0(X2)&v2_funct_1(X3))=>v2_funct_1(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_tops_2)).
% 0.16/0.35  fof(c_0_10, plain, ![X16, X17, X18]:((((((k1_relset_1(u1_struct_0(X16),u1_struct_0(X17),X18)=k2_struct_0(X16)|~v3_tops_2(X18,X16,X17)|(~v1_funct_1(X18)|~v1_funct_2(X18,u1_struct_0(X16),u1_struct_0(X17))|~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X16),u1_struct_0(X17)))))|~l1_pre_topc(X17)|~l1_pre_topc(X16))&(k2_relset_1(u1_struct_0(X16),u1_struct_0(X17),X18)=k2_struct_0(X17)|~v3_tops_2(X18,X16,X17)|(~v1_funct_1(X18)|~v1_funct_2(X18,u1_struct_0(X16),u1_struct_0(X17))|~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X16),u1_struct_0(X17)))))|~l1_pre_topc(X17)|~l1_pre_topc(X16)))&(v2_funct_1(X18)|~v3_tops_2(X18,X16,X17)|(~v1_funct_1(X18)|~v1_funct_2(X18,u1_struct_0(X16),u1_struct_0(X17))|~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X16),u1_struct_0(X17)))))|~l1_pre_topc(X17)|~l1_pre_topc(X16)))&(v5_pre_topc(X18,X16,X17)|~v3_tops_2(X18,X16,X17)|(~v1_funct_1(X18)|~v1_funct_2(X18,u1_struct_0(X16),u1_struct_0(X17))|~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X16),u1_struct_0(X17)))))|~l1_pre_topc(X17)|~l1_pre_topc(X16)))&(v5_pre_topc(k2_tops_2(u1_struct_0(X16),u1_struct_0(X17),X18),X17,X16)|~v3_tops_2(X18,X16,X17)|(~v1_funct_1(X18)|~v1_funct_2(X18,u1_struct_0(X16),u1_struct_0(X17))|~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X16),u1_struct_0(X17)))))|~l1_pre_topc(X17)|~l1_pre_topc(X16)))&(k1_relset_1(u1_struct_0(X16),u1_struct_0(X17),X18)!=k2_struct_0(X16)|k2_relset_1(u1_struct_0(X16),u1_struct_0(X17),X18)!=k2_struct_0(X17)|~v2_funct_1(X18)|~v5_pre_topc(X18,X16,X17)|~v5_pre_topc(k2_tops_2(u1_struct_0(X16),u1_struct_0(X17),X18),X17,X16)|v3_tops_2(X18,X16,X17)|(~v1_funct_1(X18)|~v1_funct_2(X18,u1_struct_0(X16),u1_struct_0(X17))|~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X16),u1_struct_0(X17)))))|~l1_pre_topc(X17)|~l1_pre_topc(X16))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_tops_2])])])])).
% 0.16/0.35  fof(c_0_11, plain, ![X13, X14, X15]:(~v1_funct_1(X15)|~v1_funct_2(X15,X13,X14)|~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14)))|(k2_relset_1(X13,X14,X15)!=X14|~v2_funct_1(X15)|k2_tops_2(X13,X14,X15)=k2_funct_1(X15))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tops_2])])).
% 0.16/0.35  cnf(c_0_12, plain, (v5_pre_topc(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3),X2,X1)|~v3_tops_2(X3,X1,X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.16/0.35  cnf(c_0_13, plain, (k2_tops_2(X2,X3,X1)=k2_funct_1(X1)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|k2_relset_1(X2,X3,X1)!=X3|~v2_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.16/0.35  cnf(c_0_14, plain, (v2_funct_1(X1)|~v3_tops_2(X1,X2,X3)|~v1_funct_1(X1)|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))|~l1_pre_topc(X3)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.16/0.35  fof(c_0_15, plain, ![X4]:(~v1_relat_1(X4)|~v1_funct_1(X4)|(~v2_funct_1(X4)|k2_funct_1(k2_funct_1(X4))=X4)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_funct_1])])).
% 0.16/0.35  cnf(c_0_16, plain, (v5_pre_topc(k2_funct_1(X1),X2,X3)|k2_relset_1(u1_struct_0(X3),u1_struct_0(X2),X1)!=u1_struct_0(X2)|~v3_tops_2(X1,X3,X2)|~l1_pre_topc(X2)|~l1_pre_topc(X3)|~v1_funct_2(X1,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~v1_funct_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_13]), c_0_14])).
% 0.16/0.35  cnf(c_0_17, plain, (k2_funct_1(k2_funct_1(X1))=X1|~v1_relat_1(X1)|~v1_funct_1(X1)|~v2_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.16/0.35  fof(c_0_18, plain, ![X8, X9, X10]:(((v1_funct_1(k2_funct_1(X10))|(~v2_funct_1(X10)|k2_relset_1(X8,X9,X10)!=X9)|(~v1_funct_1(X10)|~v1_funct_2(X10,X8,X9)|~m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X8,X9)))))&(v1_funct_2(k2_funct_1(X10),X9,X8)|(~v2_funct_1(X10)|k2_relset_1(X8,X9,X10)!=X9)|(~v1_funct_1(X10)|~v1_funct_2(X10,X8,X9)|~m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X8,X9))))))&(m1_subset_1(k2_funct_1(X10),k1_zfmisc_1(k2_zfmisc_1(X9,X8)))|(~v2_funct_1(X10)|k2_relset_1(X8,X9,X10)!=X9)|(~v1_funct_1(X10)|~v1_funct_2(X10,X8,X9)|~m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X8,X9)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_funct_2])])])).
% 0.16/0.35  fof(c_0_19, plain, ![X5, X6, X7]:(~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))|v1_relat_1(X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.16/0.35  fof(c_0_20, plain, ![X11]:(~l1_struct_0(X11)|k2_struct_0(X11)=u1_struct_0(X11)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).
% 0.16/0.35  fof(c_0_21, plain, ![X12]:(~l1_pre_topc(X12)|l1_struct_0(X12)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.16/0.35  fof(c_0_22, negated_conjecture, ~(![X1]:(l1_pre_topc(X1)=>![X2]:((~(v2_struct_0(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>(v3_tops_2(X3,X1,X2)=>v3_tops_2(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3),X2,X1)))))), inference(assume_negation,[status(cth)],[t70_tops_2])).
% 0.16/0.35  cnf(c_0_23, plain, (v5_pre_topc(X1,X2,X3)|k2_relset_1(u1_struct_0(X3),u1_struct_0(X2),k2_funct_1(X1))!=u1_struct_0(X2)|~v3_tops_2(k2_funct_1(X1),X3,X2)|~l1_pre_topc(X2)|~l1_pre_topc(X3)|~v1_funct_2(k2_funct_1(X1),u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.16/0.35  cnf(c_0_24, plain, (m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v2_funct_1(X1)|k2_relset_1(X3,X2,X1)!=X2|~v1_funct_1(X1)|~v1_funct_2(X1,X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.16/0.35  cnf(c_0_25, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.16/0.35  cnf(c_0_26, plain, (v1_funct_1(k2_funct_1(X1))|~v2_funct_1(X1)|k2_relset_1(X2,X3,X1)!=X3|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.16/0.35  cnf(c_0_27, plain, (v1_funct_2(k2_funct_1(X1),X2,X3)|~v2_funct_1(X1)|k2_relset_1(X3,X2,X1)!=X2|~v1_funct_1(X1)|~v1_funct_2(X1,X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.16/0.35  cnf(c_0_28, plain, (k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)=k2_struct_0(X2)|~v3_tops_2(X3,X1,X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.16/0.35  cnf(c_0_29, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.16/0.35  cnf(c_0_30, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.16/0.35  fof(c_0_31, negated_conjecture, (l1_pre_topc(esk1_0)&((~v2_struct_0(esk2_0)&l1_pre_topc(esk2_0))&(((v1_funct_1(esk3_0)&v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0)))&m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))))&(v3_tops_2(esk3_0,esk1_0,esk2_0)&~v3_tops_2(k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0),esk2_0,esk1_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_22])])])])).
% 0.16/0.35  cnf(c_0_32, plain, (v3_tops_2(X3,X1,X2)|k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)!=k2_struct_0(X1)|k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)!=k2_struct_0(X2)|~v2_funct_1(X3)|~v5_pre_topc(X3,X1,X2)|~v5_pre_topc(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3),X2,X1)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.16/0.35  cnf(c_0_33, plain, (v5_pre_topc(X1,X2,X3)|k2_relset_1(u1_struct_0(X3),u1_struct_0(X2),k2_funct_1(X1))!=u1_struct_0(X2)|k2_relset_1(u1_struct_0(X2),u1_struct_0(X3),X1)!=u1_struct_0(X3)|~v3_tops_2(k2_funct_1(X1),X3,X2)|~l1_pre_topc(X2)|~l1_pre_topc(X3)|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))|~v2_funct_1(X1)|~v1_funct_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_25]), c_0_26]), c_0_27])).
% 0.16/0.35  cnf(c_0_34, plain, (k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),k2_funct_1(X3))=k2_struct_0(X2)|k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),X3)!=u1_struct_0(X1)|~v3_tops_2(k2_funct_1(X3),X1,X2)|~l1_pre_topc(X2)|~l1_pre_topc(X1)|~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))|~v2_funct_1(X3)|~v1_funct_1(X3)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_24]), c_0_26]), c_0_27])).
% 0.16/0.35  cnf(c_0_35, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.16/0.35  fof(c_0_36, plain, ![X19, X20, X21]:((k1_relset_1(u1_struct_0(X20),u1_struct_0(X19),k2_tops_2(u1_struct_0(X19),u1_struct_0(X20),X21))=k2_struct_0(X20)|(k2_relset_1(u1_struct_0(X19),u1_struct_0(X20),X21)!=k2_struct_0(X20)|~v2_funct_1(X21))|(~v1_funct_1(X21)|~v1_funct_2(X21,u1_struct_0(X19),u1_struct_0(X20))|~m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X19),u1_struct_0(X20)))))|(v2_struct_0(X20)|~l1_struct_0(X20))|~l1_struct_0(X19))&(k2_relset_1(u1_struct_0(X20),u1_struct_0(X19),k2_tops_2(u1_struct_0(X19),u1_struct_0(X20),X21))=k2_struct_0(X19)|(k2_relset_1(u1_struct_0(X19),u1_struct_0(X20),X21)!=k2_struct_0(X20)|~v2_funct_1(X21))|(~v1_funct_1(X21)|~v1_funct_2(X21,u1_struct_0(X19),u1_struct_0(X20))|~m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X19),u1_struct_0(X20)))))|(v2_struct_0(X20)|~l1_struct_0(X20))|~l1_struct_0(X19))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t62_tops_2])])])])])).
% 0.16/0.35  cnf(c_0_37, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.16/0.35  cnf(c_0_38, negated_conjecture, (v3_tops_2(esk3_0,esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.16/0.35  cnf(c_0_39, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.16/0.35  cnf(c_0_40, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.16/0.35  cnf(c_0_41, negated_conjecture, (v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.16/0.35  cnf(c_0_42, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.16/0.35  fof(c_0_43, plain, ![X22, X23, X24]:(~l1_struct_0(X22)|(~l1_struct_0(X23)|(~v1_funct_1(X24)|~v1_funct_2(X24,u1_struct_0(X22),u1_struct_0(X23))|~m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X22),u1_struct_0(X23))))|(k2_relset_1(u1_struct_0(X22),u1_struct_0(X23),X24)!=k2_struct_0(X23)|~v2_funct_1(X24)|v2_funct_1(k2_tops_2(u1_struct_0(X22),u1_struct_0(X23),X24)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_tops_2])])])).
% 0.16/0.35  cnf(c_0_44, plain, (v3_tops_2(X1,X2,X3)|k2_relset_1(u1_struct_0(X2),u1_struct_0(X3),X1)!=k2_struct_0(X3)|k1_relset_1(u1_struct_0(X2),u1_struct_0(X3),X1)!=k2_struct_0(X2)|k2_relset_1(u1_struct_0(X2),u1_struct_0(X3),X1)!=u1_struct_0(X3)|~v5_pre_topc(k2_funct_1(X1),X3,X2)|~v5_pre_topc(X1,X2,X3)|~l1_pre_topc(X3)|~l1_pre_topc(X2)|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))|~v2_funct_1(X1)|~v1_funct_1(X1)), inference(spm,[status(thm)],[c_0_32, c_0_13])).
% 0.16/0.35  cnf(c_0_45, plain, (v5_pre_topc(X1,X2,X3)|~v3_tops_2(X1,X2,X3)|~v1_funct_1(X1)|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))|~l1_pre_topc(X3)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.16/0.35  cnf(c_0_46, plain, (v5_pre_topc(X1,X2,X3)|k2_relset_1(u1_struct_0(X2),u1_struct_0(X3),X1)!=u1_struct_0(X3)|~v3_tops_2(k2_funct_1(X1),X3,X2)|~l1_pre_topc(X2)|~l1_pre_topc(X3)|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))|~v2_funct_1(X1)|~v1_funct_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35])).
% 0.16/0.35  cnf(c_0_47, plain, (k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),k2_tops_2(u1_struct_0(X2),u1_struct_0(X1),X3))=k2_struct_0(X1)|v2_struct_0(X1)|k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),X3)!=k2_struct_0(X1)|~v2_funct_1(X3)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))|~l1_struct_0(X1)|~l1_struct_0(X2)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.16/0.35  cnf(c_0_48, negated_conjecture, (k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0)=k2_struct_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_37]), c_0_38]), c_0_39]), c_0_40]), c_0_41]), c_0_42])])).
% 0.16/0.35  cnf(c_0_49, negated_conjecture, (v2_funct_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_37]), c_0_38]), c_0_39]), c_0_40]), c_0_41]), c_0_42])])).
% 0.16/0.35  cnf(c_0_50, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.16/0.35  cnf(c_0_51, plain, (v2_funct_1(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3))|~l1_struct_0(X1)|~l1_struct_0(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)!=k2_struct_0(X2)|~v2_funct_1(X3)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.16/0.35  cnf(c_0_52, plain, (k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),k2_tops_2(u1_struct_0(X2),u1_struct_0(X1),X3))=k2_struct_0(X2)|v2_struct_0(X1)|k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),X3)!=k2_struct_0(X1)|~v2_funct_1(X3)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))|~l1_struct_0(X1)|~l1_struct_0(X2)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.16/0.35  cnf(c_0_53, plain, (v3_tops_2(X1,X2,X3)|k2_relset_1(u1_struct_0(X2),u1_struct_0(X3),X1)!=k2_struct_0(X3)|k1_relset_1(u1_struct_0(X2),u1_struct_0(X3),X1)!=k2_struct_0(X2)|k2_relset_1(u1_struct_0(X2),u1_struct_0(X3),X1)!=u1_struct_0(X3)|~v3_tops_2(k2_funct_1(X1),X3,X2)|~l1_pre_topc(X3)|~l1_pre_topc(X2)|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))|~v2_funct_1(X1)|~v1_funct_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_26]), c_0_24]), c_0_27]), c_0_46])).
% 0.16/0.35  cnf(c_0_54, negated_conjecture, (k1_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0))=k2_struct_0(esk2_0)|~l1_struct_0(esk1_0)|~l1_struct_0(esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_37]), c_0_48]), c_0_41]), c_0_49]), c_0_42])]), c_0_50])).
% 0.16/0.35  cnf(c_0_55, plain, (v2_funct_1(k2_funct_1(X1))|k2_relset_1(u1_struct_0(X2),u1_struct_0(X3),X1)!=k2_struct_0(X3)|k2_relset_1(u1_struct_0(X2),u1_struct_0(X3),X1)!=u1_struct_0(X3)|~l1_struct_0(X3)|~l1_struct_0(X2)|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))|~v2_funct_1(X1)|~v1_funct_1(X1)), inference(spm,[status(thm)],[c_0_51, c_0_13])).
% 0.16/0.35  cnf(c_0_56, negated_conjecture, (k2_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0))=k2_struct_0(esk1_0)|~l1_struct_0(esk1_0)|~l1_struct_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_37]), c_0_41]), c_0_49]), c_0_42])]), c_0_50]), c_0_48])])).
% 0.16/0.35  cnf(c_0_57, negated_conjecture, (~v3_tops_2(k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0),esk2_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.16/0.35  cnf(c_0_58, plain, (v3_tops_2(k2_funct_1(X1),X2,X3)|k2_relset_1(u1_struct_0(X2),u1_struct_0(X3),k2_funct_1(X1))!=k2_struct_0(X3)|k1_relset_1(u1_struct_0(X2),u1_struct_0(X3),k2_funct_1(X1))!=k2_struct_0(X2)|k2_relset_1(u1_struct_0(X2),u1_struct_0(X3),k2_funct_1(X1))!=u1_struct_0(X3)|~v3_tops_2(X1,X3,X2)|~l1_pre_topc(X3)|~l1_pre_topc(X2)|~v1_funct_2(k2_funct_1(X1),u1_struct_0(X2),u1_struct_0(X3))|~m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))|~v2_funct_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_53, c_0_17])).
% 0.16/0.35  cnf(c_0_59, negated_conjecture, (k1_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k2_funct_1(esk3_0))=k2_struct_0(esk2_0)|~l1_struct_0(esk1_0)|~l1_struct_0(esk2_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_13]), c_0_48]), c_0_41]), c_0_37]), c_0_49]), c_0_42])]), c_0_29])).
% 0.16/0.35  cnf(c_0_60, negated_conjecture, (v1_relat_1(esk3_0)), inference(spm,[status(thm)],[c_0_25, c_0_37])).
% 0.16/0.35  cnf(c_0_61, negated_conjecture, (v2_funct_1(k2_funct_1(esk3_0))|~l1_struct_0(esk2_0)|~l1_struct_0(esk1_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_37]), c_0_48]), c_0_48]), c_0_41]), c_0_49]), c_0_42])]), c_0_29])).
% 0.16/0.35  cnf(c_0_62, negated_conjecture, (k2_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k2_funct_1(esk3_0))=k2_struct_0(esk1_0)|~l1_struct_0(esk1_0)|~l1_struct_0(esk2_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_13]), c_0_48]), c_0_41]), c_0_37]), c_0_49]), c_0_42])]), c_0_29])).
% 0.16/0.35  cnf(c_0_63, negated_conjecture, (v1_funct_1(k2_funct_1(esk3_0))|k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0)!=u1_struct_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_37]), c_0_41]), c_0_42])]), c_0_49])])).
% 0.16/0.35  cnf(c_0_64, negated_conjecture, (k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0)!=u1_struct_0(esk2_0)|~v3_tops_2(k2_funct_1(esk3_0),esk2_0,esk1_0)|~v2_funct_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_13]), c_0_41]), c_0_37]), c_0_42])])).
% 0.16/0.35  cnf(c_0_65, negated_conjecture, (v3_tops_2(k2_funct_1(esk3_0),esk2_0,esk1_0)|k2_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k2_funct_1(esk3_0))!=u1_struct_0(esk1_0)|~l1_struct_0(esk1_0)|~l1_struct_0(esk2_0)|~v1_funct_2(k2_funct_1(esk3_0),u1_struct_0(esk2_0),u1_struct_0(esk1_0))|~m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0))))|~v1_funct_1(k2_funct_1(esk3_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_38]), c_0_40]), c_0_39]), c_0_49]), c_0_42]), c_0_60])]), c_0_61]), c_0_62])).
% 0.16/0.35  cnf(c_0_66, negated_conjecture, (v1_funct_1(k2_funct_1(esk3_0))|k2_struct_0(esk2_0)!=u1_struct_0(esk2_0)), inference(rw,[status(thm)],[c_0_63, c_0_48])).
% 0.16/0.35  cnf(c_0_67, negated_conjecture, (k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0)!=u1_struct_0(esk2_0)|~v3_tops_2(k2_funct_1(esk3_0),esk2_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_64, c_0_49])])).
% 0.16/0.35  cnf(c_0_68, negated_conjecture, (v3_tops_2(k2_funct_1(esk3_0),esk2_0,esk1_0)|k2_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k2_funct_1(esk3_0))!=u1_struct_0(esk1_0)|~l1_struct_0(esk1_0)|~l1_struct_0(esk2_0)|~v1_funct_2(k2_funct_1(esk3_0),u1_struct_0(esk2_0),u1_struct_0(esk1_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_24]), c_0_48]), c_0_41]), c_0_37]), c_0_49]), c_0_42])]), c_0_66]), c_0_29])).
% 0.16/0.35  cnf(c_0_69, negated_conjecture, (k2_struct_0(esk2_0)!=u1_struct_0(esk2_0)|~v3_tops_2(k2_funct_1(esk3_0),esk2_0,esk1_0)), inference(rw,[status(thm)],[c_0_67, c_0_48])).
% 0.16/0.35  cnf(c_0_70, negated_conjecture, (v3_tops_2(k2_funct_1(esk3_0),esk2_0,esk1_0)|~l1_struct_0(esk1_0)|~l1_struct_0(esk2_0)|~v1_funct_2(k2_funct_1(esk3_0),u1_struct_0(esk2_0),u1_struct_0(esk1_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_62]), c_0_29])).
% 0.16/0.35  cnf(c_0_71, negated_conjecture, (~l1_struct_0(esk1_0)|~l1_struct_0(esk2_0)|~v1_funct_2(k2_funct_1(esk3_0),u1_struct_0(esk2_0),u1_struct_0(esk1_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_29])).
% 0.16/0.35  cnf(c_0_72, negated_conjecture, (~l1_struct_0(esk1_0)|~l1_struct_0(esk2_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_27]), c_0_48]), c_0_41]), c_0_37]), c_0_49]), c_0_42])]), c_0_29])).
% 0.16/0.35  cnf(c_0_73, negated_conjecture, (~l1_struct_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_30]), c_0_40])])).
% 0.16/0.35  cnf(c_0_74, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_30]), c_0_39])]), ['proof']).
% 0.16/0.35  # SZS output end CNFRefutation
% 0.16/0.35  # Proof object total steps             : 75
% 0.16/0.35  # Proof object clause steps            : 54
% 0.16/0.35  # Proof object formula steps           : 21
% 0.16/0.35  # Proof object conjectures             : 31
% 0.16/0.35  # Proof object clause conjectures      : 28
% 0.16/0.35  # Proof object formula conjectures     : 3
% 0.16/0.35  # Proof object initial clauses used    : 24
% 0.16/0.35  # Proof object initial formulas used   : 10
% 0.16/0.35  # Proof object generating inferences   : 27
% 0.16/0.35  # Proof object simplifying inferences  : 100
% 0.16/0.35  # Training examples: 0 positive, 0 negative
% 0.16/0.35  # Parsed axioms                        : 10
% 0.16/0.35  # Removed by relevancy pruning/SinE    : 0
% 0.16/0.35  # Initial clauses                      : 25
% 0.16/0.35  # Removed in clause preprocessing      : 0
% 0.16/0.35  # Initial clauses in saturation        : 25
% 0.16/0.35  # Processed clauses                    : 175
% 0.16/0.35  # ...of these trivial                  : 0
% 0.16/0.35  # ...subsumed                          : 13
% 0.16/0.35  # ...remaining for further processing  : 162
% 0.16/0.35  # Other redundant clauses eliminated   : 0
% 0.16/0.35  # Clauses deleted for lack of memory   : 0
% 0.16/0.35  # Backward-subsumed                    : 61
% 0.16/0.35  # Backward-rewritten                   : 4
% 0.16/0.35  # Generated clauses                    : 156
% 0.16/0.35  # ...of the previous two non-trivial   : 144
% 0.16/0.35  # Contextual simplify-reflections      : 63
% 0.16/0.35  # Paramodulations                      : 156
% 0.16/0.35  # Factorizations                       : 0
% 0.16/0.35  # Equation resolutions                 : 0
% 0.16/0.35  # Propositional unsat checks           : 0
% 0.16/0.35  #    Propositional check models        : 0
% 0.16/0.35  #    Propositional check unsatisfiable : 0
% 0.16/0.35  #    Propositional clauses             : 0
% 0.16/0.35  #    Propositional clauses after purity: 0
% 0.16/0.35  #    Propositional unsat core size     : 0
% 0.16/0.35  #    Propositional preprocessing time  : 0.000
% 0.16/0.35  #    Propositional encoding time       : 0.000
% 0.16/0.35  #    Propositional solver time         : 0.000
% 0.16/0.35  #    Success case prop preproc time    : 0.000
% 0.16/0.35  #    Success case prop encoding time   : 0.000
% 0.16/0.35  #    Success case prop solver time     : 0.000
% 0.16/0.35  # Current number of processed clauses  : 72
% 0.16/0.35  #    Positive orientable unit clauses  : 9
% 0.16/0.35  #    Positive unorientable unit clauses: 0
% 0.16/0.35  #    Negative unit clauses             : 3
% 0.16/0.35  #    Non-unit-clauses                  : 60
% 0.16/0.35  # Current number of unprocessed clauses: 12
% 0.16/0.35  # ...number of literals in the above   : 154
% 0.16/0.35  # Current number of archived formulas  : 0
% 0.16/0.35  # Current number of archived clauses   : 90
% 0.16/0.35  # Clause-clause subsumption calls (NU) : 4551
% 0.16/0.35  # Rec. Clause-clause subsumption calls : 455
% 0.16/0.35  # Non-unit clause-clause subsumptions  : 137
% 0.16/0.35  # Unit Clause-clause subsumption calls : 12
% 0.16/0.35  # Rewrite failures with RHS unbound    : 0
% 0.16/0.35  # BW rewrite match attempts            : 2
% 0.16/0.35  # BW rewrite match successes           : 2
% 0.16/0.35  # Condensation attempts                : 0
% 0.16/0.35  # Condensation successes               : 0
% 0.16/0.35  # Termbank termtop insertions          : 10699
% 0.16/0.35  
% 0.16/0.35  # -------------------------------------------------
% 0.16/0.35  # User time                : 0.043 s
% 0.16/0.35  # System time              : 0.004 s
% 0.16/0.35  # Total time               : 0.047 s
% 0.16/0.35  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
