%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:14:05 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 476 expanded)
%              Number of clauses        :   44 ( 145 expanded)
%              Number of leaves         :   11 ( 120 expanded)
%              Depth                    :   16
%              Number of atoms          :  357 (3354 expanded)
%              Number of equality atoms :   62 ( 143 expanded)
%              Maximal formula depth    :   20 (   6 average)
%              Maximal clause size      :   46 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_tops_2)).

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

fof(d4_tops_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( ( k2_relset_1(X1,X2,X3) = X2
          & v2_funct_1(X3) )
       => k2_tops_2(X1,X2,X3) = k2_funct_1(X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).

fof(cc2_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(fc6_relat_1,axiom,(
    ! [X1,X2] : v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(dt_k2_tops_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( v1_funct_1(k2_tops_2(X1,X2,X3))
        & v1_funct_2(k2_tops_2(X1,X2,X3),X2,X1)
        & m1_subset_1(k2_tops_2(X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_2)).

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

fof(t65_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => k2_funct_1(k2_funct_1(X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).

fof(d3_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => k2_struct_0(X1) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

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

fof(c_0_11,negated_conjecture,(
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

fof(c_0_12,plain,(
    ! [X14,X15,X16] :
      ( ( k1_relset_1(u1_struct_0(X14),u1_struct_0(X15),X16) = k2_struct_0(X14)
        | ~ v3_tops_2(X16,X14,X15)
        | ~ v1_funct_1(X16)
        | ~ v1_funct_2(X16,u1_struct_0(X14),u1_struct_0(X15))
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X14),u1_struct_0(X15))))
        | ~ l1_pre_topc(X15)
        | ~ l1_pre_topc(X14) )
      & ( k2_relset_1(u1_struct_0(X14),u1_struct_0(X15),X16) = k2_struct_0(X15)
        | ~ v3_tops_2(X16,X14,X15)
        | ~ v1_funct_1(X16)
        | ~ v1_funct_2(X16,u1_struct_0(X14),u1_struct_0(X15))
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X14),u1_struct_0(X15))))
        | ~ l1_pre_topc(X15)
        | ~ l1_pre_topc(X14) )
      & ( v2_funct_1(X16)
        | ~ v3_tops_2(X16,X14,X15)
        | ~ v1_funct_1(X16)
        | ~ v1_funct_2(X16,u1_struct_0(X14),u1_struct_0(X15))
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X14),u1_struct_0(X15))))
        | ~ l1_pre_topc(X15)
        | ~ l1_pre_topc(X14) )
      & ( v5_pre_topc(X16,X14,X15)
        | ~ v3_tops_2(X16,X14,X15)
        | ~ v1_funct_1(X16)
        | ~ v1_funct_2(X16,u1_struct_0(X14),u1_struct_0(X15))
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X14),u1_struct_0(X15))))
        | ~ l1_pre_topc(X15)
        | ~ l1_pre_topc(X14) )
      & ( v5_pre_topc(k2_tops_2(u1_struct_0(X14),u1_struct_0(X15),X16),X15,X14)
        | ~ v3_tops_2(X16,X14,X15)
        | ~ v1_funct_1(X16)
        | ~ v1_funct_2(X16,u1_struct_0(X14),u1_struct_0(X15))
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X14),u1_struct_0(X15))))
        | ~ l1_pre_topc(X15)
        | ~ l1_pre_topc(X14) )
      & ( k1_relset_1(u1_struct_0(X14),u1_struct_0(X15),X16) != k2_struct_0(X14)
        | k2_relset_1(u1_struct_0(X14),u1_struct_0(X15),X16) != k2_struct_0(X15)
        | ~ v2_funct_1(X16)
        | ~ v5_pre_topc(X16,X14,X15)
        | ~ v5_pre_topc(k2_tops_2(u1_struct_0(X14),u1_struct_0(X15),X16),X15,X14)
        | v3_tops_2(X16,X14,X15)
        | ~ v1_funct_1(X16)
        | ~ v1_funct_2(X16,u1_struct_0(X14),u1_struct_0(X15))
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X14),u1_struct_0(X15))))
        | ~ l1_pre_topc(X15)
        | ~ l1_pre_topc(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_tops_2])])])])).

fof(c_0_13,negated_conjecture,
    ( l1_pre_topc(esk1_0)
    & ~ v2_struct_0(esk2_0)
    & l1_pre_topc(esk2_0)
    & v1_funct_1(esk3_0)
    & v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0))
    & m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))
    & v3_tops_2(esk3_0,esk1_0,esk2_0)
    & ~ v3_tops_2(k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0),esk2_0,esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_11])])])])).

fof(c_0_14,plain,(
    ! [X11,X12,X13] :
      ( ~ v1_funct_1(X13)
      | ~ v1_funct_2(X13,X11,X12)
      | ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X11,X12)))
      | k2_relset_1(X11,X12,X13) != X12
      | ~ v2_funct_1(X13)
      | k2_tops_2(X11,X12,X13) = k2_funct_1(X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tops_2])])).

cnf(c_0_15,plain,
    ( v2_funct_1(X1)
    | ~ v3_tops_2(X1,X2,X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,negated_conjecture,
    ( v3_tops_2(esk3_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_22,plain,(
    ! [X4,X5] :
      ( ~ v1_relat_1(X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(X4))
      | v1_relat_1(X5) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_23,plain,(
    ! [X6,X7] : v1_relat_1(k2_zfmisc_1(X6,X7)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

fof(c_0_24,plain,(
    ! [X17,X18,X19] :
      ( ( v1_funct_1(k2_tops_2(X17,X18,X19))
        | ~ v1_funct_1(X19)
        | ~ v1_funct_2(X19,X17,X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18))) )
      & ( v1_funct_2(k2_tops_2(X17,X18,X19),X18,X17)
        | ~ v1_funct_1(X19)
        | ~ v1_funct_2(X19,X17,X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18))) )
      & ( m1_subset_1(k2_tops_2(X17,X18,X19),k1_zfmisc_1(k2_zfmisc_1(X18,X17)))
        | ~ v1_funct_1(X19)
        | ~ v1_funct_2(X19,X17,X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_tops_2])])])).

fof(c_0_25,plain,(
    ! [X20,X21,X22] :
      ( ( k1_relset_1(u1_struct_0(X21),u1_struct_0(X20),k2_tops_2(u1_struct_0(X20),u1_struct_0(X21),X22)) = k2_struct_0(X21)
        | k2_relset_1(u1_struct_0(X20),u1_struct_0(X21),X22) != k2_struct_0(X21)
        | ~ v2_funct_1(X22)
        | ~ v1_funct_1(X22)
        | ~ v1_funct_2(X22,u1_struct_0(X20),u1_struct_0(X21))
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X20),u1_struct_0(X21))))
        | v2_struct_0(X21)
        | ~ l1_struct_0(X21)
        | ~ l1_struct_0(X20) )
      & ( k2_relset_1(u1_struct_0(X21),u1_struct_0(X20),k2_tops_2(u1_struct_0(X20),u1_struct_0(X21),X22)) = k2_struct_0(X20)
        | k2_relset_1(u1_struct_0(X20),u1_struct_0(X21),X22) != k2_struct_0(X21)
        | ~ v2_funct_1(X22)
        | ~ v1_funct_1(X22)
        | ~ v1_funct_2(X22,u1_struct_0(X20),u1_struct_0(X21))
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X20),u1_struct_0(X21))))
        | v2_struct_0(X21)
        | ~ l1_struct_0(X21)
        | ~ l1_struct_0(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t62_tops_2])])])])])).

fof(c_0_26,plain,(
    ! [X8] :
      ( ~ v1_relat_1(X8)
      | ~ v1_funct_1(X8)
      | ~ v2_funct_1(X8)
      | k2_funct_1(k2_funct_1(X8)) = X8 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_funct_1])])).

cnf(c_0_27,plain,
    ( k2_tops_2(X2,X3,X1) = k2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | k2_relset_1(X2,X3,X1) != X3
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_28,negated_conjecture,
    ( v2_funct_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17]),c_0_18]),c_0_19]),c_0_20]),c_0_21])])).

cnf(c_0_29,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_31,plain,
    ( m1_subset_1(k2_tops_2(X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_32,plain,
    ( v1_funct_1(k2_tops_2(X1,X2,X3))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_33,plain,
    ( v1_funct_2(k2_tops_2(X1,X2,X3),X2,X1)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_34,plain,
    ( k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),k2_tops_2(u1_struct_0(X2),u1_struct_0(X1),X3)) = k2_struct_0(X2)
    | v2_struct_0(X1)
    | k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),X3) != k2_struct_0(X1)
    | ~ v2_funct_1(X3)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_35,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_36,plain,(
    ! [X9] :
      ( ~ l1_struct_0(X9)
      | k2_struct_0(X9) = u1_struct_0(X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

cnf(c_0_37,plain,
    ( k2_funct_1(k2_funct_1(X1)) = X1
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_38,negated_conjecture,
    ( k2_funct_1(esk3_0) = k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0)
    | k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0) != u1_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_16]),c_0_18]),c_0_28]),c_0_21])])).

cnf(c_0_39,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_16]),c_0_30])])).

cnf(c_0_40,plain,
    ( k2_tops_2(X1,X2,k2_tops_2(X2,X1,X3)) = k2_funct_1(k2_tops_2(X2,X1,X3))
    | k2_relset_1(X1,X2,k2_tops_2(X2,X1,X3)) != X2
    | ~ v1_funct_2(X3,X2,X1)
    | ~ v2_funct_1(k2_tops_2(X2,X1,X3))
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_31]),c_0_32]),c_0_33])).

cnf(c_0_41,negated_conjecture,
    ( k2_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0)) = k2_struct_0(esk1_0)
    | k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0) != k2_struct_0(esk2_0)
    | ~ l1_struct_0(esk1_0)
    | ~ l1_struct_0(esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_16]),c_0_18]),c_0_28]),c_0_21])]),c_0_35])).

cnf(c_0_42,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_43,negated_conjecture,
    ( k2_funct_1(k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0)) = esk3_0
    | k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0) != u1_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_28]),c_0_21]),c_0_39])])).

cnf(c_0_44,negated_conjecture,
    ( k2_funct_1(k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0)) = k2_tops_2(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0))
    | k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0) != k2_struct_0(esk2_0)
    | ~ l1_struct_0(esk1_0)
    | ~ l1_struct_0(esk2_0)
    | ~ v2_funct_1(k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_18]),c_0_21]),c_0_16])]),c_0_42])).

cnf(c_0_45,plain,
    ( k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),k2_tops_2(u1_struct_0(X2),u1_struct_0(X1),X3)) = k2_struct_0(X1)
    | v2_struct_0(X1)
    | k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),X3) != k2_struct_0(X1)
    | ~ v2_funct_1(X3)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_46,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_47,negated_conjecture,
    ( k2_tops_2(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0)) = esk3_0
    | k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0) != u1_struct_0(esk2_0)
    | k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0) != k2_struct_0(esk2_0)
    | ~ l1_struct_0(esk1_0)
    | ~ l1_struct_0(esk2_0)
    | ~ v2_funct_1(k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_48,negated_conjecture,
    ( v1_funct_1(k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_16]),c_0_18]),c_0_21])])).

cnf(c_0_49,negated_conjecture,
    ( ~ v3_tops_2(k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0),esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_50,negated_conjecture,
    ( k1_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0)) = k2_struct_0(esk2_0)
    | k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0) != k2_struct_0(esk2_0)
    | ~ l1_struct_0(esk1_0)
    | ~ l1_struct_0(esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_16]),c_0_18]),c_0_28]),c_0_21])]),c_0_35])).

cnf(c_0_51,negated_conjecture,
    ( k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0) != u1_struct_0(esk2_0)
    | k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0) != k2_struct_0(esk2_0)
    | ~ v5_pre_topc(k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0),esk2_0,esk1_0)
    | ~ v5_pre_topc(esk3_0,esk1_0,esk2_0)
    | ~ v1_funct_2(k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0),u1_struct_0(esk2_0),u1_struct_0(esk1_0))
    | ~ l1_struct_0(esk1_0)
    | ~ l1_struct_0(esk2_0)
    | ~ v2_funct_1(k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0)))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_20]),c_0_19]),c_0_48])]),c_0_49]),c_0_50]),c_0_41])).

cnf(c_0_52,plain,
    ( v5_pre_topc(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3),X2,X1)
    | ~ v3_tops_2(X3,X1,X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_53,negated_conjecture,
    ( k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0) != u1_struct_0(esk2_0)
    | k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0) != k2_struct_0(esk2_0)
    | ~ v5_pre_topc(esk3_0,esk1_0,esk2_0)
    | ~ v1_funct_2(k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0),u1_struct_0(esk2_0),u1_struct_0(esk1_0))
    | ~ l1_struct_0(esk1_0)
    | ~ l1_struct_0(esk2_0)
    | ~ v2_funct_1(k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_17]),c_0_18]),c_0_19]),c_0_20]),c_0_21]),c_0_16])])).

cnf(c_0_54,negated_conjecture,
    ( k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0) != u1_struct_0(esk2_0)
    | k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0) != k2_struct_0(esk2_0)
    | ~ v5_pre_topc(esk3_0,esk1_0,esk2_0)
    | ~ v1_funct_2(k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0),u1_struct_0(esk2_0),u1_struct_0(esk1_0))
    | ~ l1_struct_0(esk1_0)
    | ~ l1_struct_0(esk2_0)
    | ~ v2_funct_1(k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_31]),c_0_18]),c_0_21]),c_0_16])])).

fof(c_0_55,plain,(
    ! [X23,X24,X25] :
      ( ~ l1_struct_0(X23)
      | ~ l1_struct_0(X24)
      | ~ v1_funct_1(X25)
      | ~ v1_funct_2(X25,u1_struct_0(X23),u1_struct_0(X24))
      | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X23),u1_struct_0(X24))))
      | k2_relset_1(u1_struct_0(X23),u1_struct_0(X24),X25) != k2_struct_0(X24)
      | ~ v2_funct_1(X25)
      | v2_funct_1(k2_tops_2(u1_struct_0(X23),u1_struct_0(X24),X25)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_tops_2])])])).

cnf(c_0_56,negated_conjecture,
    ( k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0) != u1_struct_0(esk2_0)
    | k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0) != k2_struct_0(esk2_0)
    | ~ v5_pre_topc(esk3_0,esk1_0,esk2_0)
    | ~ l1_struct_0(esk1_0)
    | ~ l1_struct_0(esk2_0)
    | ~ v2_funct_1(k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_33]),c_0_18]),c_0_21]),c_0_16])])).

cnf(c_0_57,plain,
    ( v2_funct_1(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) != k2_struct_0(X2)
    | ~ v2_funct_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_58,negated_conjecture,
    ( k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0) != u1_struct_0(esk2_0)
    | k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0) != k2_struct_0(esk2_0)
    | ~ v5_pre_topc(esk3_0,esk1_0,esk2_0)
    | ~ l1_struct_0(esk1_0)
    | ~ l1_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_18]),c_0_28]),c_0_21]),c_0_16])])).

cnf(c_0_59,plain,
    ( v5_pre_topc(X1,X2,X3)
    | ~ v3_tops_2(X1,X2,X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_60,negated_conjecture,
    ( k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0) != u1_struct_0(esk2_0)
    | k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0) != k2_struct_0(esk2_0)
    | ~ l1_struct_0(esk1_0)
    | ~ l1_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_17]),c_0_18]),c_0_19]),c_0_20]),c_0_21]),c_0_16])])).

cnf(c_0_61,plain,
    ( k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) = k2_struct_0(X2)
    | ~ v3_tops_2(X3,X1,X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_62,plain,(
    ! [X10] :
      ( ~ l1_pre_topc(X10)
      | l1_struct_0(X10) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_63,negated_conjecture,
    ( ~ l1_struct_0(esk1_0)
    | ~ l1_struct_0(esk2_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_17]),c_0_18]),c_0_19]),c_0_20]),c_0_21]),c_0_16])]),c_0_42])).

cnf(c_0_64,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_65,negated_conjecture,
    ( ~ l1_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_20])])).

cnf(c_0_66,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_64]),c_0_19])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:46:05 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.21/0.39  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.21/0.39  #
% 0.21/0.39  # Preprocessing time       : 0.028 s
% 0.21/0.39  # Presaturation interreduction done
% 0.21/0.39  
% 0.21/0.39  # Proof found!
% 0.21/0.39  # SZS status Theorem
% 0.21/0.39  # SZS output start CNFRefutation
% 0.21/0.39  fof(t70_tops_2, conjecture, ![X1]:(l1_pre_topc(X1)=>![X2]:((~(v2_struct_0(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>(v3_tops_2(X3,X1,X2)=>v3_tops_2(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3),X2,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_tops_2)).
% 0.21/0.39  fof(d5_tops_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(l1_pre_topc(X2)=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>(v3_tops_2(X3,X1,X2)<=>((((k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)=k2_struct_0(X1)&k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)=k2_struct_0(X2))&v2_funct_1(X3))&v5_pre_topc(X3,X1,X2))&v5_pre_topc(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3),X2,X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tops_2)).
% 0.21/0.39  fof(d4_tops_2, axiom, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((k2_relset_1(X1,X2,X3)=X2&v2_funct_1(X3))=>k2_tops_2(X1,X2,X3)=k2_funct_1(X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tops_2)).
% 0.21/0.39  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.21/0.39  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.21/0.39  fof(dt_k2_tops_2, axiom, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((v1_funct_1(k2_tops_2(X1,X2,X3))&v1_funct_2(k2_tops_2(X1,X2,X3),X2,X1))&m1_subset_1(k2_tops_2(X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tops_2)).
% 0.21/0.39  fof(t62_tops_2, axiom, ![X1]:(l1_struct_0(X1)=>![X2]:((~(v2_struct_0(X2))&l1_struct_0(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>((k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)=k2_struct_0(X2)&v2_funct_1(X3))=>(k1_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3))=k2_struct_0(X2)&k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3))=k2_struct_0(X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_tops_2)).
% 0.21/0.39  fof(t65_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>k2_funct_1(k2_funct_1(X1))=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_1)).
% 0.21/0.39  fof(d3_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>k2_struct_0(X1)=u1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 0.21/0.39  fof(t63_tops_2, axiom, ![X1]:(l1_struct_0(X1)=>![X2]:(l1_struct_0(X2)=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>((k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)=k2_struct_0(X2)&v2_funct_1(X3))=>v2_funct_1(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_tops_2)).
% 0.21/0.39  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.21/0.39  fof(c_0_11, negated_conjecture, ~(![X1]:(l1_pre_topc(X1)=>![X2]:((~(v2_struct_0(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>(v3_tops_2(X3,X1,X2)=>v3_tops_2(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3),X2,X1)))))), inference(assume_negation,[status(cth)],[t70_tops_2])).
% 0.21/0.39  fof(c_0_12, plain, ![X14, X15, X16]:((((((k1_relset_1(u1_struct_0(X14),u1_struct_0(X15),X16)=k2_struct_0(X14)|~v3_tops_2(X16,X14,X15)|(~v1_funct_1(X16)|~v1_funct_2(X16,u1_struct_0(X14),u1_struct_0(X15))|~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X14),u1_struct_0(X15)))))|~l1_pre_topc(X15)|~l1_pre_topc(X14))&(k2_relset_1(u1_struct_0(X14),u1_struct_0(X15),X16)=k2_struct_0(X15)|~v3_tops_2(X16,X14,X15)|(~v1_funct_1(X16)|~v1_funct_2(X16,u1_struct_0(X14),u1_struct_0(X15))|~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X14),u1_struct_0(X15)))))|~l1_pre_topc(X15)|~l1_pre_topc(X14)))&(v2_funct_1(X16)|~v3_tops_2(X16,X14,X15)|(~v1_funct_1(X16)|~v1_funct_2(X16,u1_struct_0(X14),u1_struct_0(X15))|~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X14),u1_struct_0(X15)))))|~l1_pre_topc(X15)|~l1_pre_topc(X14)))&(v5_pre_topc(X16,X14,X15)|~v3_tops_2(X16,X14,X15)|(~v1_funct_1(X16)|~v1_funct_2(X16,u1_struct_0(X14),u1_struct_0(X15))|~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X14),u1_struct_0(X15)))))|~l1_pre_topc(X15)|~l1_pre_topc(X14)))&(v5_pre_topc(k2_tops_2(u1_struct_0(X14),u1_struct_0(X15),X16),X15,X14)|~v3_tops_2(X16,X14,X15)|(~v1_funct_1(X16)|~v1_funct_2(X16,u1_struct_0(X14),u1_struct_0(X15))|~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X14),u1_struct_0(X15)))))|~l1_pre_topc(X15)|~l1_pre_topc(X14)))&(k1_relset_1(u1_struct_0(X14),u1_struct_0(X15),X16)!=k2_struct_0(X14)|k2_relset_1(u1_struct_0(X14),u1_struct_0(X15),X16)!=k2_struct_0(X15)|~v2_funct_1(X16)|~v5_pre_topc(X16,X14,X15)|~v5_pre_topc(k2_tops_2(u1_struct_0(X14),u1_struct_0(X15),X16),X15,X14)|v3_tops_2(X16,X14,X15)|(~v1_funct_1(X16)|~v1_funct_2(X16,u1_struct_0(X14),u1_struct_0(X15))|~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X14),u1_struct_0(X15)))))|~l1_pre_topc(X15)|~l1_pre_topc(X14))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_tops_2])])])])).
% 0.21/0.39  fof(c_0_13, negated_conjecture, (l1_pre_topc(esk1_0)&((~v2_struct_0(esk2_0)&l1_pre_topc(esk2_0))&(((v1_funct_1(esk3_0)&v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0)))&m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))))&(v3_tops_2(esk3_0,esk1_0,esk2_0)&~v3_tops_2(k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0),esk2_0,esk1_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_11])])])])).
% 0.21/0.39  fof(c_0_14, plain, ![X11, X12, X13]:(~v1_funct_1(X13)|~v1_funct_2(X13,X11,X12)|~m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X11,X12)))|(k2_relset_1(X11,X12,X13)!=X12|~v2_funct_1(X13)|k2_tops_2(X11,X12,X13)=k2_funct_1(X13))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tops_2])])).
% 0.21/0.39  cnf(c_0_15, plain, (v2_funct_1(X1)|~v3_tops_2(X1,X2,X3)|~v1_funct_1(X1)|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))|~l1_pre_topc(X3)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.39  cnf(c_0_16, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.21/0.39  cnf(c_0_17, negated_conjecture, (v3_tops_2(esk3_0,esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.21/0.39  cnf(c_0_18, negated_conjecture, (v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.21/0.39  cnf(c_0_19, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.21/0.39  cnf(c_0_20, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.21/0.39  cnf(c_0_21, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.21/0.39  fof(c_0_22, plain, ![X4, X5]:(~v1_relat_1(X4)|(~m1_subset_1(X5,k1_zfmisc_1(X4))|v1_relat_1(X5))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.21/0.39  fof(c_0_23, plain, ![X6, X7]:v1_relat_1(k2_zfmisc_1(X6,X7)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.21/0.39  fof(c_0_24, plain, ![X17, X18, X19]:(((v1_funct_1(k2_tops_2(X17,X18,X19))|(~v1_funct_1(X19)|~v1_funct_2(X19,X17,X18)|~m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18)))))&(v1_funct_2(k2_tops_2(X17,X18,X19),X18,X17)|(~v1_funct_1(X19)|~v1_funct_2(X19,X17,X18)|~m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18))))))&(m1_subset_1(k2_tops_2(X17,X18,X19),k1_zfmisc_1(k2_zfmisc_1(X18,X17)))|(~v1_funct_1(X19)|~v1_funct_2(X19,X17,X18)|~m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_tops_2])])])).
% 0.21/0.39  fof(c_0_25, plain, ![X20, X21, X22]:((k1_relset_1(u1_struct_0(X21),u1_struct_0(X20),k2_tops_2(u1_struct_0(X20),u1_struct_0(X21),X22))=k2_struct_0(X21)|(k2_relset_1(u1_struct_0(X20),u1_struct_0(X21),X22)!=k2_struct_0(X21)|~v2_funct_1(X22))|(~v1_funct_1(X22)|~v1_funct_2(X22,u1_struct_0(X20),u1_struct_0(X21))|~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X20),u1_struct_0(X21)))))|(v2_struct_0(X21)|~l1_struct_0(X21))|~l1_struct_0(X20))&(k2_relset_1(u1_struct_0(X21),u1_struct_0(X20),k2_tops_2(u1_struct_0(X20),u1_struct_0(X21),X22))=k2_struct_0(X20)|(k2_relset_1(u1_struct_0(X20),u1_struct_0(X21),X22)!=k2_struct_0(X21)|~v2_funct_1(X22))|(~v1_funct_1(X22)|~v1_funct_2(X22,u1_struct_0(X20),u1_struct_0(X21))|~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X20),u1_struct_0(X21)))))|(v2_struct_0(X21)|~l1_struct_0(X21))|~l1_struct_0(X20))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t62_tops_2])])])])])).
% 0.21/0.39  fof(c_0_26, plain, ![X8]:(~v1_relat_1(X8)|~v1_funct_1(X8)|(~v2_funct_1(X8)|k2_funct_1(k2_funct_1(X8))=X8)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_funct_1])])).
% 0.21/0.39  cnf(c_0_27, plain, (k2_tops_2(X2,X3,X1)=k2_funct_1(X1)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|k2_relset_1(X2,X3,X1)!=X3|~v2_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.39  cnf(c_0_28, negated_conjecture, (v2_funct_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_17]), c_0_18]), c_0_19]), c_0_20]), c_0_21])])).
% 0.21/0.39  cnf(c_0_29, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.21/0.39  cnf(c_0_30, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.21/0.39  cnf(c_0_31, plain, (m1_subset_1(k2_tops_2(X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))|~v1_funct_1(X3)|~v1_funct_2(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.21/0.39  cnf(c_0_32, plain, (v1_funct_1(k2_tops_2(X1,X2,X3))|~v1_funct_1(X3)|~v1_funct_2(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.21/0.39  cnf(c_0_33, plain, (v1_funct_2(k2_tops_2(X1,X2,X3),X2,X1)|~v1_funct_1(X3)|~v1_funct_2(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.21/0.39  cnf(c_0_34, plain, (k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),k2_tops_2(u1_struct_0(X2),u1_struct_0(X1),X3))=k2_struct_0(X2)|v2_struct_0(X1)|k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),X3)!=k2_struct_0(X1)|~v2_funct_1(X3)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))|~l1_struct_0(X1)|~l1_struct_0(X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.21/0.39  cnf(c_0_35, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.21/0.39  fof(c_0_36, plain, ![X9]:(~l1_struct_0(X9)|k2_struct_0(X9)=u1_struct_0(X9)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).
% 0.21/0.39  cnf(c_0_37, plain, (k2_funct_1(k2_funct_1(X1))=X1|~v1_relat_1(X1)|~v1_funct_1(X1)|~v2_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.21/0.39  cnf(c_0_38, negated_conjecture, (k2_funct_1(esk3_0)=k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0)|k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0)!=u1_struct_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_16]), c_0_18]), c_0_28]), c_0_21])])).
% 0.21/0.39  cnf(c_0_39, negated_conjecture, (v1_relat_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_16]), c_0_30])])).
% 0.21/0.39  cnf(c_0_40, plain, (k2_tops_2(X1,X2,k2_tops_2(X2,X1,X3))=k2_funct_1(k2_tops_2(X2,X1,X3))|k2_relset_1(X1,X2,k2_tops_2(X2,X1,X3))!=X2|~v1_funct_2(X3,X2,X1)|~v2_funct_1(k2_tops_2(X2,X1,X3))|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_31]), c_0_32]), c_0_33])).
% 0.21/0.39  cnf(c_0_41, negated_conjecture, (k2_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0))=k2_struct_0(esk1_0)|k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0)!=k2_struct_0(esk2_0)|~l1_struct_0(esk1_0)|~l1_struct_0(esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_16]), c_0_18]), c_0_28]), c_0_21])]), c_0_35])).
% 0.21/0.39  cnf(c_0_42, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.21/0.39  cnf(c_0_43, negated_conjecture, (k2_funct_1(k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0))=esk3_0|k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0)!=u1_struct_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_28]), c_0_21]), c_0_39])])).
% 0.21/0.39  cnf(c_0_44, negated_conjecture, (k2_funct_1(k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0))=k2_tops_2(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0))|k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0)!=k2_struct_0(esk2_0)|~l1_struct_0(esk1_0)|~l1_struct_0(esk2_0)|~v2_funct_1(k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_18]), c_0_21]), c_0_16])]), c_0_42])).
% 0.21/0.39  cnf(c_0_45, plain, (k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),k2_tops_2(u1_struct_0(X2),u1_struct_0(X1),X3))=k2_struct_0(X1)|v2_struct_0(X1)|k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),X3)!=k2_struct_0(X1)|~v2_funct_1(X3)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))|~l1_struct_0(X1)|~l1_struct_0(X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.21/0.39  cnf(c_0_46, plain, (v3_tops_2(X3,X1,X2)|k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)!=k2_struct_0(X1)|k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)!=k2_struct_0(X2)|~v2_funct_1(X3)|~v5_pre_topc(X3,X1,X2)|~v5_pre_topc(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3),X2,X1)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.39  cnf(c_0_47, negated_conjecture, (k2_tops_2(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0))=esk3_0|k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0)!=u1_struct_0(esk2_0)|k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0)!=k2_struct_0(esk2_0)|~l1_struct_0(esk1_0)|~l1_struct_0(esk2_0)|~v2_funct_1(k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0))), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.21/0.39  cnf(c_0_48, negated_conjecture, (v1_funct_1(k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_16]), c_0_18]), c_0_21])])).
% 0.21/0.39  cnf(c_0_49, negated_conjecture, (~v3_tops_2(k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0),esk2_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.21/0.39  cnf(c_0_50, negated_conjecture, (k1_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0))=k2_struct_0(esk2_0)|k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0)!=k2_struct_0(esk2_0)|~l1_struct_0(esk1_0)|~l1_struct_0(esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_16]), c_0_18]), c_0_28]), c_0_21])]), c_0_35])).
% 0.21/0.39  cnf(c_0_51, negated_conjecture, (k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0)!=u1_struct_0(esk2_0)|k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0)!=k2_struct_0(esk2_0)|~v5_pre_topc(k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0),esk2_0,esk1_0)|~v5_pre_topc(esk3_0,esk1_0,esk2_0)|~v1_funct_2(k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0),u1_struct_0(esk2_0),u1_struct_0(esk1_0))|~l1_struct_0(esk1_0)|~l1_struct_0(esk2_0)|~v2_funct_1(k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0))|~m1_subset_1(k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0))))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_20]), c_0_19]), c_0_48])]), c_0_49]), c_0_50]), c_0_41])).
% 0.21/0.39  cnf(c_0_52, plain, (v5_pre_topc(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3),X2,X1)|~v3_tops_2(X3,X1,X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.39  cnf(c_0_53, negated_conjecture, (k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0)!=u1_struct_0(esk2_0)|k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0)!=k2_struct_0(esk2_0)|~v5_pre_topc(esk3_0,esk1_0,esk2_0)|~v1_funct_2(k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0),u1_struct_0(esk2_0),u1_struct_0(esk1_0))|~l1_struct_0(esk1_0)|~l1_struct_0(esk2_0)|~v2_funct_1(k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0))|~m1_subset_1(k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_17]), c_0_18]), c_0_19]), c_0_20]), c_0_21]), c_0_16])])).
% 0.21/0.39  cnf(c_0_54, negated_conjecture, (k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0)!=u1_struct_0(esk2_0)|k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0)!=k2_struct_0(esk2_0)|~v5_pre_topc(esk3_0,esk1_0,esk2_0)|~v1_funct_2(k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0),u1_struct_0(esk2_0),u1_struct_0(esk1_0))|~l1_struct_0(esk1_0)|~l1_struct_0(esk2_0)|~v2_funct_1(k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_31]), c_0_18]), c_0_21]), c_0_16])])).
% 0.21/0.39  fof(c_0_55, plain, ![X23, X24, X25]:(~l1_struct_0(X23)|(~l1_struct_0(X24)|(~v1_funct_1(X25)|~v1_funct_2(X25,u1_struct_0(X23),u1_struct_0(X24))|~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X23),u1_struct_0(X24))))|(k2_relset_1(u1_struct_0(X23),u1_struct_0(X24),X25)!=k2_struct_0(X24)|~v2_funct_1(X25)|v2_funct_1(k2_tops_2(u1_struct_0(X23),u1_struct_0(X24),X25)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_tops_2])])])).
% 0.21/0.39  cnf(c_0_56, negated_conjecture, (k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0)!=u1_struct_0(esk2_0)|k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0)!=k2_struct_0(esk2_0)|~v5_pre_topc(esk3_0,esk1_0,esk2_0)|~l1_struct_0(esk1_0)|~l1_struct_0(esk2_0)|~v2_funct_1(k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_33]), c_0_18]), c_0_21]), c_0_16])])).
% 0.21/0.39  cnf(c_0_57, plain, (v2_funct_1(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3))|~l1_struct_0(X1)|~l1_struct_0(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)!=k2_struct_0(X2)|~v2_funct_1(X3)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.21/0.39  cnf(c_0_58, negated_conjecture, (k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0)!=u1_struct_0(esk2_0)|k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0)!=k2_struct_0(esk2_0)|~v5_pre_topc(esk3_0,esk1_0,esk2_0)|~l1_struct_0(esk1_0)|~l1_struct_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_18]), c_0_28]), c_0_21]), c_0_16])])).
% 0.21/0.39  cnf(c_0_59, plain, (v5_pre_topc(X1,X2,X3)|~v3_tops_2(X1,X2,X3)|~v1_funct_1(X1)|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))|~l1_pre_topc(X3)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.39  cnf(c_0_60, negated_conjecture, (k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0)!=u1_struct_0(esk2_0)|k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0)!=k2_struct_0(esk2_0)|~l1_struct_0(esk1_0)|~l1_struct_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_17]), c_0_18]), c_0_19]), c_0_20]), c_0_21]), c_0_16])])).
% 0.21/0.39  cnf(c_0_61, plain, (k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)=k2_struct_0(X2)|~v3_tops_2(X3,X1,X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.39  fof(c_0_62, plain, ![X10]:(~l1_pre_topc(X10)|l1_struct_0(X10)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.21/0.39  cnf(c_0_63, negated_conjecture, (~l1_struct_0(esk1_0)|~l1_struct_0(esk2_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_17]), c_0_18]), c_0_19]), c_0_20]), c_0_21]), c_0_16])]), c_0_42])).
% 0.21/0.39  cnf(c_0_64, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.21/0.39  cnf(c_0_65, negated_conjecture, (~l1_struct_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_20])])).
% 0.21/0.39  cnf(c_0_66, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_64]), c_0_19])]), ['proof']).
% 0.21/0.39  # SZS output end CNFRefutation
% 0.21/0.39  # Proof object total steps             : 67
% 0.21/0.39  # Proof object clause steps            : 44
% 0.21/0.39  # Proof object formula steps           : 23
% 0.21/0.39  # Proof object conjectures             : 29
% 0.21/0.39  # Proof object clause conjectures      : 26
% 0.21/0.39  # Proof object formula conjectures     : 3
% 0.21/0.39  # Proof object initial clauses used    : 25
% 0.21/0.39  # Proof object initial formulas used   : 11
% 0.21/0.39  # Proof object generating inferences   : 19
% 0.21/0.39  # Proof object simplifying inferences  : 82
% 0.21/0.39  # Training examples: 0 positive, 0 negative
% 0.21/0.39  # Parsed axioms                        : 11
% 0.21/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.39  # Initial clauses                      : 26
% 0.21/0.39  # Removed in clause preprocessing      : 0
% 0.21/0.39  # Initial clauses in saturation        : 26
% 0.21/0.39  # Processed clauses                    : 124
% 0.21/0.39  # ...of these trivial                  : 0
% 0.21/0.39  # ...subsumed                          : 10
% 0.21/0.39  # ...remaining for further processing  : 114
% 0.21/0.39  # Other redundant clauses eliminated   : 0
% 0.21/0.39  # Clauses deleted for lack of memory   : 0
% 0.21/0.39  # Backward-subsumed                    : 39
% 0.21/0.39  # Backward-rewritten                   : 0
% 0.21/0.39  # Generated clauses                    : 107
% 0.21/0.39  # ...of the previous two non-trivial   : 95
% 0.21/0.39  # Contextual simplify-reflections      : 22
% 0.21/0.39  # Paramodulations                      : 107
% 0.21/0.39  # Factorizations                       : 0
% 0.21/0.39  # Equation resolutions                 : 0
% 0.21/0.39  # Propositional unsat checks           : 0
% 0.21/0.39  #    Propositional check models        : 0
% 0.21/0.39  #    Propositional check unsatisfiable : 0
% 0.21/0.39  #    Propositional clauses             : 0
% 0.21/0.39  #    Propositional clauses after purity: 0
% 0.21/0.39  #    Propositional unsat core size     : 0
% 0.21/0.39  #    Propositional preprocessing time  : 0.000
% 0.21/0.39  #    Propositional encoding time       : 0.000
% 0.21/0.39  #    Propositional solver time         : 0.000
% 0.21/0.39  #    Success case prop preproc time    : 0.000
% 0.21/0.39  #    Success case prop encoding time   : 0.000
% 0.21/0.39  #    Success case prop solver time     : 0.000
% 0.21/0.39  # Current number of processed clauses  : 49
% 0.21/0.39  #    Positive orientable unit clauses  : 10
% 0.21/0.39  #    Positive unorientable unit clauses: 0
% 0.21/0.39  #    Negative unit clauses             : 3
% 0.21/0.39  #    Non-unit-clauses                  : 36
% 0.21/0.39  # Current number of unprocessed clauses: 23
% 0.21/0.39  # ...number of literals in the above   : 242
% 0.21/0.39  # Current number of archived formulas  : 0
% 0.21/0.39  # Current number of archived clauses   : 65
% 0.21/0.39  # Clause-clause subsumption calls (NU) : 1879
% 0.21/0.39  # Rec. Clause-clause subsumption calls : 154
% 0.21/0.39  # Non-unit clause-clause subsumptions  : 69
% 0.21/0.39  # Unit Clause-clause subsumption calls : 8
% 0.21/0.39  # Rewrite failures with RHS unbound    : 0
% 0.21/0.39  # BW rewrite match attempts            : 0
% 0.21/0.39  # BW rewrite match successes           : 0
% 0.21/0.39  # Condensation attempts                : 0
% 0.21/0.39  # Condensation successes               : 0
% 0.21/0.39  # Termbank termtop insertions          : 9447
% 0.21/0.39  
% 0.21/0.39  # -------------------------------------------------
% 0.21/0.39  # User time                : 0.040 s
% 0.21/0.39  # System time              : 0.005 s
% 0.21/0.39  # Total time               : 0.045 s
% 0.21/0.39  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
