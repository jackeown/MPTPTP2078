%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1900+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:01 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   23 (  44 expanded)
%              Number of clauses        :   14 (  14 expanded)
%              Number of leaves         :    4 (  11 expanded)
%              Depth                    :    5
%              Number of atoms          :  124 ( 313 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   30 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t18_tdlat_3,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ( v1_tdlat_3(X1)
      <=> ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => v4_pre_topc(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_tdlat_3)).

fof(dt_k8_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => m1_subset_1(k8_relset_1(X1,X2,X3,X4),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relset_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_pre_topc)).

fof(t68_tex_2,conjecture,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & v1_tdlat_3(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( v2_pre_topc(X2)
            & l1_pre_topc(X2) )
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
             => v5_pre_topc(X3,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_tex_2)).

fof(c_0_4,plain,(
    ! [X14,X15] :
      ( ( ~ v1_tdlat_3(X14)
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))
        | v4_pre_topc(X15,X14)
        | ~ v2_pre_topc(X14)
        | ~ l1_pre_topc(X14) )
      & ( m1_subset_1(esk2_1(X14),k1_zfmisc_1(u1_struct_0(X14)))
        | v1_tdlat_3(X14)
        | ~ v2_pre_topc(X14)
        | ~ l1_pre_topc(X14) )
      & ( ~ v4_pre_topc(esk2_1(X14),X14)
        | v1_tdlat_3(X14)
        | ~ v2_pre_topc(X14)
        | ~ l1_pre_topc(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t18_tdlat_3])])])])])).

fof(c_0_5,plain,(
    ! [X10,X11,X12,X13] :
      ( ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))
      | m1_subset_1(k8_relset_1(X10,X11,X12,X13),k1_zfmisc_1(X10)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k8_relset_1])])).

fof(c_0_6,plain,(
    ! [X5,X6,X7,X8] :
      ( ( ~ v5_pre_topc(X7,X5,X6)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ v4_pre_topc(X8,X6)
        | v4_pre_topc(k8_relset_1(u1_struct_0(X5),u1_struct_0(X6),X7,X8),X5)
        | ~ v1_funct_1(X7)
        | ~ v1_funct_2(X7,u1_struct_0(X5),u1_struct_0(X6))
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X6))))
        | ~ l1_pre_topc(X6)
        | ~ l1_pre_topc(X5) )
      & ( m1_subset_1(esk1_3(X5,X6,X7),k1_zfmisc_1(u1_struct_0(X6)))
        | v5_pre_topc(X7,X5,X6)
        | ~ v1_funct_1(X7)
        | ~ v1_funct_2(X7,u1_struct_0(X5),u1_struct_0(X6))
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X6))))
        | ~ l1_pre_topc(X6)
        | ~ l1_pre_topc(X5) )
      & ( v4_pre_topc(esk1_3(X5,X6,X7),X6)
        | v5_pre_topc(X7,X5,X6)
        | ~ v1_funct_1(X7)
        | ~ v1_funct_2(X7,u1_struct_0(X5),u1_struct_0(X6))
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X6))))
        | ~ l1_pre_topc(X6)
        | ~ l1_pre_topc(X5) )
      & ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X5),u1_struct_0(X6),X7,esk1_3(X5,X6,X7)),X5)
        | v5_pre_topc(X7,X5,X6)
        | ~ v1_funct_1(X7)
        | ~ v1_funct_2(X7,u1_struct_0(X5),u1_struct_0(X6))
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X6))))
        | ~ l1_pre_topc(X6)
        | ~ l1_pre_topc(X5) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_pre_topc])])])])])).

cnf(c_0_7,plain,
    ( v4_pre_topc(X2,X1)
    | ~ v1_tdlat_3(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,plain,
    ( m1_subset_1(k8_relset_1(X2,X3,X1,X4),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1] :
        ( ( v2_pre_topc(X1)
          & v1_tdlat_3(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( v2_pre_topc(X2)
              & l1_pre_topc(X2) )
           => ! [X3] :
                ( ( v1_funct_1(X3)
                  & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
               => v5_pre_topc(X3,X1,X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t68_tex_2])).

cnf(c_0_10,plain,
    ( v5_pre_topc(X3,X1,X2)
    | ~ v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,esk1_3(X1,X2,X3)),X1)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( v4_pre_topc(k8_relset_1(u1_struct_0(X1),X2,X3,X4),X1)
    | ~ v1_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),X2)))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_7,c_0_8])).

fof(c_0_12,negated_conjecture,
    ( v2_pre_topc(esk3_0)
    & v1_tdlat_3(esk3_0)
    & l1_pre_topc(esk3_0)
    & v2_pre_topc(esk4_0)
    & l1_pre_topc(esk4_0)
    & v1_funct_1(esk5_0)
    & v1_funct_2(esk5_0,u1_struct_0(esk3_0),u1_struct_0(esk4_0))
    & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0))))
    & ~ v5_pre_topc(esk5_0,esk3_0,esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).

cnf(c_0_13,plain,
    ( v5_pre_topc(X1,X2,X3)
    | ~ v1_tdlat_3(X2)
    | ~ v2_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))
    | ~ v1_funct_1(X1)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_14,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_15,negated_conjecture,
    ( v1_tdlat_3(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( v1_funct_2(esk5_0,u1_struct_0(esk3_0),u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_21,negated_conjecture,
    ( ~ v5_pre_topc(esk5_0,esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_22,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15]),c_0_16]),c_0_17]),c_0_18]),c_0_19]),c_0_20])]),c_0_21]),
    [proof]).

%------------------------------------------------------------------------------
