%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:09:21 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   66 (1186 expanded)
%              Number of clauses        :   53 ( 399 expanded)
%              Number of leaves         :    6 ( 285 expanded)
%              Depth                    :   14
%              Number of atoms          :  253 (11231 expanded)
%              Number of equality atoms :    9 ( 721 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   30 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t63_pre_topc,conjecture,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( v2_pre_topc(X2)
            & l1_pre_topc(X2) )
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
             => ! [X4] :
                  ( ( v1_funct_1(X4)
                    & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))) )
                 => ( X3 = X4
                   => ( v5_pre_topc(X3,X1,X2)
                    <=> v5_pre_topc(X4,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_pre_topc)).

fof(redefinition_k8_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k8_relset_1(X1,X2,X3,X4) = k10_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

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

fof(t61_pre_topc,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( v4_pre_topc(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
        <=> ( v4_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_pre_topc)).

fof(dt_g1_pre_topc,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ( v1_pre_topc(g1_pre_topc(X1,X2))
        & l1_pre_topc(g1_pre_topc(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_g1_pre_topc)).

fof(dt_u1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1] :
        ( ( v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( v2_pre_topc(X2)
              & l1_pre_topc(X2) )
           => ! [X3] :
                ( ( v1_funct_1(X3)
                  & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
               => ! [X4] :
                    ( ( v1_funct_1(X4)
                      & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))) )
                   => ( X3 = X4
                     => ( v5_pre_topc(X3,X1,X2)
                      <=> v5_pre_topc(X4,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t63_pre_topc])).

fof(c_0_7,negated_conjecture,
    ( v2_pre_topc(esk2_0)
    & l1_pre_topc(esk2_0)
    & v2_pre_topc(esk3_0)
    & l1_pre_topc(esk3_0)
    & v1_funct_1(esk4_0)
    & v1_funct_2(esk4_0,u1_struct_0(esk2_0),u1_struct_0(esk3_0))
    & m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0))))
    & v1_funct_1(esk5_0)
    & v1_funct_2(esk5_0,u1_struct_0(esk2_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))))
    & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))))))
    & esk4_0 = esk5_0
    & ( ~ v5_pre_topc(esk4_0,esk2_0,esk3_0)
      | ~ v5_pre_topc(esk5_0,esk2_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))) )
    & ( v5_pre_topc(esk4_0,esk2_0,esk3_0)
      | v5_pre_topc(esk5_0,esk2_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).

fof(c_0_8,plain,(
    ! [X5,X6,X7,X8] :
      ( ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
      | k8_relset_1(X5,X6,X7,X8) = k10_relat_1(X7,X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k8_relset_1])])).

cnf(c_0_9,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_10,negated_conjecture,
    ( esk4_0 = esk5_0 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,plain,
    ( k8_relset_1(X2,X3,X1,X4) = k10_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

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

cnf(c_0_14,negated_conjecture,
    ( v1_funct_2(esk5_0,u1_struct_0(esk2_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_15,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))))) ),
    inference(rw,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_16,negated_conjecture,
    ( k10_relat_1(esk4_0,X1) = k8_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_17,plain,
    ( v4_pre_topc(k8_relset_1(u1_struct_0(X2),u1_struct_0(X3),X1,X4),X2)
    | ~ v5_pre_topc(X1,X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ v4_pre_topc(X4,X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( v1_funct_2(esk4_0,u1_struct_0(esk2_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))) ),
    inference(rw,[status(thm)],[c_0_14,c_0_10])).

cnf(c_0_19,negated_conjecture,
    ( k8_relset_1(u1_struct_0(esk2_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))),esk4_0,X1) = k8_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_15]),c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_21,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_22,negated_conjecture,
    ( v5_pre_topc(esk4_0,esk2_0,esk3_0)
    | v5_pre_topc(esk5_0,esk2_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_23,plain,(
    ! [X17,X18] :
      ( ( v4_pre_topc(X18,g1_pre_topc(u1_struct_0(X17),u1_pre_topc(X17)))
        | ~ v4_pre_topc(X18,X17)
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))
        | ~ v2_pre_topc(X17)
        | ~ l1_pre_topc(X17) )
      & ( m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X17),u1_pre_topc(X17)))))
        | ~ v4_pre_topc(X18,X17)
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))
        | ~ v2_pre_topc(X17)
        | ~ l1_pre_topc(X17) )
      & ( v4_pre_topc(X18,X17)
        | ~ v4_pre_topc(X18,g1_pre_topc(u1_struct_0(X17),u1_pre_topc(X17)))
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X17),u1_pre_topc(X17)))))
        | ~ v2_pre_topc(X17)
        | ~ l1_pre_topc(X17) )
      & ( m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))
        | ~ v4_pre_topc(X18,g1_pre_topc(u1_struct_0(X17),u1_pre_topc(X17)))
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X17),u1_pre_topc(X17)))))
        | ~ v2_pre_topc(X17)
        | ~ l1_pre_topc(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t61_pre_topc])])])])).

cnf(c_0_24,plain,
    ( v4_pre_topc(esk1_3(X1,X2,X3),X2)
    | v5_pre_topc(X3,X1,X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_25,negated_conjecture,
    ( v1_funct_2(esk4_0,u1_struct_0(esk2_0),u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_26,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_27,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X2)))
    | v5_pre_topc(X3,X1,X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_28,plain,(
    ! [X14,X15] :
      ( ( v1_pre_topc(g1_pre_topc(X14,X15))
        | ~ m1_subset_1(X15,k1_zfmisc_1(k1_zfmisc_1(X14))) )
      & ( l1_pre_topc(g1_pre_topc(X14,X15))
        | ~ m1_subset_1(X15,k1_zfmisc_1(k1_zfmisc_1(X14))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_g1_pre_topc])])])).

fof(c_0_29,plain,(
    ! [X16] :
      ( ~ l1_pre_topc(X16)
      | m1_subset_1(u1_pre_topc(X16),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X16)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).

cnf(c_0_30,negated_conjecture,
    ( v4_pre_topc(k8_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0,X1),esk2_0)
    | ~ v4_pre_topc(X1,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))
    | ~ v5_pre_topc(esk4_0,esk2_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19]),c_0_20]),c_0_21]),c_0_15])])).

cnf(c_0_31,negated_conjecture,
    ( v5_pre_topc(esk4_0,esk2_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))
    | v5_pre_topc(esk4_0,esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_22,c_0_10])).

cnf(c_0_32,plain,
    ( v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ v4_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_33,negated_conjecture,
    ( v4_pre_topc(esk1_3(esk2_0,esk3_0,esk4_0),esk3_0)
    | v5_pre_topc(esk4_0,esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_20]),c_0_26]),c_0_21]),c_0_12])])).

cnf(c_0_34,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_35,negated_conjecture,
    ( v5_pre_topc(esk4_0,esk2_0,esk3_0)
    | m1_subset_1(esk1_3(esk2_0,esk3_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_25]),c_0_20]),c_0_26]),c_0_21]),c_0_12])])).

cnf(c_0_36,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))
    | ~ v4_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_37,plain,
    ( v5_pre_topc(X3,X1,X2)
    | ~ v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,esk1_3(X1,X2,X3)),X1)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_38,plain,
    ( l1_pre_topc(g1_pre_topc(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_39,plain,
    ( m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_40,negated_conjecture,
    ( v4_pre_topc(k8_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0,X1),esk2_0)
    | v5_pre_topc(esk4_0,esk2_0,esk3_0)
    | ~ v4_pre_topc(X1,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))))) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_41,negated_conjecture,
    ( v4_pre_topc(esk1_3(esk2_0,esk3_0,esk4_0),g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))
    | v5_pre_topc(esk4_0,esk2_0,esk3_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34]),c_0_26])]),c_0_35])).

cnf(c_0_42,negated_conjecture,
    ( v5_pre_topc(esk4_0,esk2_0,esk3_0)
    | m1_subset_1(esk1_3(esk2_0,esk3_0,esk4_0),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_33]),c_0_34]),c_0_26])]),c_0_35])).

cnf(c_0_43,negated_conjecture,
    ( v5_pre_topc(esk4_0,esk2_0,esk3_0)
    | ~ v4_pre_topc(k8_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0,esk1_3(esk2_0,esk3_0,esk4_0)),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_25]),c_0_20]),c_0_26]),c_0_21]),c_0_12])])).

cnf(c_0_44,negated_conjecture,
    ( v4_pre_topc(esk1_3(esk2_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)),esk4_0),g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))
    | v5_pre_topc(esk4_0,esk2_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_18]),c_0_20]),c_0_21]),c_0_15])])).

cnf(c_0_45,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_46,negated_conjecture,
    ( v5_pre_topc(esk4_0,esk2_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))
    | m1_subset_1(esk1_3(esk2_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)),esk4_0),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_18]),c_0_20]),c_0_21]),c_0_15])])).

cnf(c_0_47,negated_conjecture,
    ( ~ v5_pre_topc(esk4_0,esk2_0,esk3_0)
    | ~ v5_pre_topc(esk5_0,esk2_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_48,negated_conjecture,
    ( v5_pre_topc(esk4_0,esk2_0,esk3_0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42]),c_0_43])).

cnf(c_0_49,plain,
    ( v4_pre_topc(X1,X2)
    | ~ v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_50,negated_conjecture,
    ( v4_pre_topc(esk1_3(esk2_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)),esk4_0),g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))
    | v5_pre_topc(esk4_0,esk2_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_26])])).

cnf(c_0_51,negated_conjecture,
    ( v5_pre_topc(esk4_0,esk2_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))
    | m1_subset_1(esk1_3(esk2_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)),esk4_0),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_45]),c_0_26])])).

cnf(c_0_52,negated_conjecture,
    ( ~ v5_pre_topc(esk4_0,esk2_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))
    | ~ v5_pre_topc(esk4_0,esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_47,c_0_10])).

cnf(c_0_53,negated_conjecture,
    ( v5_pre_topc(esk4_0,esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_45]),c_0_26])])).

cnf(c_0_54,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_55,negated_conjecture,
    ( v4_pre_topc(k8_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0,X1),esk2_0)
    | ~ v4_pre_topc(X1,esk3_0)
    | ~ v5_pre_topc(esk4_0,esk2_0,esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_25]),c_0_20]),c_0_26]),c_0_21]),c_0_12])])).

cnf(c_0_56,negated_conjecture,
    ( v4_pre_topc(esk1_3(esk2_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)),esk4_0),esk3_0)
    | v5_pre_topc(esk4_0,esk2_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_34]),c_0_26])]),c_0_51])).

cnf(c_0_57,negated_conjecture,
    ( ~ v5_pre_topc(esk4_0,esk2_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_53])])).

cnf(c_0_58,negated_conjecture,
    ( v5_pre_topc(esk4_0,esk2_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))
    | m1_subset_1(esk1_3(esk2_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)),esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_50]),c_0_34]),c_0_26])]),c_0_51])).

cnf(c_0_59,negated_conjecture,
    ( v4_pre_topc(k8_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0,X1),esk2_0)
    | ~ v4_pre_topc(X1,esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_55,c_0_53])])).

cnf(c_0_60,negated_conjecture,
    ( v4_pre_topc(esk1_3(esk2_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)),esk4_0),esk3_0) ),
    inference(sr,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_61,negated_conjecture,
    ( m1_subset_1(esk1_3(esk2_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)),esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(sr,[status(thm)],[c_0_58,c_0_57])).

cnf(c_0_62,negated_conjecture,
    ( v5_pre_topc(esk4_0,esk2_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))
    | ~ v4_pre_topc(k8_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0,esk1_3(esk2_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)),esk4_0)),esk2_0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_18]),c_0_19]),c_0_20]),c_0_21]),c_0_15])])).

cnf(c_0_63,negated_conjecture,
    ( v4_pre_topc(k8_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0,esk1_3(esk2_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)),esk4_0)),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_61])])).

cnf(c_0_64,negated_conjecture,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_62,c_0_63])]),c_0_57])).

cnf(c_0_65,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_45]),c_0_26])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:45:46 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.39  # AutoSched0-Mode selected heuristic G_E___208_B07_F1_SE_CS_SP_PS_S4d
% 0.13/0.39  # and selection function SelectCQIPrecWNTNp.
% 0.13/0.39  #
% 0.13/0.39  # Preprocessing time       : 0.032 s
% 0.13/0.39  # Presaturation interreduction done
% 0.13/0.39  
% 0.13/0.39  # Proof found!
% 0.13/0.39  # SZS status Theorem
% 0.13/0.39  # SZS output start CNFRefutation
% 0.13/0.39  fof(t63_pre_topc, conjecture, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:((v2_pre_topc(X2)&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))))=>(X3=X4=>(v5_pre_topc(X3,X1,X2)<=>v5_pre_topc(X4,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_pre_topc)).
% 0.13/0.39  fof(redefinition_k8_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k8_relset_1(X1,X2,X3,X4)=k10_relat_1(X3,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 0.13/0.39  fof(d12_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(l1_pre_topc(X2)=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>(v5_pre_topc(X3,X1,X2)<=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))=>(v4_pre_topc(X4,X2)=>v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4),X1))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_pre_topc)).
% 0.13/0.39  fof(t61_pre_topc, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:((v4_pre_topc(X2,X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))<=>(v4_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_pre_topc)).
% 0.13/0.39  fof(dt_g1_pre_topc, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>(v1_pre_topc(g1_pre_topc(X1,X2))&l1_pre_topc(g1_pre_topc(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_g1_pre_topc)).
% 0.13/0.39  fof(dt_u1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 0.13/0.39  fof(c_0_6, negated_conjecture, ~(![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:((v2_pre_topc(X2)&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))))=>(X3=X4=>(v5_pre_topc(X3,X1,X2)<=>v5_pre_topc(X4,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))))))), inference(assume_negation,[status(cth)],[t63_pre_topc])).
% 0.13/0.39  fof(c_0_7, negated_conjecture, ((v2_pre_topc(esk2_0)&l1_pre_topc(esk2_0))&((v2_pre_topc(esk3_0)&l1_pre_topc(esk3_0))&(((v1_funct_1(esk4_0)&v1_funct_2(esk4_0,u1_struct_0(esk2_0),u1_struct_0(esk3_0)))&m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0)))))&(((v1_funct_1(esk5_0)&v1_funct_2(esk5_0,u1_struct_0(esk2_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))))&m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))))))&(esk4_0=esk5_0&((~v5_pre_topc(esk4_0,esk2_0,esk3_0)|~v5_pre_topc(esk5_0,esk2_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))))&(v5_pre_topc(esk4_0,esk2_0,esk3_0)|v5_pre_topc(esk5_0,esk2_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).
% 0.13/0.39  fof(c_0_8, plain, ![X5, X6, X7, X8]:(~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))|k8_relset_1(X5,X6,X7,X8)=k10_relat_1(X7,X8)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k8_relset_1])])).
% 0.13/0.39  cnf(c_0_9, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))))))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.39  cnf(c_0_10, negated_conjecture, (esk4_0=esk5_0), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.39  cnf(c_0_11, plain, (k8_relset_1(X2,X3,X1,X4)=k10_relat_1(X1,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.39  cnf(c_0_12, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0))))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.39  fof(c_0_13, plain, ![X9, X10, X11, X12]:((~v5_pre_topc(X11,X9,X10)|(~m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X10)))|(~v4_pre_topc(X12,X10)|v4_pre_topc(k8_relset_1(u1_struct_0(X9),u1_struct_0(X10),X11,X12),X9)))|(~v1_funct_1(X11)|~v1_funct_2(X11,u1_struct_0(X9),u1_struct_0(X10))|~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X9),u1_struct_0(X10)))))|~l1_pre_topc(X10)|~l1_pre_topc(X9))&((m1_subset_1(esk1_3(X9,X10,X11),k1_zfmisc_1(u1_struct_0(X10)))|v5_pre_topc(X11,X9,X10)|(~v1_funct_1(X11)|~v1_funct_2(X11,u1_struct_0(X9),u1_struct_0(X10))|~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X9),u1_struct_0(X10)))))|~l1_pre_topc(X10)|~l1_pre_topc(X9))&((v4_pre_topc(esk1_3(X9,X10,X11),X10)|v5_pre_topc(X11,X9,X10)|(~v1_funct_1(X11)|~v1_funct_2(X11,u1_struct_0(X9),u1_struct_0(X10))|~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X9),u1_struct_0(X10)))))|~l1_pre_topc(X10)|~l1_pre_topc(X9))&(~v4_pre_topc(k8_relset_1(u1_struct_0(X9),u1_struct_0(X10),X11,esk1_3(X9,X10,X11)),X9)|v5_pre_topc(X11,X9,X10)|(~v1_funct_1(X11)|~v1_funct_2(X11,u1_struct_0(X9),u1_struct_0(X10))|~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X9),u1_struct_0(X10)))))|~l1_pre_topc(X10)|~l1_pre_topc(X9))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_pre_topc])])])])])).
% 0.13/0.39  cnf(c_0_14, negated_conjecture, (v1_funct_2(esk5_0,u1_struct_0(esk2_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.39  cnf(c_0_15, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))))))), inference(rw,[status(thm)],[c_0_9, c_0_10])).
% 0.13/0.39  cnf(c_0_16, negated_conjecture, (k10_relat_1(esk4_0,X1)=k8_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0,X1)), inference(spm,[status(thm)],[c_0_11, c_0_12])).
% 0.13/0.39  cnf(c_0_17, plain, (v4_pre_topc(k8_relset_1(u1_struct_0(X2),u1_struct_0(X3),X1,X4),X2)|~v5_pre_topc(X1,X2,X3)|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))|~v4_pre_topc(X4,X3)|~v1_funct_1(X1)|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))|~l1_pre_topc(X3)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.39  cnf(c_0_18, negated_conjecture, (v1_funct_2(esk4_0,u1_struct_0(esk2_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))))), inference(rw,[status(thm)],[c_0_14, c_0_10])).
% 0.13/0.39  cnf(c_0_19, negated_conjecture, (k8_relset_1(u1_struct_0(esk2_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))),esk4_0,X1)=k8_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_15]), c_0_16])).
% 0.13/0.39  cnf(c_0_20, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.39  cnf(c_0_21, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.39  cnf(c_0_22, negated_conjecture, (v5_pre_topc(esk4_0,esk2_0,esk3_0)|v5_pre_topc(esk5_0,esk2_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.39  fof(c_0_23, plain, ![X17, X18]:(((v4_pre_topc(X18,g1_pre_topc(u1_struct_0(X17),u1_pre_topc(X17)))|(~v4_pre_topc(X18,X17)|~m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17))))|(~v2_pre_topc(X17)|~l1_pre_topc(X17)))&(m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X17),u1_pre_topc(X17)))))|(~v4_pre_topc(X18,X17)|~m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17))))|(~v2_pre_topc(X17)|~l1_pre_topc(X17))))&((v4_pre_topc(X18,X17)|(~v4_pre_topc(X18,g1_pre_topc(u1_struct_0(X17),u1_pre_topc(X17)))|~m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X17),u1_pre_topc(X17))))))|(~v2_pre_topc(X17)|~l1_pre_topc(X17)))&(m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))|(~v4_pre_topc(X18,g1_pre_topc(u1_struct_0(X17),u1_pre_topc(X17)))|~m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X17),u1_pre_topc(X17))))))|(~v2_pre_topc(X17)|~l1_pre_topc(X17))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t61_pre_topc])])])])).
% 0.13/0.39  cnf(c_0_24, plain, (v4_pre_topc(esk1_3(X1,X2,X3),X2)|v5_pre_topc(X3,X1,X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.39  cnf(c_0_25, negated_conjecture, (v1_funct_2(esk4_0,u1_struct_0(esk2_0),u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.39  cnf(c_0_26, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.39  cnf(c_0_27, plain, (m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X2)))|v5_pre_topc(X3,X1,X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.39  fof(c_0_28, plain, ![X14, X15]:((v1_pre_topc(g1_pre_topc(X14,X15))|~m1_subset_1(X15,k1_zfmisc_1(k1_zfmisc_1(X14))))&(l1_pre_topc(g1_pre_topc(X14,X15))|~m1_subset_1(X15,k1_zfmisc_1(k1_zfmisc_1(X14))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_g1_pre_topc])])])).
% 0.13/0.39  fof(c_0_29, plain, ![X16]:(~l1_pre_topc(X16)|m1_subset_1(u1_pre_topc(X16),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X16))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).
% 0.13/0.39  cnf(c_0_30, negated_conjecture, (v4_pre_topc(k8_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0,X1),esk2_0)|~v4_pre_topc(X1,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))|~v5_pre_topc(esk4_0,esk2_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_19]), c_0_20]), c_0_21]), c_0_15])])).
% 0.13/0.39  cnf(c_0_31, negated_conjecture, (v5_pre_topc(esk4_0,esk2_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))|v5_pre_topc(esk4_0,esk2_0,esk3_0)), inference(rw,[status(thm)],[c_0_22, c_0_10])).
% 0.13/0.39  cnf(c_0_32, plain, (v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))|~v4_pre_topc(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.39  cnf(c_0_33, negated_conjecture, (v4_pre_topc(esk1_3(esk2_0,esk3_0,esk4_0),esk3_0)|v5_pre_topc(esk4_0,esk2_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_20]), c_0_26]), c_0_21]), c_0_12])])).
% 0.13/0.39  cnf(c_0_34, negated_conjecture, (v2_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.39  cnf(c_0_35, negated_conjecture, (v5_pre_topc(esk4_0,esk2_0,esk3_0)|m1_subset_1(esk1_3(esk2_0,esk3_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_25]), c_0_20]), c_0_26]), c_0_21]), c_0_12])])).
% 0.13/0.39  cnf(c_0_36, plain, (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))|~v4_pre_topc(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.39  cnf(c_0_37, plain, (v5_pre_topc(X3,X1,X2)|~v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,esk1_3(X1,X2,X3)),X1)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.39  cnf(c_0_38, plain, (l1_pre_topc(g1_pre_topc(X1,X2))|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.13/0.39  cnf(c_0_39, plain, (m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.13/0.39  cnf(c_0_40, negated_conjecture, (v4_pre_topc(k8_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0,X1),esk2_0)|v5_pre_topc(esk4_0,esk2_0,esk3_0)|~v4_pre_topc(X1,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))))), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.13/0.39  cnf(c_0_41, negated_conjecture, (v4_pre_topc(esk1_3(esk2_0,esk3_0,esk4_0),g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))|v5_pre_topc(esk4_0,esk2_0,esk3_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_34]), c_0_26])]), c_0_35])).
% 0.13/0.39  cnf(c_0_42, negated_conjecture, (v5_pre_topc(esk4_0,esk2_0,esk3_0)|m1_subset_1(esk1_3(esk2_0,esk3_0,esk4_0),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_33]), c_0_34]), c_0_26])]), c_0_35])).
% 0.13/0.39  cnf(c_0_43, negated_conjecture, (v5_pre_topc(esk4_0,esk2_0,esk3_0)|~v4_pre_topc(k8_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0,esk1_3(esk2_0,esk3_0,esk4_0)),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_25]), c_0_20]), c_0_26]), c_0_21]), c_0_12])])).
% 0.13/0.39  cnf(c_0_44, negated_conjecture, (v4_pre_topc(esk1_3(esk2_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)),esk4_0),g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))|v5_pre_topc(esk4_0,esk2_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_18]), c_0_20]), c_0_21]), c_0_15])])).
% 0.13/0.39  cnf(c_0_45, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.13/0.39  cnf(c_0_46, negated_conjecture, (v5_pre_topc(esk4_0,esk2_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))|m1_subset_1(esk1_3(esk2_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)),esk4_0),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_18]), c_0_20]), c_0_21]), c_0_15])])).
% 0.13/0.39  cnf(c_0_47, negated_conjecture, (~v5_pre_topc(esk4_0,esk2_0,esk3_0)|~v5_pre_topc(esk5_0,esk2_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.39  cnf(c_0_48, negated_conjecture, (v5_pre_topc(esk4_0,esk2_0,esk3_0)|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_42]), c_0_43])).
% 0.13/0.39  cnf(c_0_49, plain, (v4_pre_topc(X1,X2)|~v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.39  cnf(c_0_50, negated_conjecture, (v4_pre_topc(esk1_3(esk2_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)),esk4_0),g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))|v5_pre_topc(esk4_0,esk2_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_26])])).
% 0.13/0.39  cnf(c_0_51, negated_conjecture, (v5_pre_topc(esk4_0,esk2_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))|m1_subset_1(esk1_3(esk2_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)),esk4_0),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_45]), c_0_26])])).
% 0.13/0.39  cnf(c_0_52, negated_conjecture, (~v5_pre_topc(esk4_0,esk2_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))|~v5_pre_topc(esk4_0,esk2_0,esk3_0)), inference(rw,[status(thm)],[c_0_47, c_0_10])).
% 0.13/0.39  cnf(c_0_53, negated_conjecture, (v5_pre_topc(esk4_0,esk2_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_45]), c_0_26])])).
% 0.13/0.39  cnf(c_0_54, plain, (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.39  cnf(c_0_55, negated_conjecture, (v4_pre_topc(k8_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0,X1),esk2_0)|~v4_pre_topc(X1,esk3_0)|~v5_pre_topc(esk4_0,esk2_0,esk3_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_25]), c_0_20]), c_0_26]), c_0_21]), c_0_12])])).
% 0.13/0.39  cnf(c_0_56, negated_conjecture, (v4_pre_topc(esk1_3(esk2_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)),esk4_0),esk3_0)|v5_pre_topc(esk4_0,esk2_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_34]), c_0_26])]), c_0_51])).
% 0.13/0.39  cnf(c_0_57, negated_conjecture, (~v5_pre_topc(esk4_0,esk2_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_52, c_0_53])])).
% 0.13/0.39  cnf(c_0_58, negated_conjecture, (v5_pre_topc(esk4_0,esk2_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))|m1_subset_1(esk1_3(esk2_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)),esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_50]), c_0_34]), c_0_26])]), c_0_51])).
% 0.13/0.39  cnf(c_0_59, negated_conjecture, (v4_pre_topc(k8_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0,X1),esk2_0)|~v4_pre_topc(X1,esk3_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_55, c_0_53])])).
% 0.13/0.39  cnf(c_0_60, negated_conjecture, (v4_pre_topc(esk1_3(esk2_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)),esk4_0),esk3_0)), inference(sr,[status(thm)],[c_0_56, c_0_57])).
% 0.13/0.39  cnf(c_0_61, negated_conjecture, (m1_subset_1(esk1_3(esk2_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)),esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(sr,[status(thm)],[c_0_58, c_0_57])).
% 0.13/0.39  cnf(c_0_62, negated_conjecture, (v5_pre_topc(esk4_0,esk2_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))|~v4_pre_topc(k8_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0,esk1_3(esk2_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)),esk4_0)),esk2_0)|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_18]), c_0_19]), c_0_20]), c_0_21]), c_0_15])])).
% 0.13/0.39  cnf(c_0_63, negated_conjecture, (v4_pre_topc(k8_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0,esk1_3(esk2_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)),esk4_0)),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_61])])).
% 0.13/0.39  cnf(c_0_64, negated_conjecture, (~l1_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_62, c_0_63])]), c_0_57])).
% 0.13/0.39  cnf(c_0_65, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_45]), c_0_26])]), ['proof']).
% 0.13/0.39  # SZS output end CNFRefutation
% 0.13/0.39  # Proof object total steps             : 66
% 0.13/0.39  # Proof object clause steps            : 53
% 0.13/0.39  # Proof object formula steps           : 13
% 0.13/0.39  # Proof object conjectures             : 44
% 0.13/0.39  # Proof object clause conjectures      : 41
% 0.13/0.39  # Proof object formula conjectures     : 3
% 0.13/0.39  # Proof object initial clauses used    : 22
% 0.13/0.39  # Proof object initial formulas used   : 6
% 0.13/0.39  # Proof object generating inferences   : 22
% 0.13/0.39  # Proof object simplifying inferences  : 80
% 0.13/0.39  # Training examples: 0 positive, 0 negative
% 0.13/0.39  # Parsed axioms                        : 6
% 0.13/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.39  # Initial clauses                      : 25
% 0.13/0.39  # Removed in clause preprocessing      : 0
% 0.13/0.39  # Initial clauses in saturation        : 25
% 0.13/0.39  # Processed clauses                    : 85
% 0.13/0.39  # ...of these trivial                  : 2
% 0.13/0.39  # ...subsumed                          : 4
% 0.13/0.39  # ...remaining for further processing  : 79
% 0.13/0.39  # Other redundant clauses eliminated   : 0
% 0.13/0.39  # Clauses deleted for lack of memory   : 0
% 0.13/0.39  # Backward-subsumed                    : 5
% 0.13/0.39  # Backward-rewritten                   : 10
% 0.13/0.39  # Generated clauses                    : 44
% 0.13/0.39  # ...of the previous two non-trivial   : 44
% 0.13/0.39  # Contextual simplify-reflections      : 8
% 0.13/0.39  # Paramodulations                      : 40
% 0.13/0.39  # Factorizations                       : 0
% 0.13/0.39  # Equation resolutions                 : 0
% 0.13/0.39  # Propositional unsat checks           : 0
% 0.13/0.39  #    Propositional check models        : 0
% 0.13/0.39  #    Propositional check unsatisfiable : 0
% 0.13/0.39  #    Propositional clauses             : 0
% 0.13/0.39  #    Propositional clauses after purity: 0
% 0.13/0.39  #    Propositional unsat core size     : 0
% 0.13/0.39  #    Propositional preprocessing time  : 0.000
% 0.13/0.39  #    Propositional encoding time       : 0.000
% 0.13/0.39  #    Propositional solver time         : 0.000
% 0.13/0.39  #    Success case prop preproc time    : 0.000
% 0.13/0.39  #    Success case prop encoding time   : 0.000
% 0.13/0.39  #    Success case prop solver time     : 0.000
% 0.13/0.39  # Current number of processed clauses  : 36
% 0.13/0.39  #    Positive orientable unit clauses  : 18
% 0.13/0.39  #    Positive unorientable unit clauses: 0
% 0.13/0.39  #    Negative unit clauses             : 2
% 0.13/0.39  #    Non-unit-clauses                  : 16
% 0.13/0.39  # Current number of unprocessed clauses: 8
% 0.13/0.39  # ...number of literals in the above   : 27
% 0.13/0.39  # Current number of archived formulas  : 0
% 0.13/0.39  # Current number of archived clauses   : 43
% 0.13/0.39  # Clause-clause subsumption calls (NU) : 691
% 0.13/0.39  # Rec. Clause-clause subsumption calls : 147
% 0.13/0.39  # Non-unit clause-clause subsumptions  : 17
% 0.13/0.39  # Unit Clause-clause subsumption calls : 7
% 0.13/0.39  # Rewrite failures with RHS unbound    : 0
% 0.13/0.39  # BW rewrite match attempts            : 9
% 0.13/0.39  # BW rewrite match successes           : 2
% 0.13/0.39  # Condensation attempts                : 0
% 0.13/0.39  # Condensation successes               : 0
% 0.13/0.39  # Termbank termtop insertions          : 4245
% 0.13/0.39  
% 0.13/0.39  # -------------------------------------------------
% 0.13/0.39  # User time                : 0.037 s
% 0.13/0.39  # System time              : 0.004 s
% 0.13/0.39  # Total time               : 0.041 s
% 0.13/0.39  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
