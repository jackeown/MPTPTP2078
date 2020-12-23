%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:14:16 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 482 expanded)
%              Number of clauses        :   48 ( 143 expanded)
%              Number of leaves         :   13 ( 120 expanded)
%              Depth                    :   12
%              Number of atoms          :  384 (5441 expanded)
%              Number of equality atoms :   45 ( 714 expanded)
%              Maximal formula depth    :   24 (   5 average)
%              Maximal clause size      :   79 (   3 average)
%              Maximal term depth       :    4 (   2 average)

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

fof(t25_compts_1,axiom,(
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
                  & k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) = k2_struct_0(X2)
                  & v5_pre_topc(X3,X1,X2) )
               => ! [X4] :
                    ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                   => ( v4_pre_topc(X4,X1)
                     => v4_pre_topc(k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4),X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_compts_1)).

fof(t72_tops_2,axiom,(
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
              <=> ( k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) = k2_struct_0(X1)
                  & k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) = k2_struct_0(X2)
                  & v2_funct_1(X3)
                  & ! [X4] :
                      ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                     => ( v4_pre_topc(X4,X1)
                      <=> v4_pre_topc(k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4),X2) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_tops_2)).

fof(redefinition_k7_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k7_relset_1(X1,X2,X3,X4) = k9_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

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

fof(redefinition_k8_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k8_relset_1(X1,X2,X3,X4) = k10_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(dt_k7_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => m1_subset_1(k7_relset_1(X1,X2,X3,X4),k1_zfmisc_1(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relset_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(t164_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( ( r1_tarski(X1,k1_relat_1(X2))
          & v2_funct_1(X2) )
       => k10_relat_1(X2,k9_relat_1(X2,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t164_funct_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

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

fof(c_0_13,negated_conjecture,(
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

fof(c_0_14,plain,(
    ! [X49,X50,X51,X52] :
      ( ~ v2_pre_topc(X49)
      | ~ l1_pre_topc(X49)
      | v2_struct_0(X50)
      | ~ v2_pre_topc(X50)
      | ~ l1_pre_topc(X50)
      | ~ v1_funct_1(X51)
      | ~ v1_funct_2(X51,u1_struct_0(X49),u1_struct_0(X50))
      | ~ m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X49),u1_struct_0(X50))))
      | ~ v1_compts_1(X49)
      | ~ v8_pre_topc(X50)
      | k2_relset_1(u1_struct_0(X49),u1_struct_0(X50),X51) != k2_struct_0(X50)
      | ~ v5_pre_topc(X51,X49,X50)
      | ~ m1_subset_1(X52,k1_zfmisc_1(u1_struct_0(X49)))
      | ~ v4_pre_topc(X52,X49)
      | v4_pre_topc(k7_relset_1(u1_struct_0(X49),u1_struct_0(X50),X51,X52),X50) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t25_compts_1])])])])).

fof(c_0_15,negated_conjecture,
    ( v2_pre_topc(esk3_0)
    & l1_pre_topc(esk3_0)
    & ~ v2_struct_0(esk4_0)
    & v2_pre_topc(esk4_0)
    & l1_pre_topc(esk4_0)
    & v1_funct_1(esk5_0)
    & v1_funct_2(esk5_0,u1_struct_0(esk3_0),u1_struct_0(esk4_0))
    & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0))))
    & v1_compts_1(esk3_0)
    & v8_pre_topc(esk4_0)
    & k1_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0) = k2_struct_0(esk3_0)
    & k2_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0) = k2_struct_0(esk4_0)
    & v2_funct_1(esk5_0)
    & v5_pre_topc(esk5_0,esk3_0,esk4_0)
    & ~ v3_tops_2(esk5_0,esk3_0,esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])).

fof(c_0_16,plain,(
    ! [X44,X45,X46,X47] :
      ( ( k1_relset_1(u1_struct_0(X44),u1_struct_0(X45),X46) = k2_struct_0(X44)
        | ~ v3_tops_2(X46,X44,X45)
        | ~ v1_funct_1(X46)
        | ~ v1_funct_2(X46,u1_struct_0(X44),u1_struct_0(X45))
        | ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X44),u1_struct_0(X45))))
        | v2_struct_0(X45)
        | ~ l1_pre_topc(X45)
        | ~ l1_pre_topc(X44) )
      & ( k2_relset_1(u1_struct_0(X44),u1_struct_0(X45),X46) = k2_struct_0(X45)
        | ~ v3_tops_2(X46,X44,X45)
        | ~ v1_funct_1(X46)
        | ~ v1_funct_2(X46,u1_struct_0(X44),u1_struct_0(X45))
        | ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X44),u1_struct_0(X45))))
        | v2_struct_0(X45)
        | ~ l1_pre_topc(X45)
        | ~ l1_pre_topc(X44) )
      & ( v2_funct_1(X46)
        | ~ v3_tops_2(X46,X44,X45)
        | ~ v1_funct_1(X46)
        | ~ v1_funct_2(X46,u1_struct_0(X44),u1_struct_0(X45))
        | ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X44),u1_struct_0(X45))))
        | v2_struct_0(X45)
        | ~ l1_pre_topc(X45)
        | ~ l1_pre_topc(X44) )
      & ( ~ v4_pre_topc(X47,X44)
        | v4_pre_topc(k7_relset_1(u1_struct_0(X44),u1_struct_0(X45),X46,X47),X45)
        | ~ m1_subset_1(X47,k1_zfmisc_1(u1_struct_0(X44)))
        | ~ v3_tops_2(X46,X44,X45)
        | ~ v1_funct_1(X46)
        | ~ v1_funct_2(X46,u1_struct_0(X44),u1_struct_0(X45))
        | ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X44),u1_struct_0(X45))))
        | v2_struct_0(X45)
        | ~ l1_pre_topc(X45)
        | ~ l1_pre_topc(X44) )
      & ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(X44),u1_struct_0(X45),X46,X47),X45)
        | v4_pre_topc(X47,X44)
        | ~ m1_subset_1(X47,k1_zfmisc_1(u1_struct_0(X44)))
        | ~ v3_tops_2(X46,X44,X45)
        | ~ v1_funct_1(X46)
        | ~ v1_funct_2(X46,u1_struct_0(X44),u1_struct_0(X45))
        | ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X44),u1_struct_0(X45))))
        | v2_struct_0(X45)
        | ~ l1_pre_topc(X45)
        | ~ l1_pre_topc(X44) )
      & ( m1_subset_1(esk2_3(X44,X45,X46),k1_zfmisc_1(u1_struct_0(X44)))
        | k1_relset_1(u1_struct_0(X44),u1_struct_0(X45),X46) != k2_struct_0(X44)
        | k2_relset_1(u1_struct_0(X44),u1_struct_0(X45),X46) != k2_struct_0(X45)
        | ~ v2_funct_1(X46)
        | v3_tops_2(X46,X44,X45)
        | ~ v1_funct_1(X46)
        | ~ v1_funct_2(X46,u1_struct_0(X44),u1_struct_0(X45))
        | ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X44),u1_struct_0(X45))))
        | v2_struct_0(X45)
        | ~ l1_pre_topc(X45)
        | ~ l1_pre_topc(X44) )
      & ( ~ v4_pre_topc(esk2_3(X44,X45,X46),X44)
        | ~ v4_pre_topc(k7_relset_1(u1_struct_0(X44),u1_struct_0(X45),X46,esk2_3(X44,X45,X46)),X45)
        | k1_relset_1(u1_struct_0(X44),u1_struct_0(X45),X46) != k2_struct_0(X44)
        | k2_relset_1(u1_struct_0(X44),u1_struct_0(X45),X46) != k2_struct_0(X45)
        | ~ v2_funct_1(X46)
        | v3_tops_2(X46,X44,X45)
        | ~ v1_funct_1(X46)
        | ~ v1_funct_2(X46,u1_struct_0(X44),u1_struct_0(X45))
        | ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X44),u1_struct_0(X45))))
        | v2_struct_0(X45)
        | ~ l1_pre_topc(X45)
        | ~ l1_pre_topc(X44) )
      & ( v4_pre_topc(esk2_3(X44,X45,X46),X44)
        | v4_pre_topc(k7_relset_1(u1_struct_0(X44),u1_struct_0(X45),X46,esk2_3(X44,X45,X46)),X45)
        | k1_relset_1(u1_struct_0(X44),u1_struct_0(X45),X46) != k2_struct_0(X44)
        | k2_relset_1(u1_struct_0(X44),u1_struct_0(X45),X46) != k2_struct_0(X45)
        | ~ v2_funct_1(X46)
        | v3_tops_2(X46,X44,X45)
        | ~ v1_funct_1(X46)
        | ~ v1_funct_2(X46,u1_struct_0(X44),u1_struct_0(X45))
        | ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X44),u1_struct_0(X45))))
        | v2_struct_0(X45)
        | ~ l1_pre_topc(X45)
        | ~ l1_pre_topc(X44) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t72_tops_2])])])])])])).

cnf(c_0_17,plain,
    ( v2_struct_0(X2)
    | v4_pre_topc(k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4),X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v1_compts_1(X1)
    | ~ v8_pre_topc(X2)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) != k2_struct_0(X2)
    | ~ v5_pre_topc(X3,X1,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_pre_topc(X4,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,negated_conjecture,
    ( k2_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0) = k2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,negated_conjecture,
    ( v8_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,negated_conjecture,
    ( v1_compts_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,negated_conjecture,
    ( v2_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,negated_conjecture,
    ( v5_pre_topc(esk5_0,esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_25,negated_conjecture,
    ( v1_funct_2(esk5_0,u1_struct_0(esk3_0),u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_26,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_27,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_28,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_29,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_30,plain,
    ( m1_subset_1(esk2_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | v3_tops_2(X3,X1,X2)
    | v2_struct_0(X2)
    | k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) != k2_struct_0(X1)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) != k2_struct_0(X2)
    | ~ v2_funct_1(X3)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_31,negated_conjecture,
    ( k1_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0) = k2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_32,negated_conjecture,
    ( v2_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_33,negated_conjecture,
    ( ~ v3_tops_2(esk5_0,esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_34,plain,
    ( v3_tops_2(X3,X1,X2)
    | v2_struct_0(X2)
    | ~ v4_pre_topc(esk2_3(X1,X2,X3),X1)
    | ~ v4_pre_topc(k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,esk2_3(X1,X2,X3)),X2)
    | k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) != k2_struct_0(X1)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) != k2_struct_0(X2)
    | ~ v2_funct_1(X3)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_35,negated_conjecture,
    ( v4_pre_topc(k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,X1),esk4_0)
    | ~ v4_pre_topc(X1,esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19]),c_0_20]),c_0_21]),c_0_22]),c_0_23]),c_0_24]),c_0_25]),c_0_26]),c_0_27]),c_0_28])]),c_0_29])).

cnf(c_0_36,negated_conjecture,
    ( m1_subset_1(esk2_3(esk3_0,esk4_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_18]),c_0_31]),c_0_19]),c_0_25]),c_0_26]),c_0_27]),c_0_32]),c_0_28])]),c_0_33]),c_0_29])).

fof(c_0_37,plain,(
    ! [X25,X26,X27,X28] :
      ( ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26)))
      | k7_relset_1(X25,X26,X27,X28) = k9_relat_1(X27,X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).

fof(c_0_38,plain,(
    ! [X37,X38,X39,X40] :
      ( ( ~ v5_pre_topc(X39,X37,X38)
        | ~ m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X38)))
        | ~ v4_pre_topc(X40,X38)
        | v4_pre_topc(k8_relset_1(u1_struct_0(X37),u1_struct_0(X38),X39,X40),X37)
        | ~ v1_funct_1(X39)
        | ~ v1_funct_2(X39,u1_struct_0(X37),u1_struct_0(X38))
        | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X37),u1_struct_0(X38))))
        | ~ l1_pre_topc(X38)
        | ~ l1_pre_topc(X37) )
      & ( m1_subset_1(esk1_3(X37,X38,X39),k1_zfmisc_1(u1_struct_0(X38)))
        | v5_pre_topc(X39,X37,X38)
        | ~ v1_funct_1(X39)
        | ~ v1_funct_2(X39,u1_struct_0(X37),u1_struct_0(X38))
        | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X37),u1_struct_0(X38))))
        | ~ l1_pre_topc(X38)
        | ~ l1_pre_topc(X37) )
      & ( v4_pre_topc(esk1_3(X37,X38,X39),X38)
        | v5_pre_topc(X39,X37,X38)
        | ~ v1_funct_1(X39)
        | ~ v1_funct_2(X39,u1_struct_0(X37),u1_struct_0(X38))
        | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X37),u1_struct_0(X38))))
        | ~ l1_pre_topc(X38)
        | ~ l1_pre_topc(X37) )
      & ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X37),u1_struct_0(X38),X39,esk1_3(X37,X38,X39)),X37)
        | v5_pre_topc(X39,X37,X38)
        | ~ v1_funct_1(X39)
        | ~ v1_funct_2(X39,u1_struct_0(X37),u1_struct_0(X38))
        | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X37),u1_struct_0(X38))))
        | ~ l1_pre_topc(X38)
        | ~ l1_pre_topc(X37) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_pre_topc])])])])])).

fof(c_0_39,plain,(
    ! [X29,X30,X31,X32] :
      ( ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))
      | k8_relset_1(X29,X30,X31,X32) = k10_relat_1(X31,X32) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k8_relset_1])])).

fof(c_0_40,plain,(
    ! [X15,X16,X17,X18] :
      ( ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X15,X16)))
      | m1_subset_1(k7_relset_1(X15,X16,X17,X18),k1_zfmisc_1(X16)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relset_1])])).

cnf(c_0_41,plain,
    ( v4_pre_topc(esk2_3(X1,X2,X3),X1)
    | v4_pre_topc(k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,esk2_3(X1,X2,X3)),X2)
    | v3_tops_2(X3,X1,X2)
    | v2_struct_0(X2)
    | k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) != k2_struct_0(X1)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) != k2_struct_0(X2)
    | ~ v2_funct_1(X3)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_42,negated_conjecture,
    ( ~ v4_pre_topc(esk2_3(esk3_0,esk4_0,esk5_0),esk3_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_31]),c_0_19]),c_0_25]),c_0_26]),c_0_27]),c_0_32]),c_0_28]),c_0_18]),c_0_36])]),c_0_33]),c_0_29])).

cnf(c_0_43,plain,
    ( k7_relset_1(X2,X3,X1,X4) = k9_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_44,plain,
    ( v4_pre_topc(k8_relset_1(u1_struct_0(X2),u1_struct_0(X3),X1,X4),X2)
    | ~ v5_pre_topc(X1,X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ v4_pre_topc(X4,X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_45,plain,
    ( k8_relset_1(X2,X3,X1,X4) = k10_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_46,plain,
    ( m1_subset_1(k7_relset_1(X2,X3,X1,X4),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

fof(c_0_47,plain,(
    ! [X9,X10,X11] :
      ( ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))
      | v1_relat_1(X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_48,plain,(
    ! [X19,X20,X21] :
      ( ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))
      | k1_relset_1(X19,X20,X21) = k1_relat_1(X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_49,negated_conjecture,
    ( v4_pre_topc(k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,esk2_3(esk3_0,esk4_0,esk5_0)),esk4_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_18]),c_0_31]),c_0_19]),c_0_25]),c_0_26]),c_0_27]),c_0_32]),c_0_28])]),c_0_33]),c_0_29]),c_0_42])).

cnf(c_0_50,plain,
    ( k7_relset_1(X1,X2,X3,X4) = k7_relset_1(X5,X6,X3,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ),
    inference(spm,[status(thm)],[c_0_43,c_0_43])).

cnf(c_0_51,plain,
    ( v4_pre_topc(k10_relat_1(X1,X2),X3)
    | ~ v4_pre_topc(X2,X4)
    | ~ v5_pre_topc(X1,X3,X4)
    | ~ v1_funct_2(X1,u1_struct_0(X3),u1_struct_0(X4))
    | ~ l1_pre_topc(X4)
    | ~ l1_pre_topc(X3)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X4))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X4))) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

fof(c_0_52,plain,(
    ! [X7,X8] :
      ( ~ v1_relat_1(X8)
      | ~ v1_funct_1(X8)
      | ~ r1_tarski(X7,k1_relat_1(X8))
      | ~ v2_funct_1(X8)
      | k10_relat_1(X8,k9_relat_1(X8,X7)) = X7 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t164_funct_1])])).

cnf(c_0_53,plain,
    ( m1_subset_1(k9_relat_1(X1,X2),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X4,X3))) ),
    inference(spm,[status(thm)],[c_0_46,c_0_43])).

cnf(c_0_54,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_55,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_56,negated_conjecture,
    ( v4_pre_topc(k7_relset_1(X1,X2,esk5_0,esk2_3(esk3_0,esk4_0,esk5_0)),esk4_0)
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_18])])).

cnf(c_0_57,negated_conjecture,
    ( v4_pre_topc(k10_relat_1(esk5_0,X1),esk3_0)
    | ~ v4_pre_topc(X1,esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_18]),c_0_24]),c_0_25]),c_0_26]),c_0_27]),c_0_28])])).

cnf(c_0_58,plain,
    ( k10_relat_1(X1,k9_relat_1(X1,X2)) = X2
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r1_tarski(X2,k1_relat_1(X1))
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_59,negated_conjecture,
    ( m1_subset_1(k9_relat_1(esk5_0,X1),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_53,c_0_18])).

cnf(c_0_60,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(spm,[status(thm)],[c_0_54,c_0_18])).

cnf(c_0_61,negated_conjecture,
    ( k1_relat_1(esk5_0) = k2_struct_0(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_55]),c_0_18])])).

cnf(c_0_62,negated_conjecture,
    ( v4_pre_topc(k9_relat_1(esk5_0,esk2_3(esk3_0,esk4_0,esk5_0)),esk4_0)
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_56,c_0_43])).

cnf(c_0_63,negated_conjecture,
    ( v4_pre_topc(X1,esk3_0)
    | ~ v4_pre_topc(k9_relat_1(esk5_0,X1),esk4_0)
    | ~ r1_tarski(X1,k2_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_59]),c_0_32]),c_0_28]),c_0_60]),c_0_61])])).

cnf(c_0_64,negated_conjecture,
    ( v4_pre_topc(k9_relat_1(esk5_0,esk2_3(esk3_0,esk4_0,esk5_0)),esk4_0) ),
    inference(spm,[status(thm)],[c_0_62,c_0_18])).

fof(c_0_65,plain,(
    ! [X5,X6] :
      ( ( ~ m1_subset_1(X5,k1_zfmisc_1(X6))
        | r1_tarski(X5,X6) )
      & ( ~ r1_tarski(X5,X6)
        | m1_subset_1(X5,k1_zfmisc_1(X6)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_66,plain,(
    ! [X42] :
      ( ~ l1_struct_0(X42)
      | k2_struct_0(X42) = u1_struct_0(X42) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

fof(c_0_67,plain,(
    ! [X43] :
      ( ~ l1_pre_topc(X43)
      | l1_struct_0(X43) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_68,negated_conjecture,
    ( ~ r1_tarski(esk2_3(esk3_0,esk4_0,esk5_0),k2_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_42])).

cnf(c_0_69,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_70,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_71,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_72,negated_conjecture,
    ( ~ m1_subset_1(esk2_3(esk3_0,esk4_0,esk5_0),k1_zfmisc_1(k2_struct_0(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_73,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_74,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_36]),c_0_27])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:21:07 EST 2020
% 0.18/0.33  % CPUTime    : 
% 0.18/0.33  # Version: 2.5pre002
% 0.18/0.33  # No SInE strategy applied
% 0.18/0.33  # Trying AutoSched0 for 299 seconds
% 0.18/0.40  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_AE_CS_SP_PS_S0V
% 0.18/0.40  # and selection function PSelectComplexExceptRRHorn.
% 0.18/0.40  #
% 0.18/0.40  # Preprocessing time       : 0.029 s
% 0.18/0.40  # Presaturation interreduction done
% 0.18/0.40  
% 0.18/0.40  # Proof found!
% 0.18/0.40  # SZS status Theorem
% 0.18/0.40  # SZS output start CNFRefutation
% 0.18/0.40  fof(t26_compts_1, conjecture, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>((((((v1_compts_1(X1)&v8_pre_topc(X2))&k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)=k2_struct_0(X1))&k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)=k2_struct_0(X2))&v2_funct_1(X3))&v5_pre_topc(X3,X1,X2))=>v3_tops_2(X3,X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_compts_1)).
% 0.18/0.40  fof(t25_compts_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>((((v1_compts_1(X1)&v8_pre_topc(X2))&k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)=k2_struct_0(X2))&v5_pre_topc(X3,X1,X2))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>(v4_pre_topc(X4,X1)=>v4_pre_topc(k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4),X2))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_compts_1)).
% 0.18/0.40  fof(t72_tops_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:((~(v2_struct_0(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>(v3_tops_2(X3,X1,X2)<=>(((k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)=k2_struct_0(X1)&k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)=k2_struct_0(X2))&v2_funct_1(X3))&![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>(v4_pre_topc(X4,X1)<=>v4_pre_topc(k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4),X2)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_tops_2)).
% 0.18/0.40  fof(redefinition_k7_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k7_relset_1(X1,X2,X3,X4)=k9_relat_1(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 0.18/0.40  fof(d12_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(l1_pre_topc(X2)=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>(v5_pre_topc(X3,X1,X2)<=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))=>(v4_pre_topc(X4,X2)=>v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4),X1))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_pre_topc)).
% 0.18/0.40  fof(redefinition_k8_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k8_relset_1(X1,X2,X3,X4)=k10_relat_1(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 0.18/0.40  fof(dt_k7_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>m1_subset_1(k7_relset_1(X1,X2,X3,X4),k1_zfmisc_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relset_1)).
% 0.18/0.40  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.18/0.40  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.18/0.40  fof(t164_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>((r1_tarski(X1,k1_relat_1(X2))&v2_funct_1(X2))=>k10_relat_1(X2,k9_relat_1(X2,X1))=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t164_funct_1)).
% 0.18/0.40  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.18/0.40  fof(d3_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>k2_struct_0(X1)=u1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 0.18/0.40  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.18/0.40  fof(c_0_13, negated_conjecture, ~(![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>((((((v1_compts_1(X1)&v8_pre_topc(X2))&k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)=k2_struct_0(X1))&k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)=k2_struct_0(X2))&v2_funct_1(X3))&v5_pre_topc(X3,X1,X2))=>v3_tops_2(X3,X1,X2)))))), inference(assume_negation,[status(cth)],[t26_compts_1])).
% 0.18/0.40  fof(c_0_14, plain, ![X49, X50, X51, X52]:(~v2_pre_topc(X49)|~l1_pre_topc(X49)|(v2_struct_0(X50)|~v2_pre_topc(X50)|~l1_pre_topc(X50)|(~v1_funct_1(X51)|~v1_funct_2(X51,u1_struct_0(X49),u1_struct_0(X50))|~m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X49),u1_struct_0(X50))))|(~v1_compts_1(X49)|~v8_pre_topc(X50)|k2_relset_1(u1_struct_0(X49),u1_struct_0(X50),X51)!=k2_struct_0(X50)|~v5_pre_topc(X51,X49,X50)|(~m1_subset_1(X52,k1_zfmisc_1(u1_struct_0(X49)))|(~v4_pre_topc(X52,X49)|v4_pre_topc(k7_relset_1(u1_struct_0(X49),u1_struct_0(X50),X51,X52),X50))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t25_compts_1])])])])).
% 0.18/0.40  fof(c_0_15, negated_conjecture, ((v2_pre_topc(esk3_0)&l1_pre_topc(esk3_0))&(((~v2_struct_0(esk4_0)&v2_pre_topc(esk4_0))&l1_pre_topc(esk4_0))&(((v1_funct_1(esk5_0)&v1_funct_2(esk5_0,u1_struct_0(esk3_0),u1_struct_0(esk4_0)))&m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0)))))&((((((v1_compts_1(esk3_0)&v8_pre_topc(esk4_0))&k1_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0)=k2_struct_0(esk3_0))&k2_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0)=k2_struct_0(esk4_0))&v2_funct_1(esk5_0))&v5_pre_topc(esk5_0,esk3_0,esk4_0))&~v3_tops_2(esk5_0,esk3_0,esk4_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])).
% 0.18/0.40  fof(c_0_16, plain, ![X44, X45, X46, X47]:(((((k1_relset_1(u1_struct_0(X44),u1_struct_0(X45),X46)=k2_struct_0(X44)|~v3_tops_2(X46,X44,X45)|(~v1_funct_1(X46)|~v1_funct_2(X46,u1_struct_0(X44),u1_struct_0(X45))|~m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X44),u1_struct_0(X45)))))|(v2_struct_0(X45)|~l1_pre_topc(X45))|~l1_pre_topc(X44))&(k2_relset_1(u1_struct_0(X44),u1_struct_0(X45),X46)=k2_struct_0(X45)|~v3_tops_2(X46,X44,X45)|(~v1_funct_1(X46)|~v1_funct_2(X46,u1_struct_0(X44),u1_struct_0(X45))|~m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X44),u1_struct_0(X45)))))|(v2_struct_0(X45)|~l1_pre_topc(X45))|~l1_pre_topc(X44)))&(v2_funct_1(X46)|~v3_tops_2(X46,X44,X45)|(~v1_funct_1(X46)|~v1_funct_2(X46,u1_struct_0(X44),u1_struct_0(X45))|~m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X44),u1_struct_0(X45)))))|(v2_struct_0(X45)|~l1_pre_topc(X45))|~l1_pre_topc(X44)))&((~v4_pre_topc(X47,X44)|v4_pre_topc(k7_relset_1(u1_struct_0(X44),u1_struct_0(X45),X46,X47),X45)|~m1_subset_1(X47,k1_zfmisc_1(u1_struct_0(X44)))|~v3_tops_2(X46,X44,X45)|(~v1_funct_1(X46)|~v1_funct_2(X46,u1_struct_0(X44),u1_struct_0(X45))|~m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X44),u1_struct_0(X45)))))|(v2_struct_0(X45)|~l1_pre_topc(X45))|~l1_pre_topc(X44))&(~v4_pre_topc(k7_relset_1(u1_struct_0(X44),u1_struct_0(X45),X46,X47),X45)|v4_pre_topc(X47,X44)|~m1_subset_1(X47,k1_zfmisc_1(u1_struct_0(X44)))|~v3_tops_2(X46,X44,X45)|(~v1_funct_1(X46)|~v1_funct_2(X46,u1_struct_0(X44),u1_struct_0(X45))|~m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X44),u1_struct_0(X45)))))|(v2_struct_0(X45)|~l1_pre_topc(X45))|~l1_pre_topc(X44))))&((m1_subset_1(esk2_3(X44,X45,X46),k1_zfmisc_1(u1_struct_0(X44)))|(k1_relset_1(u1_struct_0(X44),u1_struct_0(X45),X46)!=k2_struct_0(X44)|k2_relset_1(u1_struct_0(X44),u1_struct_0(X45),X46)!=k2_struct_0(X45)|~v2_funct_1(X46))|v3_tops_2(X46,X44,X45)|(~v1_funct_1(X46)|~v1_funct_2(X46,u1_struct_0(X44),u1_struct_0(X45))|~m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X44),u1_struct_0(X45)))))|(v2_struct_0(X45)|~l1_pre_topc(X45))|~l1_pre_topc(X44))&((~v4_pre_topc(esk2_3(X44,X45,X46),X44)|~v4_pre_topc(k7_relset_1(u1_struct_0(X44),u1_struct_0(X45),X46,esk2_3(X44,X45,X46)),X45)|(k1_relset_1(u1_struct_0(X44),u1_struct_0(X45),X46)!=k2_struct_0(X44)|k2_relset_1(u1_struct_0(X44),u1_struct_0(X45),X46)!=k2_struct_0(X45)|~v2_funct_1(X46))|v3_tops_2(X46,X44,X45)|(~v1_funct_1(X46)|~v1_funct_2(X46,u1_struct_0(X44),u1_struct_0(X45))|~m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X44),u1_struct_0(X45)))))|(v2_struct_0(X45)|~l1_pre_topc(X45))|~l1_pre_topc(X44))&(v4_pre_topc(esk2_3(X44,X45,X46),X44)|v4_pre_topc(k7_relset_1(u1_struct_0(X44),u1_struct_0(X45),X46,esk2_3(X44,X45,X46)),X45)|(k1_relset_1(u1_struct_0(X44),u1_struct_0(X45),X46)!=k2_struct_0(X44)|k2_relset_1(u1_struct_0(X44),u1_struct_0(X45),X46)!=k2_struct_0(X45)|~v2_funct_1(X46))|v3_tops_2(X46,X44,X45)|(~v1_funct_1(X46)|~v1_funct_2(X46,u1_struct_0(X44),u1_struct_0(X45))|~m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X44),u1_struct_0(X45)))))|(v2_struct_0(X45)|~l1_pre_topc(X45))|~l1_pre_topc(X44))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t72_tops_2])])])])])])).
% 0.18/0.40  cnf(c_0_17, plain, (v2_struct_0(X2)|v4_pre_topc(k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4),X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~v1_compts_1(X1)|~v8_pre_topc(X2)|k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)!=k2_struct_0(X2)|~v5_pre_topc(X3,X1,X2)|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))|~v4_pre_topc(X4,X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.18/0.40  cnf(c_0_18, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0))))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.40  cnf(c_0_19, negated_conjecture, (k2_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0)=k2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.40  cnf(c_0_20, negated_conjecture, (v8_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.40  cnf(c_0_21, negated_conjecture, (v1_compts_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.40  cnf(c_0_22, negated_conjecture, (v2_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.40  cnf(c_0_23, negated_conjecture, (v2_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.40  cnf(c_0_24, negated_conjecture, (v5_pre_topc(esk5_0,esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.40  cnf(c_0_25, negated_conjecture, (v1_funct_2(esk5_0,u1_struct_0(esk3_0),u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.40  cnf(c_0_26, negated_conjecture, (l1_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.40  cnf(c_0_27, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.40  cnf(c_0_28, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.40  cnf(c_0_29, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.40  cnf(c_0_30, plain, (m1_subset_1(esk2_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))|v3_tops_2(X3,X1,X2)|v2_struct_0(X2)|k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)!=k2_struct_0(X1)|k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)!=k2_struct_0(X2)|~v2_funct_1(X3)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.18/0.40  cnf(c_0_31, negated_conjecture, (k1_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0)=k2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.40  cnf(c_0_32, negated_conjecture, (v2_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.40  cnf(c_0_33, negated_conjecture, (~v3_tops_2(esk5_0,esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.40  cnf(c_0_34, plain, (v3_tops_2(X3,X1,X2)|v2_struct_0(X2)|~v4_pre_topc(esk2_3(X1,X2,X3),X1)|~v4_pre_topc(k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,esk2_3(X1,X2,X3)),X2)|k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)!=k2_struct_0(X1)|k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)!=k2_struct_0(X2)|~v2_funct_1(X3)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.18/0.40  cnf(c_0_35, negated_conjecture, (v4_pre_topc(k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,X1),esk4_0)|~v4_pre_topc(X1,esk3_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_19]), c_0_20]), c_0_21]), c_0_22]), c_0_23]), c_0_24]), c_0_25]), c_0_26]), c_0_27]), c_0_28])]), c_0_29])).
% 0.18/0.40  cnf(c_0_36, negated_conjecture, (m1_subset_1(esk2_3(esk3_0,esk4_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_18]), c_0_31]), c_0_19]), c_0_25]), c_0_26]), c_0_27]), c_0_32]), c_0_28])]), c_0_33]), c_0_29])).
% 0.18/0.40  fof(c_0_37, plain, ![X25, X26, X27, X28]:(~m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26)))|k7_relset_1(X25,X26,X27,X28)=k9_relat_1(X27,X28)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).
% 0.18/0.40  fof(c_0_38, plain, ![X37, X38, X39, X40]:((~v5_pre_topc(X39,X37,X38)|(~m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X38)))|(~v4_pre_topc(X40,X38)|v4_pre_topc(k8_relset_1(u1_struct_0(X37),u1_struct_0(X38),X39,X40),X37)))|(~v1_funct_1(X39)|~v1_funct_2(X39,u1_struct_0(X37),u1_struct_0(X38))|~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X37),u1_struct_0(X38)))))|~l1_pre_topc(X38)|~l1_pre_topc(X37))&((m1_subset_1(esk1_3(X37,X38,X39),k1_zfmisc_1(u1_struct_0(X38)))|v5_pre_topc(X39,X37,X38)|(~v1_funct_1(X39)|~v1_funct_2(X39,u1_struct_0(X37),u1_struct_0(X38))|~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X37),u1_struct_0(X38)))))|~l1_pre_topc(X38)|~l1_pre_topc(X37))&((v4_pre_topc(esk1_3(X37,X38,X39),X38)|v5_pre_topc(X39,X37,X38)|(~v1_funct_1(X39)|~v1_funct_2(X39,u1_struct_0(X37),u1_struct_0(X38))|~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X37),u1_struct_0(X38)))))|~l1_pre_topc(X38)|~l1_pre_topc(X37))&(~v4_pre_topc(k8_relset_1(u1_struct_0(X37),u1_struct_0(X38),X39,esk1_3(X37,X38,X39)),X37)|v5_pre_topc(X39,X37,X38)|(~v1_funct_1(X39)|~v1_funct_2(X39,u1_struct_0(X37),u1_struct_0(X38))|~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X37),u1_struct_0(X38)))))|~l1_pre_topc(X38)|~l1_pre_topc(X37))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_pre_topc])])])])])).
% 0.18/0.40  fof(c_0_39, plain, ![X29, X30, X31, X32]:(~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))|k8_relset_1(X29,X30,X31,X32)=k10_relat_1(X31,X32)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k8_relset_1])])).
% 0.18/0.40  fof(c_0_40, plain, ![X15, X16, X17, X18]:(~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X15,X16)))|m1_subset_1(k7_relset_1(X15,X16,X17,X18),k1_zfmisc_1(X16))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relset_1])])).
% 0.18/0.40  cnf(c_0_41, plain, (v4_pre_topc(esk2_3(X1,X2,X3),X1)|v4_pre_topc(k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,esk2_3(X1,X2,X3)),X2)|v3_tops_2(X3,X1,X2)|v2_struct_0(X2)|k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)!=k2_struct_0(X1)|k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)!=k2_struct_0(X2)|~v2_funct_1(X3)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.18/0.40  cnf(c_0_42, negated_conjecture, (~v4_pre_topc(esk2_3(esk3_0,esk4_0,esk5_0),esk3_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_31]), c_0_19]), c_0_25]), c_0_26]), c_0_27]), c_0_32]), c_0_28]), c_0_18]), c_0_36])]), c_0_33]), c_0_29])).
% 0.18/0.40  cnf(c_0_43, plain, (k7_relset_1(X2,X3,X1,X4)=k9_relat_1(X1,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.18/0.40  cnf(c_0_44, plain, (v4_pre_topc(k8_relset_1(u1_struct_0(X2),u1_struct_0(X3),X1,X4),X2)|~v5_pre_topc(X1,X2,X3)|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))|~v4_pre_topc(X4,X3)|~v1_funct_1(X1)|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))|~l1_pre_topc(X3)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.18/0.40  cnf(c_0_45, plain, (k8_relset_1(X2,X3,X1,X4)=k10_relat_1(X1,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.18/0.40  cnf(c_0_46, plain, (m1_subset_1(k7_relset_1(X2,X3,X1,X4),k1_zfmisc_1(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.18/0.40  fof(c_0_47, plain, ![X9, X10, X11]:(~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))|v1_relat_1(X11)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.18/0.40  fof(c_0_48, plain, ![X19, X20, X21]:(~m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))|k1_relset_1(X19,X20,X21)=k1_relat_1(X21)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.18/0.40  cnf(c_0_49, negated_conjecture, (v4_pre_topc(k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,esk2_3(esk3_0,esk4_0,esk5_0)),esk4_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_18]), c_0_31]), c_0_19]), c_0_25]), c_0_26]), c_0_27]), c_0_32]), c_0_28])]), c_0_33]), c_0_29]), c_0_42])).
% 0.18/0.40  cnf(c_0_50, plain, (k7_relset_1(X1,X2,X3,X4)=k7_relset_1(X5,X6,X3,X4)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))), inference(spm,[status(thm)],[c_0_43, c_0_43])).
% 0.18/0.40  cnf(c_0_51, plain, (v4_pre_topc(k10_relat_1(X1,X2),X3)|~v4_pre_topc(X2,X4)|~v5_pre_topc(X1,X3,X4)|~v1_funct_2(X1,u1_struct_0(X3),u1_struct_0(X4))|~l1_pre_topc(X4)|~l1_pre_topc(X3)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X4))))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X4)))), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.18/0.40  fof(c_0_52, plain, ![X7, X8]:(~v1_relat_1(X8)|~v1_funct_1(X8)|(~r1_tarski(X7,k1_relat_1(X8))|~v2_funct_1(X8)|k10_relat_1(X8,k9_relat_1(X8,X7))=X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t164_funct_1])])).
% 0.18/0.40  cnf(c_0_53, plain, (m1_subset_1(k9_relat_1(X1,X2),k1_zfmisc_1(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X4,X3)))), inference(spm,[status(thm)],[c_0_46, c_0_43])).
% 0.18/0.40  cnf(c_0_54, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.18/0.40  cnf(c_0_55, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.18/0.40  cnf(c_0_56, negated_conjecture, (v4_pre_topc(k7_relset_1(X1,X2,esk5_0,esk2_3(esk3_0,esk4_0,esk5_0)),esk4_0)|~m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_18])])).
% 0.18/0.40  cnf(c_0_57, negated_conjecture, (v4_pre_topc(k10_relat_1(esk5_0,X1),esk3_0)|~v4_pre_topc(X1,esk4_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_18]), c_0_24]), c_0_25]), c_0_26]), c_0_27]), c_0_28])])).
% 0.18/0.40  cnf(c_0_58, plain, (k10_relat_1(X1,k9_relat_1(X1,X2))=X2|~v1_relat_1(X1)|~v1_funct_1(X1)|~r1_tarski(X2,k1_relat_1(X1))|~v2_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.18/0.40  cnf(c_0_59, negated_conjecture, (m1_subset_1(k9_relat_1(esk5_0,X1),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(spm,[status(thm)],[c_0_53, c_0_18])).
% 0.18/0.40  cnf(c_0_60, negated_conjecture, (v1_relat_1(esk5_0)), inference(spm,[status(thm)],[c_0_54, c_0_18])).
% 0.18/0.40  cnf(c_0_61, negated_conjecture, (k1_relat_1(esk5_0)=k2_struct_0(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_55]), c_0_18])])).
% 0.18/0.40  cnf(c_0_62, negated_conjecture, (v4_pre_topc(k9_relat_1(esk5_0,esk2_3(esk3_0,esk4_0,esk5_0)),esk4_0)|~m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(spm,[status(thm)],[c_0_56, c_0_43])).
% 0.18/0.40  cnf(c_0_63, negated_conjecture, (v4_pre_topc(X1,esk3_0)|~v4_pre_topc(k9_relat_1(esk5_0,X1),esk4_0)|~r1_tarski(X1,k2_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_59]), c_0_32]), c_0_28]), c_0_60]), c_0_61])])).
% 0.18/0.40  cnf(c_0_64, negated_conjecture, (v4_pre_topc(k9_relat_1(esk5_0,esk2_3(esk3_0,esk4_0,esk5_0)),esk4_0)), inference(spm,[status(thm)],[c_0_62, c_0_18])).
% 0.18/0.40  fof(c_0_65, plain, ![X5, X6]:((~m1_subset_1(X5,k1_zfmisc_1(X6))|r1_tarski(X5,X6))&(~r1_tarski(X5,X6)|m1_subset_1(X5,k1_zfmisc_1(X6)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.18/0.40  fof(c_0_66, plain, ![X42]:(~l1_struct_0(X42)|k2_struct_0(X42)=u1_struct_0(X42)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).
% 0.18/0.40  fof(c_0_67, plain, ![X43]:(~l1_pre_topc(X43)|l1_struct_0(X43)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.18/0.40  cnf(c_0_68, negated_conjecture, (~r1_tarski(esk2_3(esk3_0,esk4_0,esk5_0),k2_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_42])).
% 0.18/0.40  cnf(c_0_69, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.18/0.40  cnf(c_0_70, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_66])).
% 0.18/0.40  cnf(c_0_71, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.18/0.40  cnf(c_0_72, negated_conjecture, (~m1_subset_1(esk2_3(esk3_0,esk4_0,esk5_0),k1_zfmisc_1(k2_struct_0(esk3_0)))), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 0.18/0.40  cnf(c_0_73, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_70, c_0_71])).
% 0.18/0.40  cnf(c_0_74, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_73]), c_0_36]), c_0_27])]), ['proof']).
% 0.18/0.40  # SZS output end CNFRefutation
% 0.18/0.40  # Proof object total steps             : 75
% 0.18/0.40  # Proof object clause steps            : 48
% 0.18/0.40  # Proof object formula steps           : 27
% 0.18/0.40  # Proof object conjectures             : 33
% 0.18/0.40  # Proof object clause conjectures      : 30
% 0.18/0.40  # Proof object formula conjectures     : 3
% 0.18/0.40  # Proof object initial clauses used    : 29
% 0.18/0.40  # Proof object initial formulas used   : 13
% 0.18/0.40  # Proof object generating inferences   : 19
% 0.18/0.40  # Proof object simplifying inferences  : 65
% 0.18/0.40  # Training examples: 0 positive, 0 negative
% 0.18/0.40  # Parsed axioms                        : 17
% 0.18/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.40  # Initial clauses                      : 45
% 0.18/0.40  # Removed in clause preprocessing      : 0
% 0.18/0.40  # Initial clauses in saturation        : 45
% 0.18/0.40  # Processed clauses                    : 246
% 0.18/0.40  # ...of these trivial                  : 0
% 0.18/0.40  # ...subsumed                          : 77
% 0.18/0.40  # ...remaining for further processing  : 169
% 0.18/0.40  # Other redundant clauses eliminated   : 0
% 0.18/0.40  # Clauses deleted for lack of memory   : 0
% 0.18/0.40  # Backward-subsumed                    : 3
% 0.18/0.40  # Backward-rewritten                   : 0
% 0.18/0.40  # Generated clauses                    : 319
% 0.18/0.40  # ...of the previous two non-trivial   : 298
% 0.18/0.40  # Contextual simplify-reflections      : 9
% 0.18/0.40  # Paramodulations                      : 319
% 0.18/0.40  # Factorizations                       : 0
% 0.18/0.40  # Equation resolutions                 : 0
% 0.18/0.40  # Propositional unsat checks           : 0
% 0.18/0.40  #    Propositional check models        : 0
% 0.18/0.40  #    Propositional check unsatisfiable : 0
% 0.18/0.40  #    Propositional clauses             : 0
% 0.18/0.40  #    Propositional clauses after purity: 0
% 0.18/0.40  #    Propositional unsat core size     : 0
% 0.18/0.40  #    Propositional preprocessing time  : 0.000
% 0.18/0.40  #    Propositional encoding time       : 0.000
% 0.18/0.40  #    Propositional solver time         : 0.000
% 0.18/0.40  #    Success case prop preproc time    : 0.000
% 0.18/0.40  #    Success case prop encoding time   : 0.000
% 0.18/0.40  #    Success case prop solver time     : 0.000
% 0.18/0.40  # Current number of processed clauses  : 121
% 0.18/0.40  #    Positive orientable unit clauses  : 22
% 0.18/0.40  #    Positive unorientable unit clauses: 0
% 0.18/0.40  #    Negative unit clauses             : 5
% 0.18/0.40  #    Non-unit-clauses                  : 94
% 0.18/0.40  # Current number of unprocessed clauses: 140
% 0.18/0.40  # ...number of literals in the above   : 1101
% 0.18/0.40  # Current number of archived formulas  : 0
% 0.18/0.40  # Current number of archived clauses   : 48
% 0.18/0.40  # Clause-clause subsumption calls (NU) : 16504
% 0.18/0.40  # Rec. Clause-clause subsumption calls : 1189
% 0.18/0.40  # Non-unit clause-clause subsumptions  : 68
% 0.18/0.40  # Unit Clause-clause subsumption calls : 20
% 0.18/0.40  # Rewrite failures with RHS unbound    : 0
% 0.18/0.40  # BW rewrite match attempts            : 3
% 0.18/0.40  # BW rewrite match successes           : 2
% 0.18/0.40  # Condensation attempts                : 0
% 0.18/0.40  # Condensation successes               : 0
% 0.18/0.40  # Termbank termtop insertions          : 19411
% 0.18/0.40  
% 0.18/0.40  # -------------------------------------------------
% 0.18/0.40  # User time                : 0.060 s
% 0.18/0.40  # System time              : 0.006 s
% 0.18/0.40  # Total time               : 0.066 s
% 0.18/0.40  # Maximum resident set size: 1600 pages
%------------------------------------------------------------------------------
