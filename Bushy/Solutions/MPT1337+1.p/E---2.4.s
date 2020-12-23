%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : tops_2__t60_tops_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:42 EDT 2019

% Result     : Theorem 0.59s
% Output     : CNFRefutation 0.59s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 361 expanded)
%              Number of clauses        :   50 ( 135 expanded)
%              Number of leaves         :    9 (  86 expanded)
%              Depth                    :   12
%              Number of atoms          :  297 (2553 expanded)
%              Number of equality atoms :   34 ( 245 expanded)
%              Maximal formula depth    :   22 (   5 average)
%              Maximal clause size      :   44 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t60_tops_2,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( l1_pre_topc(X2)
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
             => ! [X4] :
                  ( m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
                 => ( ( v5_pre_topc(X3,X1,X2)
                      & v2_tops_2(X4,X2) )
                   => ! [X5] :
                        ( m1_subset_1(X5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
                       => ( X5 = k9_relat_1(k3_funct_3(X3),X4)
                         => v2_tops_2(X5,X1) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t60_tops_2.p',t60_tops_2)).

fof(d12_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2,X3] :
          ( X3 = k9_relat_1(X1,X2)
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r2_hidden(X5,k1_relat_1(X1))
                  & r2_hidden(X5,X2)
                  & X4 = k1_funct_1(X1,X5) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t60_tops_2.p',d12_funct_1)).

fof(d2_tops_2,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
         => ( v2_tops_2(X2,X1)
          <=> ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ( r2_hidden(X3,X2)
                 => v4_pre_topc(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t60_tops_2.p',d2_tops_2)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t60_tops_2.p',cc1_relset_1)).

fof(dt_k3_funct_3,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_relat_1(k3_funct_3(X1))
        & v1_funct_1(k3_funct_3(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t60_tops_2.p',dt_k3_funct_3)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t60_tops_2.p',t4_subset)).

fof(redefinition_k8_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k8_relset_1(X1,X2,X3,X4) = k10_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t60_tops_2.p',redefinition_k8_relset_1)).

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
    file('/export/starexec/sandbox2/benchmark/tops_2__t60_tops_2.p',d12_pre_topc)).

fof(t24_funct_3,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( r2_hidden(X1,k1_relat_1(k3_funct_3(X2)))
       => k1_funct_1(k3_funct_3(X2),X1) = k10_relat_1(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t60_tops_2.p',t24_funct_3)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( l1_pre_topc(X2)
           => ! [X3] :
                ( ( v1_funct_1(X3)
                  & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
               => ! [X4] :
                    ( m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
                   => ( ( v5_pre_topc(X3,X1,X2)
                        & v2_tops_2(X4,X2) )
                     => ! [X5] :
                          ( m1_subset_1(X5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
                         => ( X5 = k9_relat_1(k3_funct_3(X3),X4)
                           => v2_tops_2(X5,X1) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t60_tops_2])).

fof(c_0_10,negated_conjecture,
    ( l1_pre_topc(esk1_0)
    & l1_pre_topc(esk2_0)
    & v1_funct_1(esk3_0)
    & v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0))
    & m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))
    & m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))))
    & v5_pre_topc(esk3_0,esk1_0,esk2_0)
    & v2_tops_2(esk4_0,esk2_0)
    & m1_subset_1(esk5_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))
    & esk5_0 = k9_relat_1(k3_funct_3(esk3_0),esk4_0)
    & ~ v2_tops_2(esk5_0,esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).

fof(c_0_11,plain,(
    ! [X13,X14,X15,X16,X18,X19,X20,X21,X23] :
      ( ( r2_hidden(esk6_4(X13,X14,X15,X16),k1_relat_1(X13))
        | ~ r2_hidden(X16,X15)
        | X15 != k9_relat_1(X13,X14)
        | ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13) )
      & ( r2_hidden(esk6_4(X13,X14,X15,X16),X14)
        | ~ r2_hidden(X16,X15)
        | X15 != k9_relat_1(X13,X14)
        | ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13) )
      & ( X16 = k1_funct_1(X13,esk6_4(X13,X14,X15,X16))
        | ~ r2_hidden(X16,X15)
        | X15 != k9_relat_1(X13,X14)
        | ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13) )
      & ( ~ r2_hidden(X19,k1_relat_1(X13))
        | ~ r2_hidden(X19,X14)
        | X18 != k1_funct_1(X13,X19)
        | r2_hidden(X18,X15)
        | X15 != k9_relat_1(X13,X14)
        | ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13) )
      & ( ~ r2_hidden(esk7_3(X13,X20,X21),X21)
        | ~ r2_hidden(X23,k1_relat_1(X13))
        | ~ r2_hidden(X23,X20)
        | esk7_3(X13,X20,X21) != k1_funct_1(X13,X23)
        | X21 = k9_relat_1(X13,X20)
        | ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13) )
      & ( r2_hidden(esk8_3(X13,X20,X21),k1_relat_1(X13))
        | r2_hidden(esk7_3(X13,X20,X21),X21)
        | X21 = k9_relat_1(X13,X20)
        | ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13) )
      & ( r2_hidden(esk8_3(X13,X20,X21),X20)
        | r2_hidden(esk7_3(X13,X20,X21),X21)
        | X21 = k9_relat_1(X13,X20)
        | ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13) )
      & ( esk7_3(X13,X20,X21) = k1_funct_1(X13,esk8_3(X13,X20,X21))
        | r2_hidden(esk7_3(X13,X20,X21),X21)
        | X21 = k9_relat_1(X13,X20)
        | ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_funct_1])])])])])])).

fof(c_0_12,plain,(
    ! [X30,X31,X32] :
      ( ( ~ v2_tops_2(X31,X30)
        | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X30)))
        | ~ r2_hidden(X32,X31)
        | v4_pre_topc(X32,X30)
        | ~ m1_subset_1(X31,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X30))))
        | ~ l1_pre_topc(X30) )
      & ( m1_subset_1(esk10_2(X30,X31),k1_zfmisc_1(u1_struct_0(X30)))
        | v2_tops_2(X31,X30)
        | ~ m1_subset_1(X31,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X30))))
        | ~ l1_pre_topc(X30) )
      & ( r2_hidden(esk10_2(X30,X31),X31)
        | v2_tops_2(X31,X30)
        | ~ m1_subset_1(X31,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X30))))
        | ~ l1_pre_topc(X30) )
      & ( ~ v4_pre_topc(esk10_2(X30,X31),X30)
        | v2_tops_2(X31,X30)
        | ~ m1_subset_1(X31,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X30))))
        | ~ l1_pre_topc(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tops_2])])])])])).

cnf(c_0_13,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,negated_conjecture,
    ( esk5_0 = k9_relat_1(k3_funct_3(esk3_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,negated_conjecture,
    ( ~ v2_tops_2(esk5_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( r2_hidden(esk6_4(X1,X2,X3,X4),X2)
    | ~ r2_hidden(X4,X3)
    | X3 != k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( r2_hidden(esk10_2(X1,X2),X2)
    | v2_tops_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,negated_conjecture,
    ( m1_subset_1(k9_relat_1(k3_funct_3(esk3_0),esk4_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0)))) ),
    inference(rw,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_19,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_20,negated_conjecture,
    ( ~ v2_tops_2(k9_relat_1(k3_funct_3(esk3_0),esk4_0),esk1_0) ),
    inference(rw,[status(thm)],[c_0_15,c_0_14])).

fof(c_0_21,plain,(
    ! [X67,X68,X69] :
      ( ~ m1_subset_1(X69,k1_zfmisc_1(k2_zfmisc_1(X67,X68)))
      | v1_relat_1(X69) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_22,plain,
    ( r2_hidden(esk6_4(X1,X2,k9_relat_1(X1,X2),X3),X2)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X3,k9_relat_1(X1,X2))
    | ~ v1_funct_1(X1) ),
    inference(er,[status(thm)],[c_0_16])).

cnf(c_0_23,negated_conjecture,
    ( r2_hidden(esk10_2(esk1_0,k9_relat_1(k3_funct_3(esk3_0),esk4_0)),k9_relat_1(k3_funct_3(esk3_0),esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19])]),c_0_20])).

fof(c_0_24,plain,(
    ! [X34] :
      ( ( v1_relat_1(k3_funct_3(X34))
        | ~ v1_relat_1(X34)
        | ~ v1_funct_1(X34) )
      & ( v1_funct_1(k3_funct_3(X34))
        | ~ v1_relat_1(X34)
        | ~ v1_funct_1(X34) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_funct_3])])])).

cnf(c_0_25,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_27,plain,
    ( r2_hidden(esk6_4(X1,X2,X3,X4),k1_relat_1(X1))
    | ~ r2_hidden(X4,X3)
    | X3 != k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_28,plain,
    ( X1 = k1_funct_1(X2,esk6_4(X2,X3,X4,X1))
    | ~ r2_hidden(X1,X4)
    | X4 != k9_relat_1(X2,X3)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_29,plain,(
    ! [X56,X57,X58] :
      ( ~ r2_hidden(X56,X57)
      | ~ m1_subset_1(X57,k1_zfmisc_1(X58))
      | m1_subset_1(X56,X58) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(esk6_4(k3_funct_3(esk3_0),esk4_0,k9_relat_1(k3_funct_3(esk3_0),esk4_0),esk10_2(esk1_0,k9_relat_1(k3_funct_3(esk3_0),esk4_0))),esk4_0)
    | ~ v1_relat_1(k3_funct_3(esk3_0))
    | ~ v1_funct_1(k3_funct_3(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_31,plain,
    ( v1_relat_1(k3_funct_3(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_32,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_33,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_34,plain,
    ( r2_hidden(esk6_4(X1,X2,k9_relat_1(X1,X2),X3),k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X3,k9_relat_1(X1,X2))
    | ~ v1_funct_1(X1) ),
    inference(er,[status(thm)],[c_0_27])).

cnf(c_0_35,plain,
    ( k1_funct_1(X1,esk6_4(X1,X2,k9_relat_1(X1,X2),X3)) = X3
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X3,k9_relat_1(X1,X2))
    | ~ v1_funct_1(X1) ),
    inference(er,[status(thm)],[c_0_28])).

cnf(c_0_36,plain,
    ( v4_pre_topc(X3,X2)
    | ~ v2_tops_2(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r2_hidden(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_37,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(esk6_4(k3_funct_3(esk3_0),esk4_0,k9_relat_1(k3_funct_3(esk3_0),esk4_0),esk10_2(esk1_0,k9_relat_1(k3_funct_3(esk3_0),esk4_0))),esk4_0)
    | ~ v1_funct_1(k3_funct_3(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32]),c_0_33])])).

cnf(c_0_39,plain,
    ( v1_funct_1(k3_funct_3(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(esk6_4(k3_funct_3(esk3_0),esk4_0,k9_relat_1(k3_funct_3(esk3_0),esk4_0),esk10_2(esk1_0,k9_relat_1(k3_funct_3(esk3_0),esk4_0))),k1_relat_1(k3_funct_3(esk3_0)))
    | ~ v1_relat_1(k3_funct_3(esk3_0))
    | ~ v1_funct_1(k3_funct_3(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_23])).

fof(c_0_41,plain,(
    ! [X44,X45,X46,X47] :
      ( ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X45)))
      | k8_relset_1(X44,X45,X46,X47) = k10_relat_1(X46,X47) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k8_relset_1])])).

cnf(c_0_42,negated_conjecture,
    ( k1_funct_1(k3_funct_3(esk3_0),esk6_4(k3_funct_3(esk3_0),esk4_0,k9_relat_1(k3_funct_3(esk3_0),esk4_0),esk10_2(esk1_0,k9_relat_1(k3_funct_3(esk3_0),esk4_0)))) = esk10_2(esk1_0,k9_relat_1(k3_funct_3(esk3_0),esk4_0))
    | ~ v1_relat_1(k3_funct_3(esk3_0))
    | ~ v1_funct_1(k3_funct_3(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_23])).

fof(c_0_43,plain,(
    ! [X25,X26,X27,X28] :
      ( ( ~ v5_pre_topc(X27,X25,X26)
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X26)))
        | ~ v4_pre_topc(X28,X26)
        | v4_pre_topc(k8_relset_1(u1_struct_0(X25),u1_struct_0(X26),X27,X28),X25)
        | ~ v1_funct_1(X27)
        | ~ v1_funct_2(X27,u1_struct_0(X25),u1_struct_0(X26))
        | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X25),u1_struct_0(X26))))
        | ~ l1_pre_topc(X26)
        | ~ l1_pre_topc(X25) )
      & ( m1_subset_1(esk9_3(X25,X26,X27),k1_zfmisc_1(u1_struct_0(X26)))
        | v5_pre_topc(X27,X25,X26)
        | ~ v1_funct_1(X27)
        | ~ v1_funct_2(X27,u1_struct_0(X25),u1_struct_0(X26))
        | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X25),u1_struct_0(X26))))
        | ~ l1_pre_topc(X26)
        | ~ l1_pre_topc(X25) )
      & ( v4_pre_topc(esk9_3(X25,X26,X27),X26)
        | v5_pre_topc(X27,X25,X26)
        | ~ v1_funct_1(X27)
        | ~ v1_funct_2(X27,u1_struct_0(X25),u1_struct_0(X26))
        | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X25),u1_struct_0(X26))))
        | ~ l1_pre_topc(X26)
        | ~ l1_pre_topc(X25) )
      & ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X25),u1_struct_0(X26),X27,esk9_3(X25,X26,X27)),X25)
        | v5_pre_topc(X27,X25,X26)
        | ~ v1_funct_1(X27)
        | ~ v1_funct_2(X27,u1_struct_0(X25),u1_struct_0(X26))
        | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X25),u1_struct_0(X26))))
        | ~ l1_pre_topc(X26)
        | ~ l1_pre_topc(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_pre_topc])])])])])).

cnf(c_0_44,plain,
    ( v4_pre_topc(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ v2_tops_2(X3,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_45,negated_conjecture,
    ( v2_tops_2(esk4_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_46,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_47,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_48,negated_conjecture,
    ( r2_hidden(esk6_4(k3_funct_3(esk3_0),esk4_0,k9_relat_1(k3_funct_3(esk3_0),esk4_0),esk10_2(esk1_0,k9_relat_1(k3_funct_3(esk3_0),esk4_0))),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_32]),c_0_33])])).

fof(c_0_49,plain,(
    ! [X50,X51] :
      ( ~ v1_relat_1(X51)
      | ~ v1_funct_1(X51)
      | ~ r2_hidden(X50,k1_relat_1(k3_funct_3(X51)))
      | k1_funct_1(k3_funct_3(X51),X50) = k10_relat_1(X51,X50) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t24_funct_3])])).

cnf(c_0_50,negated_conjecture,
    ( r2_hidden(esk6_4(k3_funct_3(esk3_0),esk4_0,k9_relat_1(k3_funct_3(esk3_0),esk4_0),esk10_2(esk1_0,k9_relat_1(k3_funct_3(esk3_0),esk4_0))),k1_relat_1(k3_funct_3(esk3_0)))
    | ~ v1_funct_1(k3_funct_3(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_31]),c_0_32]),c_0_33])])).

cnf(c_0_51,plain,
    ( k8_relset_1(X2,X3,X1,X4) = k10_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_52,negated_conjecture,
    ( k1_funct_1(k3_funct_3(esk3_0),esk6_4(k3_funct_3(esk3_0),esk4_0,k9_relat_1(k3_funct_3(esk3_0),esk4_0),esk10_2(esk1_0,k9_relat_1(k3_funct_3(esk3_0),esk4_0)))) = esk10_2(esk1_0,k9_relat_1(k3_funct_3(esk3_0),esk4_0))
    | ~ v1_funct_1(k3_funct_3(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_31]),c_0_32]),c_0_33])])).

cnf(c_0_53,plain,
    ( v4_pre_topc(k8_relset_1(u1_struct_0(X2),u1_struct_0(X3),X1,X4),X2)
    | ~ v5_pre_topc(X1,X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ v4_pre_topc(X4,X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_54,negated_conjecture,
    ( v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_55,negated_conjecture,
    ( v5_pre_topc(esk3_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_56,negated_conjecture,
    ( v4_pre_topc(X1,esk2_0)
    | ~ r2_hidden(X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_46]),c_0_47])])).

cnf(c_0_57,negated_conjecture,
    ( m1_subset_1(esk6_4(k3_funct_3(esk3_0),esk4_0,k9_relat_1(k3_funct_3(esk3_0),esk4_0),esk10_2(esk1_0,k9_relat_1(k3_funct_3(esk3_0),esk4_0))),X1)
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_48])).

cnf(c_0_58,plain,
    ( k1_funct_1(k3_funct_3(X1),X2) = k10_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(k3_funct_3(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_59,negated_conjecture,
    ( r2_hidden(esk6_4(k3_funct_3(esk3_0),esk4_0,k9_relat_1(k3_funct_3(esk3_0),esk4_0),esk10_2(esk1_0,k9_relat_1(k3_funct_3(esk3_0),esk4_0))),k1_relat_1(k3_funct_3(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_39]),c_0_32]),c_0_33])])).

cnf(c_0_60,negated_conjecture,
    ( k10_relat_1(esk3_0,X1) = k8_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_51,c_0_26])).

cnf(c_0_61,negated_conjecture,
    ( k1_funct_1(k3_funct_3(esk3_0),esk6_4(k3_funct_3(esk3_0),esk4_0,k9_relat_1(k3_funct_3(esk3_0),esk4_0),esk10_2(esk1_0,k9_relat_1(k3_funct_3(esk3_0),esk4_0)))) = esk10_2(esk1_0,k9_relat_1(k3_funct_3(esk3_0),esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_39]),c_0_32]),c_0_33])])).

cnf(c_0_62,negated_conjecture,
    ( v4_pre_topc(k8_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,X1),esk1_0)
    | ~ v4_pre_topc(X1,esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_55]),c_0_26]),c_0_33]),c_0_47]),c_0_19])])).

cnf(c_0_63,negated_conjecture,
    ( v4_pre_topc(esk6_4(k3_funct_3(esk3_0),esk4_0,k9_relat_1(k3_funct_3(esk3_0),esk4_0),esk10_2(esk1_0,k9_relat_1(k3_funct_3(esk3_0),esk4_0))),esk2_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_48])).

cnf(c_0_64,negated_conjecture,
    ( m1_subset_1(esk6_4(k3_funct_3(esk3_0),esk4_0,k9_relat_1(k3_funct_3(esk3_0),esk4_0),esk10_2(esk1_0,k9_relat_1(k3_funct_3(esk3_0),esk4_0))),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_57,c_0_46])).

cnf(c_0_65,negated_conjecture,
    ( k8_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,esk6_4(k3_funct_3(esk3_0),esk4_0,k9_relat_1(k3_funct_3(esk3_0),esk4_0),esk10_2(esk1_0,k9_relat_1(k3_funct_3(esk3_0),esk4_0)))) = esk10_2(esk1_0,k9_relat_1(k3_funct_3(esk3_0),esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_60]),c_0_61]),c_0_32]),c_0_33])])).

cnf(c_0_66,plain,
    ( v2_tops_2(X2,X1)
    | ~ v4_pre_topc(esk10_2(X1,X2),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_67,negated_conjecture,
    ( v4_pre_topc(esk10_2(esk1_0,k9_relat_1(k3_funct_3(esk3_0),esk4_0)),esk1_0) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_64])]),c_0_65])).

cnf(c_0_68,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_18]),c_0_19])]),c_0_20]),
    [proof]).
%------------------------------------------------------------------------------
