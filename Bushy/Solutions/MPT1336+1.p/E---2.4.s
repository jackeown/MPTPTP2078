%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : tops_2__t59_tops_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:42 EDT 2019

% Result     : Theorem 5.27s
% Output     : CNFRefutation 5.27s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 379 expanded)
%              Number of clauses        :   56 ( 142 expanded)
%              Number of leaves         :   12 (  91 expanded)
%              Depth                    :   14
%              Number of atoms          :  363 (2851 expanded)
%              Number of equality atoms :   48 ( 265 expanded)
%              Maximal formula depth    :   22 (   5 average)
%              Maximal clause size      :   68 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t59_tops_2,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & l1_pre_topc(X2) )
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
             => ! [X4] :
                  ( m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
                 => ( ( v5_pre_topc(X3,X1,X2)
                      & v1_tops_2(X4,X2) )
                   => ! [X5] :
                        ( m1_subset_1(X5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
                       => ( X5 = k9_relat_1(k3_funct_3(X3),X4)
                         => v1_tops_2(X5,X1) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t59_tops_2.p',t59_tops_2)).

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
    file('/export/starexec/sandbox/benchmark/tops_2__t59_tops_2.p',d12_funct_1)).

fof(d1_tops_2,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
         => ( v1_tops_2(X2,X1)
          <=> ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ( r2_hidden(X3,X2)
                 => v3_pre_topc(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t59_tops_2.p',d1_tops_2)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t59_tops_2.p',cc1_relset_1)).

fof(dt_k3_funct_3,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_relat_1(k3_funct_3(X1))
        & v1_funct_1(k3_funct_3(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t59_tops_2.p',dt_k3_funct_3)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t59_tops_2.p',t4_subset)).

fof(redefinition_k8_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k8_relset_1(X1,X2,X3,X4) = k10_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t59_tops_2.p',redefinition_k8_relset_1)).

fof(t55_tops_2,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( l1_pre_topc(X2)
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
             => ( ( k2_struct_0(X2) = k1_xboole_0
                 => k2_struct_0(X1) = k1_xboole_0 )
               => ( v5_pre_topc(X3,X1,X2)
                <=> ! [X4] :
                      ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
                     => ( v3_pre_topc(X4,X2)
                       => v3_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4),X1) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t59_tops_2.p',t55_tops_2)).

fof(t24_funct_3,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( r2_hidden(X1,k1_relat_1(k3_funct_3(X2)))
       => k1_funct_1(k3_funct_3(X2),X1) = k10_relat_1(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t59_tops_2.p',t24_funct_3)).

fof(fc5_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(k2_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t59_tops_2.p',fc5_struct_0)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t59_tops_2.p',fc1_xboole_0)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t59_tops_2.p',dt_l1_pre_topc)).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & l1_pre_topc(X2) )
           => ! [X3] :
                ( ( v1_funct_1(X3)
                  & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
               => ! [X4] :
                    ( m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
                   => ( ( v5_pre_topc(X3,X1,X2)
                        & v1_tops_2(X4,X2) )
                     => ! [X5] :
                          ( m1_subset_1(X5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
                         => ( X5 = k9_relat_1(k3_funct_3(X3),X4)
                           => v1_tops_2(X5,X1) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t59_tops_2])).

fof(c_0_13,negated_conjecture,
    ( l1_pre_topc(esk1_0)
    & ~ v2_struct_0(esk2_0)
    & l1_pre_topc(esk2_0)
    & v1_funct_1(esk3_0)
    & v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0))
    & m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))
    & m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))))
    & v5_pre_topc(esk3_0,esk1_0,esk2_0)
    & v1_tops_2(esk4_0,esk2_0)
    & m1_subset_1(esk5_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))
    & esk5_0 = k9_relat_1(k3_funct_3(esk3_0),esk4_0)
    & ~ v1_tops_2(esk5_0,esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_12])])])])).

fof(c_0_14,plain,(
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

fof(c_0_15,plain,(
    ! [X25,X26,X27] :
      ( ( ~ v1_tops_2(X26,X25)
        | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X25)))
        | ~ r2_hidden(X27,X26)
        | v3_pre_topc(X27,X25)
        | ~ m1_subset_1(X26,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X25))))
        | ~ l1_pre_topc(X25) )
      & ( m1_subset_1(esk9_2(X25,X26),k1_zfmisc_1(u1_struct_0(X25)))
        | v1_tops_2(X26,X25)
        | ~ m1_subset_1(X26,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X25))))
        | ~ l1_pre_topc(X25) )
      & ( r2_hidden(esk9_2(X25,X26),X26)
        | v1_tops_2(X26,X25)
        | ~ m1_subset_1(X26,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X25))))
        | ~ l1_pre_topc(X25) )
      & ( ~ v3_pre_topc(esk9_2(X25,X26),X25)
        | v1_tops_2(X26,X25)
        | ~ m1_subset_1(X26,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X25))))
        | ~ l1_pre_topc(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tops_2])])])])])).

cnf(c_0_16,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,negated_conjecture,
    ( esk5_0 = k9_relat_1(k3_funct_3(esk3_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( ~ v1_tops_2(esk5_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( r2_hidden(esk6_4(X1,X2,X3,X4),X2)
    | ~ r2_hidden(X4,X3)
    | X3 != k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( r2_hidden(esk9_2(X1,X2),X2)
    | v1_tops_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(k9_relat_1(k3_funct_3(esk3_0),esk4_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0)))) ),
    inference(rw,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_22,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_23,negated_conjecture,
    ( ~ v1_tops_2(k9_relat_1(k3_funct_3(esk3_0),esk4_0),esk1_0) ),
    inference(rw,[status(thm)],[c_0_18,c_0_17])).

fof(c_0_24,plain,(
    ! [X68,X69,X70] :
      ( ~ m1_subset_1(X70,k1_zfmisc_1(k2_zfmisc_1(X68,X69)))
      | v1_relat_1(X70) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_25,plain,
    ( r2_hidden(esk6_4(X1,X2,k9_relat_1(X1,X2),X3),X2)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X3,k9_relat_1(X1,X2))
    | ~ v1_funct_1(X1) ),
    inference(er,[status(thm)],[c_0_19])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(esk9_2(esk1_0,k9_relat_1(k3_funct_3(esk3_0),esk4_0)),k9_relat_1(k3_funct_3(esk3_0),esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22])]),c_0_23])).

fof(c_0_27,plain,(
    ! [X30] :
      ( ( v1_relat_1(k3_funct_3(X30))
        | ~ v1_relat_1(X30)
        | ~ v1_funct_1(X30) )
      & ( v1_funct_1(k3_funct_3(X30))
        | ~ v1_relat_1(X30)
        | ~ v1_funct_1(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_funct_3])])])).

cnf(c_0_28,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_29,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_30,plain,
    ( r2_hidden(esk6_4(X1,X2,X3,X4),k1_relat_1(X1))
    | ~ r2_hidden(X4,X3)
    | X3 != k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_31,plain,
    ( X1 = k1_funct_1(X2,esk6_4(X2,X3,X4,X1))
    | ~ r2_hidden(X1,X4)
    | X4 != k9_relat_1(X2,X3)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_32,plain,(
    ! [X52,X53,X54] :
      ( ~ r2_hidden(X52,X53)
      | ~ m1_subset_1(X53,k1_zfmisc_1(X54))
      | m1_subset_1(X52,X54) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(esk6_4(k3_funct_3(esk3_0),esk4_0,k9_relat_1(k3_funct_3(esk3_0),esk4_0),esk9_2(esk1_0,k9_relat_1(k3_funct_3(esk3_0),esk4_0))),esk4_0)
    | ~ v1_relat_1(k3_funct_3(esk3_0))
    | ~ v1_funct_1(k3_funct_3(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_34,plain,
    ( v1_relat_1(k3_funct_3(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_35,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_36,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_37,plain,
    ( r2_hidden(esk6_4(X1,X2,k9_relat_1(X1,X2),X3),k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X3,k9_relat_1(X1,X2))
    | ~ v1_funct_1(X1) ),
    inference(er,[status(thm)],[c_0_30])).

cnf(c_0_38,plain,
    ( k1_funct_1(X1,esk6_4(X1,X2,k9_relat_1(X1,X2),X3)) = X3
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X3,k9_relat_1(X1,X2))
    | ~ v1_funct_1(X1) ),
    inference(er,[status(thm)],[c_0_31])).

cnf(c_0_39,plain,
    ( v3_pre_topc(X3,X2)
    | ~ v1_tops_2(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r2_hidden(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_40,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(esk6_4(k3_funct_3(esk3_0),esk4_0,k9_relat_1(k3_funct_3(esk3_0),esk4_0),esk9_2(esk1_0,k9_relat_1(k3_funct_3(esk3_0),esk4_0))),esk4_0)
    | ~ v1_funct_1(k3_funct_3(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35]),c_0_36])])).

cnf(c_0_42,plain,
    ( v1_funct_1(k3_funct_3(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(esk6_4(k3_funct_3(esk3_0),esk4_0,k9_relat_1(k3_funct_3(esk3_0),esk4_0),esk9_2(esk1_0,k9_relat_1(k3_funct_3(esk3_0),esk4_0))),k1_relat_1(k3_funct_3(esk3_0)))
    | ~ v1_relat_1(k3_funct_3(esk3_0))
    | ~ v1_funct_1(k3_funct_3(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_26])).

fof(c_0_44,plain,(
    ! [X40,X41,X42,X43] :
      ( ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41)))
      | k8_relset_1(X40,X41,X42,X43) = k10_relat_1(X42,X43) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k8_relset_1])])).

cnf(c_0_45,negated_conjecture,
    ( k1_funct_1(k3_funct_3(esk3_0),esk6_4(k3_funct_3(esk3_0),esk4_0,k9_relat_1(k3_funct_3(esk3_0),esk4_0),esk9_2(esk1_0,k9_relat_1(k3_funct_3(esk3_0),esk4_0)))) = esk9_2(esk1_0,k9_relat_1(k3_funct_3(esk3_0),esk4_0))
    | ~ v1_relat_1(k3_funct_3(esk3_0))
    | ~ v1_funct_1(k3_funct_3(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_26])).

fof(c_0_46,plain,(
    ! [X55,X56,X57,X58] :
      ( ( ~ v5_pre_topc(X57,X55,X56)
        | ~ m1_subset_1(X58,k1_zfmisc_1(u1_struct_0(X56)))
        | ~ v3_pre_topc(X58,X56)
        | v3_pre_topc(k8_relset_1(u1_struct_0(X55),u1_struct_0(X56),X57,X58),X55)
        | k2_struct_0(X56) = k1_xboole_0
        | ~ v1_funct_1(X57)
        | ~ v1_funct_2(X57,u1_struct_0(X55),u1_struct_0(X56))
        | ~ m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X55),u1_struct_0(X56))))
        | ~ l1_pre_topc(X56)
        | ~ l1_pre_topc(X55) )
      & ( m1_subset_1(esk13_3(X55,X56,X57),k1_zfmisc_1(u1_struct_0(X56)))
        | v5_pre_topc(X57,X55,X56)
        | k2_struct_0(X56) = k1_xboole_0
        | ~ v1_funct_1(X57)
        | ~ v1_funct_2(X57,u1_struct_0(X55),u1_struct_0(X56))
        | ~ m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X55),u1_struct_0(X56))))
        | ~ l1_pre_topc(X56)
        | ~ l1_pre_topc(X55) )
      & ( v3_pre_topc(esk13_3(X55,X56,X57),X56)
        | v5_pre_topc(X57,X55,X56)
        | k2_struct_0(X56) = k1_xboole_0
        | ~ v1_funct_1(X57)
        | ~ v1_funct_2(X57,u1_struct_0(X55),u1_struct_0(X56))
        | ~ m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X55),u1_struct_0(X56))))
        | ~ l1_pre_topc(X56)
        | ~ l1_pre_topc(X55) )
      & ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X55),u1_struct_0(X56),X57,esk13_3(X55,X56,X57)),X55)
        | v5_pre_topc(X57,X55,X56)
        | k2_struct_0(X56) = k1_xboole_0
        | ~ v1_funct_1(X57)
        | ~ v1_funct_2(X57,u1_struct_0(X55),u1_struct_0(X56))
        | ~ m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X55),u1_struct_0(X56))))
        | ~ l1_pre_topc(X56)
        | ~ l1_pre_topc(X55) )
      & ( ~ v5_pre_topc(X57,X55,X56)
        | ~ m1_subset_1(X58,k1_zfmisc_1(u1_struct_0(X56)))
        | ~ v3_pre_topc(X58,X56)
        | v3_pre_topc(k8_relset_1(u1_struct_0(X55),u1_struct_0(X56),X57,X58),X55)
        | k2_struct_0(X55) != k1_xboole_0
        | ~ v1_funct_1(X57)
        | ~ v1_funct_2(X57,u1_struct_0(X55),u1_struct_0(X56))
        | ~ m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X55),u1_struct_0(X56))))
        | ~ l1_pre_topc(X56)
        | ~ l1_pre_topc(X55) )
      & ( m1_subset_1(esk13_3(X55,X56,X57),k1_zfmisc_1(u1_struct_0(X56)))
        | v5_pre_topc(X57,X55,X56)
        | k2_struct_0(X55) != k1_xboole_0
        | ~ v1_funct_1(X57)
        | ~ v1_funct_2(X57,u1_struct_0(X55),u1_struct_0(X56))
        | ~ m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X55),u1_struct_0(X56))))
        | ~ l1_pre_topc(X56)
        | ~ l1_pre_topc(X55) )
      & ( v3_pre_topc(esk13_3(X55,X56,X57),X56)
        | v5_pre_topc(X57,X55,X56)
        | k2_struct_0(X55) != k1_xboole_0
        | ~ v1_funct_1(X57)
        | ~ v1_funct_2(X57,u1_struct_0(X55),u1_struct_0(X56))
        | ~ m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X55),u1_struct_0(X56))))
        | ~ l1_pre_topc(X56)
        | ~ l1_pre_topc(X55) )
      & ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X55),u1_struct_0(X56),X57,esk13_3(X55,X56,X57)),X55)
        | v5_pre_topc(X57,X55,X56)
        | k2_struct_0(X55) != k1_xboole_0
        | ~ v1_funct_1(X57)
        | ~ v1_funct_2(X57,u1_struct_0(X55),u1_struct_0(X56))
        | ~ m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X55),u1_struct_0(X56))))
        | ~ l1_pre_topc(X56)
        | ~ l1_pre_topc(X55) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_tops_2])])])])])).

cnf(c_0_47,plain,
    ( v3_pre_topc(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ v1_tops_2(X3,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_48,negated_conjecture,
    ( v1_tops_2(esk4_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_49,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_50,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_51,negated_conjecture,
    ( r2_hidden(esk6_4(k3_funct_3(esk3_0),esk4_0,k9_relat_1(k3_funct_3(esk3_0),esk4_0),esk9_2(esk1_0,k9_relat_1(k3_funct_3(esk3_0),esk4_0))),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_35]),c_0_36])])).

fof(c_0_52,plain,(
    ! [X46,X47] :
      ( ~ v1_relat_1(X47)
      | ~ v1_funct_1(X47)
      | ~ r2_hidden(X46,k1_relat_1(k3_funct_3(X47)))
      | k1_funct_1(k3_funct_3(X47),X46) = k10_relat_1(X47,X46) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t24_funct_3])])).

cnf(c_0_53,negated_conjecture,
    ( r2_hidden(esk6_4(k3_funct_3(esk3_0),esk4_0,k9_relat_1(k3_funct_3(esk3_0),esk4_0),esk9_2(esk1_0,k9_relat_1(k3_funct_3(esk3_0),esk4_0))),k1_relat_1(k3_funct_3(esk3_0)))
    | ~ v1_funct_1(k3_funct_3(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_34]),c_0_35]),c_0_36])])).

cnf(c_0_54,plain,
    ( k8_relset_1(X2,X3,X1,X4) = k10_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_55,negated_conjecture,
    ( k1_funct_1(k3_funct_3(esk3_0),esk6_4(k3_funct_3(esk3_0),esk4_0,k9_relat_1(k3_funct_3(esk3_0),esk4_0),esk9_2(esk1_0,k9_relat_1(k3_funct_3(esk3_0),esk4_0)))) = esk9_2(esk1_0,k9_relat_1(k3_funct_3(esk3_0),esk4_0))
    | ~ v1_funct_1(k3_funct_3(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_34]),c_0_35]),c_0_36])])).

cnf(c_0_56,plain,
    ( v3_pre_topc(k8_relset_1(u1_struct_0(X2),u1_struct_0(X3),X1,X4),X2)
    | k2_struct_0(X3) = k1_xboole_0
    | ~ v5_pre_topc(X1,X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ v3_pre_topc(X4,X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_57,negated_conjecture,
    ( v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_58,negated_conjecture,
    ( v5_pre_topc(esk3_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_59,negated_conjecture,
    ( v3_pre_topc(X1,esk2_0)
    | ~ r2_hidden(X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_49]),c_0_50])])).

cnf(c_0_60,negated_conjecture,
    ( m1_subset_1(esk6_4(k3_funct_3(esk3_0),esk4_0,k9_relat_1(k3_funct_3(esk3_0),esk4_0),esk9_2(esk1_0,k9_relat_1(k3_funct_3(esk3_0),esk4_0))),X1)
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_51])).

cnf(c_0_61,plain,
    ( k1_funct_1(k3_funct_3(X1),X2) = k10_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(k3_funct_3(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_62,negated_conjecture,
    ( r2_hidden(esk6_4(k3_funct_3(esk3_0),esk4_0,k9_relat_1(k3_funct_3(esk3_0),esk4_0),esk9_2(esk1_0,k9_relat_1(k3_funct_3(esk3_0),esk4_0))),k1_relat_1(k3_funct_3(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_42]),c_0_35]),c_0_36])])).

cnf(c_0_63,negated_conjecture,
    ( k10_relat_1(esk3_0,X1) = k8_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_54,c_0_29])).

cnf(c_0_64,negated_conjecture,
    ( k1_funct_1(k3_funct_3(esk3_0),esk6_4(k3_funct_3(esk3_0),esk4_0,k9_relat_1(k3_funct_3(esk3_0),esk4_0),esk9_2(esk1_0,k9_relat_1(k3_funct_3(esk3_0),esk4_0)))) = esk9_2(esk1_0,k9_relat_1(k3_funct_3(esk3_0),esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_42]),c_0_35]),c_0_36])])).

cnf(c_0_65,negated_conjecture,
    ( k2_struct_0(esk2_0) = k1_xboole_0
    | v3_pre_topc(k8_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,X1),esk1_0)
    | ~ v3_pre_topc(X1,esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_58]),c_0_29]),c_0_36]),c_0_50]),c_0_22])])).

cnf(c_0_66,negated_conjecture,
    ( v3_pre_topc(esk6_4(k3_funct_3(esk3_0),esk4_0,k9_relat_1(k3_funct_3(esk3_0),esk4_0),esk9_2(esk1_0,k9_relat_1(k3_funct_3(esk3_0),esk4_0))),esk2_0) ),
    inference(spm,[status(thm)],[c_0_59,c_0_51])).

cnf(c_0_67,negated_conjecture,
    ( m1_subset_1(esk6_4(k3_funct_3(esk3_0),esk4_0,k9_relat_1(k3_funct_3(esk3_0),esk4_0),esk9_2(esk1_0,k9_relat_1(k3_funct_3(esk3_0),esk4_0))),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_60,c_0_49])).

cnf(c_0_68,negated_conjecture,
    ( k8_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,esk6_4(k3_funct_3(esk3_0),esk4_0,k9_relat_1(k3_funct_3(esk3_0),esk4_0),esk9_2(esk1_0,k9_relat_1(k3_funct_3(esk3_0),esk4_0)))) = esk9_2(esk1_0,k9_relat_1(k3_funct_3(esk3_0),esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_63]),c_0_64]),c_0_35]),c_0_36])])).

fof(c_0_69,plain,(
    ! [X71] :
      ( v2_struct_0(X71)
      | ~ l1_struct_0(X71)
      | ~ v1_xboole_0(k2_struct_0(X71)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc5_struct_0])])])).

cnf(c_0_70,plain,
    ( v1_tops_2(X2,X1)
    | ~ v3_pre_topc(esk9_2(X1,X2),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_71,negated_conjecture,
    ( k2_struct_0(esk2_0) = k1_xboole_0
    | v3_pre_topc(esk9_2(esk1_0,k9_relat_1(k3_funct_3(esk3_0),esk4_0)),esk1_0) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_67])]),c_0_68])).

cnf(c_0_72,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(k2_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_73,negated_conjecture,
    ( k2_struct_0(esk2_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_21]),c_0_22])]),c_0_23])).

cnf(c_0_74,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_75,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_76,plain,(
    ! [X35] :
      ( ~ l1_pre_topc(X35)
      | l1_struct_0(X35) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_77,negated_conjecture,
    ( ~ l1_struct_0(esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_74])]),c_0_75])).

cnf(c_0_78,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_76])).

cnf(c_0_79,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_50])]),
    [proof]).
%------------------------------------------------------------------------------
