%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : pre_topc__t57_pre_topc.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:44 EDT 2019

% Result     : Theorem 228.23s
% Output     : CNFRefutation 228.23s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 620 expanded)
%              Number of clauses        :   72 ( 229 expanded)
%              Number of leaves         :   18 ( 146 expanded)
%              Depth                    :   12
%              Number of atoms          :  322 (5371 expanded)
%              Number of equality atoms :   49 ( 390 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   30 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t57_pre_topc,conjecture,(
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
             => ! [X4] :
                  ( m1_pre_topc(X4,X2)
                 => ( v5_pre_topc(X3,X1,X2)
                   => ! [X5] :
                        ( ( v1_funct_1(X5)
                          & v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X4))
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X4)))) )
                       => ( X5 = X3
                         => v5_pre_topc(X5,X1,X4) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t57_pre_topc.p',t57_pre_topc)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t57_pre_topc.p',dt_m1_pre_topc)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t57_pre_topc.p',cc1_relset_1)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t57_pre_topc.p',cc2_relset_1)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t57_pre_topc.p',dt_l1_pre_topc)).

fof(t168_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(X2,X1) = k10_relat_1(X2,k3_xboole_0(k2_relat_1(X2),X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t57_pre_topc.p',t168_relat_1)).

fof(d19_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v5_relat_1(X2,X1)
      <=> r1_tarski(k2_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t57_pre_topc.p',d19_relat_1)).

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
    file('/export/starexec/sandbox2/benchmark/pre_topc__t57_pre_topc.p',d12_pre_topc)).

fof(d3_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => k2_struct_0(X1) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t57_pre_topc.p',d3_struct_0)).

fof(t167_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k10_relat_1(X2,X1),k1_relat_1(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t57_pre_topc.p',t167_relat_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t57_pre_topc.p',commutativity_k3_xboole_0)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t57_pre_topc.p',t28_xboole_1)).

fof(t169_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,k2_relat_1(X1)) = k1_relat_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t57_pre_topc.p',t169_relat_1)).

fof(dt_k2_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t57_pre_topc.p',dt_k2_struct_0)).

fof(t137_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => k10_relat_1(X3,k3_xboole_0(X1,X2)) = k3_xboole_0(k10_relat_1(X3,X1),k10_relat_1(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t57_pre_topc.p',t137_funct_1)).

fof(t43_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
             => ( v4_pre_topc(X3,X2)
              <=> ? [X4] :
                    ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                    & v4_pre_topc(X4,X1)
                    & k9_subset_1(u1_struct_0(X2),X4,k2_struct_0(X2)) = X3 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t57_pre_topc.p',t43_pre_topc)).

fof(redefinition_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k3_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t57_pre_topc.p',redefinition_k9_subset_1)).

fof(redefinition_k8_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k8_relset_1(X1,X2,X3,X4) = k10_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t57_pre_topc.p',redefinition_k8_relset_1)).

fof(c_0_18,negated_conjecture,(
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
               => ! [X4] :
                    ( m1_pre_topc(X4,X2)
                   => ( v5_pre_topc(X3,X1,X2)
                     => ! [X5] :
                          ( ( v1_funct_1(X5)
                            & v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X4))
                            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X4)))) )
                         => ( X5 = X3
                           => v5_pre_topc(X5,X1,X4) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t57_pre_topc])).

fof(c_0_19,negated_conjecture,
    ( v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & ~ v2_struct_0(esk2_0)
    & v2_pre_topc(esk2_0)
    & l1_pre_topc(esk2_0)
    & v1_funct_1(esk3_0)
    & v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0))
    & m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))
    & m1_pre_topc(esk4_0,esk2_0)
    & v5_pre_topc(esk3_0,esk1_0,esk2_0)
    & v1_funct_1(esk5_0)
    & v1_funct_2(esk5_0,u1_struct_0(esk1_0),u1_struct_0(esk4_0))
    & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk4_0))))
    & esk5_0 = esk3_0
    & ~ v5_pre_topc(esk5_0,esk1_0,esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_18])])])])).

fof(c_0_20,plain,(
    ! [X41,X42] :
      ( ~ l1_pre_topc(X41)
      | ~ m1_pre_topc(X42,X41)
      | l1_pre_topc(X42) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

fof(c_0_21,plain,(
    ! [X99,X100,X101] :
      ( ~ m1_subset_1(X101,k1_zfmisc_1(k2_zfmisc_1(X99,X100)))
      | v1_relat_1(X101) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_22,plain,(
    ! [X102,X103,X104] :
      ( ( v4_relat_1(X104,X102)
        | ~ m1_subset_1(X104,k1_zfmisc_1(k2_zfmisc_1(X102,X103))) )
      & ( v5_relat_1(X104,X103)
        | ~ m1_subset_1(X104,k1_zfmisc_1(k2_zfmisc_1(X102,X103))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

cnf(c_0_23,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk4_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,negated_conjecture,
    ( esk5_0 = esk3_0 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_25,plain,(
    ! [X40] :
      ( ~ l1_pre_topc(X40)
      | l1_struct_0(X40) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_26,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_28,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_29,plain,(
    ! [X71,X72] :
      ( ~ v1_relat_1(X72)
      | k10_relat_1(X72,X71) = k10_relat_1(X72,k3_xboole_0(k2_relat_1(X72),X71)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t168_relat_1])])).

cnf(c_0_30,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_31,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_32,plain,(
    ! [X23,X24] :
      ( ( ~ v5_relat_1(X24,X23)
        | r1_tarski(k2_relat_1(X24),X23)
        | ~ v1_relat_1(X24) )
      & ( ~ r1_tarski(k2_relat_1(X24),X23)
        | v5_relat_1(X24,X23)
        | ~ v1_relat_1(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).

cnf(c_0_33,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_34,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk4_0)))) ),
    inference(rw,[status(thm)],[c_0_23,c_0_24])).

fof(c_0_35,plain,(
    ! [X18,X19,X20,X21] :
      ( ( ~ v5_pre_topc(X20,X18,X19)
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X19)))
        | ~ v4_pre_topc(X21,X19)
        | v4_pre_topc(k8_relset_1(u1_struct_0(X18),u1_struct_0(X19),X20,X21),X18)
        | ~ v1_funct_1(X20)
        | ~ v1_funct_2(X20,u1_struct_0(X18),u1_struct_0(X19))
        | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X18),u1_struct_0(X19))))
        | ~ l1_pre_topc(X19)
        | ~ l1_pre_topc(X18) )
      & ( m1_subset_1(esk6_3(X18,X19,X20),k1_zfmisc_1(u1_struct_0(X19)))
        | v5_pre_topc(X20,X18,X19)
        | ~ v1_funct_1(X20)
        | ~ v1_funct_2(X20,u1_struct_0(X18),u1_struct_0(X19))
        | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X18),u1_struct_0(X19))))
        | ~ l1_pre_topc(X19)
        | ~ l1_pre_topc(X18) )
      & ( v4_pre_topc(esk6_3(X18,X19,X20),X19)
        | v5_pre_topc(X20,X18,X19)
        | ~ v1_funct_1(X20)
        | ~ v1_funct_2(X20,u1_struct_0(X18),u1_struct_0(X19))
        | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X18),u1_struct_0(X19))))
        | ~ l1_pre_topc(X19)
        | ~ l1_pre_topc(X18) )
      & ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X18),u1_struct_0(X19),X20,esk6_3(X18,X19,X20)),X18)
        | v5_pre_topc(X20,X18,X19)
        | ~ v1_funct_1(X20)
        | ~ v1_funct_2(X20,u1_struct_0(X18),u1_struct_0(X19))
        | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X18),u1_struct_0(X19))))
        | ~ l1_pre_topc(X19)
        | ~ l1_pre_topc(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_pre_topc])])])])])).

cnf(c_0_36,negated_conjecture,
    ( v1_funct_2(esk5_0,u1_struct_0(esk1_0),u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_37,negated_conjecture,
    ( ~ v5_pre_topc(esk5_0,esk1_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_38,plain,(
    ! [X25] :
      ( ~ l1_struct_0(X25)
      | k2_struct_0(X25) = u1_struct_0(X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

cnf(c_0_39,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_40,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28])])).

fof(c_0_41,plain,(
    ! [X69,X70] :
      ( ~ v1_relat_1(X70)
      | r1_tarski(k10_relat_1(X70,X69),k1_relat_1(X70)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t167_relat_1])])).

cnf(c_0_42,plain,
    ( k10_relat_1(X1,X2) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_43,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

fof(c_0_44,plain,(
    ! [X13,X14] : k3_xboole_0(X13,X14) = k3_xboole_0(X14,X13) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_45,plain,(
    ! [X76,X77] :
      ( ~ r1_tarski(X76,X77)
      | k3_xboole_0(X76,X77) = X76 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_46,plain,
    ( r1_tarski(k2_relat_1(X1),X2)
    | ~ v5_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_47,negated_conjecture,
    ( v5_relat_1(esk3_0,u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

fof(c_0_48,plain,(
    ! [X73] :
      ( ~ v1_relat_1(X73)
      | k10_relat_1(X73,k2_relat_1(X73)) = k1_relat_1(X73) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t169_relat_1])])).

cnf(c_0_49,plain,
    ( v4_pre_topc(esk6_3(X1,X2,X3),X2)
    | v5_pre_topc(X3,X1,X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_50,negated_conjecture,
    ( v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk4_0)) ),
    inference(rw,[status(thm)],[c_0_36,c_0_24])).

cnf(c_0_51,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_52,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_53,negated_conjecture,
    ( ~ v5_pre_topc(esk3_0,esk1_0,esk4_0) ),
    inference(rw,[status(thm)],[c_0_37,c_0_24])).

cnf(c_0_54,plain,
    ( m1_subset_1(esk6_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X2)))
    | v5_pre_topc(X3,X1,X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

fof(c_0_55,plain,(
    ! [X32] :
      ( ~ l1_struct_0(X32)
      | m1_subset_1(k2_struct_0(X32),k1_zfmisc_1(u1_struct_0(X32))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_struct_0])])).

cnf(c_0_56,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_57,negated_conjecture,
    ( l1_struct_0(esk4_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_58,plain,
    ( r1_tarski(k10_relat_1(X1,X2),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_59,negated_conjecture,
    ( k10_relat_1(esk3_0,k3_xboole_0(k2_relat_1(esk3_0),X1)) = k10_relat_1(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_60,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_61,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_62,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk3_0),u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_43])])).

cnf(c_0_63,plain,
    ( k10_relat_1(X1,k2_relat_1(X1)) = k1_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

fof(c_0_64,plain,(
    ! [X66,X67,X68] :
      ( ~ v1_relat_1(X68)
      | ~ v1_funct_1(X68)
      | k10_relat_1(X68,k3_xboole_0(X66,X67)) = k3_xboole_0(k10_relat_1(X68,X66),k10_relat_1(X68,X67)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t137_funct_1])])).

fof(c_0_65,plain,(
    ! [X83,X84,X85,X87] :
      ( ( m1_subset_1(esk11_3(X83,X84,X85),k1_zfmisc_1(u1_struct_0(X83)))
        | ~ v4_pre_topc(X85,X84)
        | ~ m1_subset_1(X85,k1_zfmisc_1(u1_struct_0(X84)))
        | ~ m1_pre_topc(X84,X83)
        | ~ l1_pre_topc(X83) )
      & ( v4_pre_topc(esk11_3(X83,X84,X85),X83)
        | ~ v4_pre_topc(X85,X84)
        | ~ m1_subset_1(X85,k1_zfmisc_1(u1_struct_0(X84)))
        | ~ m1_pre_topc(X84,X83)
        | ~ l1_pre_topc(X83) )
      & ( k9_subset_1(u1_struct_0(X84),esk11_3(X83,X84,X85),k2_struct_0(X84)) = X85
        | ~ v4_pre_topc(X85,X84)
        | ~ m1_subset_1(X85,k1_zfmisc_1(u1_struct_0(X84)))
        | ~ m1_pre_topc(X84,X83)
        | ~ l1_pre_topc(X83) )
      & ( ~ m1_subset_1(X87,k1_zfmisc_1(u1_struct_0(X83)))
        | ~ v4_pre_topc(X87,X83)
        | k9_subset_1(u1_struct_0(X84),X87,k2_struct_0(X84)) != X85
        | v4_pre_topc(X85,X84)
        | ~ m1_subset_1(X85,k1_zfmisc_1(u1_struct_0(X84)))
        | ~ m1_pre_topc(X84,X83)
        | ~ l1_pre_topc(X83) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_pre_topc])])])])])).

cnf(c_0_66,negated_conjecture,
    ( v4_pre_topc(esk6_3(esk1_0,esk4_0,esk3_0),esk4_0)
    | ~ l1_pre_topc(esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_34]),c_0_51]),c_0_52])]),c_0_53])).

cnf(c_0_67,negated_conjecture,
    ( m1_subset_1(esk6_3(esk1_0,esk4_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ l1_pre_topc(esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_50]),c_0_34]),c_0_51]),c_0_52])]),c_0_53])).

fof(c_0_68,plain,(
    ! [X63,X64,X65] :
      ( ~ m1_subset_1(X65,k1_zfmisc_1(X63))
      | k9_subset_1(X63,X64,X65) = k3_xboole_0(X64,X65) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).

cnf(c_0_69,plain,
    ( m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_70,negated_conjecture,
    ( k2_struct_0(esk4_0) = u1_struct_0(esk4_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

fof(c_0_71,plain,(
    ! [X59,X60,X61,X62] :
      ( ~ m1_subset_1(X61,k1_zfmisc_1(k2_zfmisc_1(X59,X60)))
      | k8_relset_1(X59,X60,X61,X62) = k10_relat_1(X61,X62) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k8_relset_1])])).

cnf(c_0_72,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk3_0,X1),k1_relat_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_58,c_0_43])).

cnf(c_0_73,negated_conjecture,
    ( k10_relat_1(esk3_0,k3_xboole_0(X1,k2_relat_1(esk3_0))) = k10_relat_1(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_74,negated_conjecture,
    ( k3_xboole_0(u1_struct_0(esk4_0),k2_relat_1(esk3_0)) = k2_relat_1(esk3_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_60])).

cnf(c_0_75,negated_conjecture,
    ( k10_relat_1(esk3_0,k2_relat_1(esk3_0)) = k1_relat_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_63,c_0_43])).

cnf(c_0_76,plain,
    ( k10_relat_1(X1,k3_xboole_0(X2,X3)) = k3_xboole_0(k10_relat_1(X1,X2),k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_77,plain,
    ( k9_subset_1(u1_struct_0(X1),esk11_3(X2,X1,X3),k2_struct_0(X1)) = X3
    | ~ v4_pre_topc(X3,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_78,negated_conjecture,
    ( v4_pre_topc(esk6_3(esk1_0,esk4_0,esk3_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_66,c_0_40])])).

cnf(c_0_79,negated_conjecture,
    ( m1_subset_1(esk6_3(esk1_0,esk4_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_67,c_0_40])])).

cnf(c_0_80,plain,
    ( k9_subset_1(X2,X3,X1) = k3_xboole_0(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_81,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_57]),c_0_70])).

cnf(c_0_82,plain,
    ( k8_relset_1(X2,X3,X1,X4) = k10_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_83,plain,
    ( v4_pre_topc(esk11_3(X1,X2,X3),X1)
    | ~ v4_pre_topc(X3,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_84,plain,
    ( m1_subset_1(esk11_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_pre_topc(X3,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_85,negated_conjecture,
    ( k3_xboole_0(k10_relat_1(esk3_0,X1),k1_relat_1(esk3_0)) = k10_relat_1(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_61,c_0_72])).

cnf(c_0_86,negated_conjecture,
    ( k1_relat_1(esk3_0) = k10_relat_1(esk3_0,u1_struct_0(esk4_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_75])).

cnf(c_0_87,negated_conjecture,
    ( k3_xboole_0(k10_relat_1(esk3_0,X1),k10_relat_1(esk3_0,X2)) = k10_relat_1(esk3_0,k3_xboole_0(X1,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_43]),c_0_51])])).

cnf(c_0_88,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk4_0),esk11_3(X1,esk4_0,esk6_3(esk1_0,esk4_0,esk3_0)),u1_struct_0(esk4_0)) = esk6_3(esk1_0,esk4_0,esk3_0)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_70]),c_0_79])])).

cnf(c_0_89,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk4_0),X1,u1_struct_0(esk4_0)) = k3_xboole_0(X1,u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_80,c_0_81])).

cnf(c_0_90,plain,
    ( v4_pre_topc(k8_relset_1(u1_struct_0(X2),u1_struct_0(X3),X1,X4),X2)
    | ~ v5_pre_topc(X1,X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ v4_pre_topc(X4,X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_91,negated_conjecture,
    ( v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_92,negated_conjecture,
    ( v5_pre_topc(esk3_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_93,negated_conjecture,
    ( k8_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,X1) = k10_relat_1(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_82,c_0_31])).

cnf(c_0_94,negated_conjecture,
    ( v4_pre_topc(esk11_3(esk2_0,esk4_0,X1),esk2_0)
    | ~ v4_pre_topc(X1,esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_27]),c_0_28])])).

cnf(c_0_95,negated_conjecture,
    ( m1_subset_1(esk11_3(esk2_0,esk4_0,X1),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ v4_pre_topc(X1,esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_27]),c_0_28])])).

cnf(c_0_96,negated_conjecture,
    ( k10_relat_1(esk3_0,k3_xboole_0(X1,u1_struct_0(esk4_0))) = k10_relat_1(esk3_0,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_85,c_0_86]),c_0_87])).

cnf(c_0_97,negated_conjecture,
    ( k3_xboole_0(u1_struct_0(esk4_0),esk11_3(X1,esk4_0,esk6_3(esk1_0,esk4_0,esk3_0))) = esk6_3(esk1_0,esk4_0,esk3_0)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_88,c_0_89]),c_0_60])).

cnf(c_0_98,negated_conjecture,
    ( v4_pre_topc(k10_relat_1(esk3_0,X1),esk1_0)
    | ~ v4_pre_topc(X1,esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_91]),c_0_92]),c_0_31]),c_0_51]),c_0_28]),c_0_52])]),c_0_93])).

cnf(c_0_99,negated_conjecture,
    ( v4_pre_topc(esk11_3(esk2_0,esk4_0,esk6_3(esk1_0,esk4_0,esk3_0)),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_78]),c_0_79])])).

cnf(c_0_100,negated_conjecture,
    ( m1_subset_1(esk11_3(esk2_0,esk4_0,esk6_3(esk1_0,esk4_0,esk3_0)),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_78]),c_0_79])])).

cnf(c_0_101,negated_conjecture,
    ( k10_relat_1(esk3_0,k3_xboole_0(u1_struct_0(esk4_0),X1)) = k10_relat_1(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_96,c_0_60])).

cnf(c_0_102,negated_conjecture,
    ( k3_xboole_0(u1_struct_0(esk4_0),esk11_3(esk2_0,esk4_0,esk6_3(esk1_0,esk4_0,esk3_0))) = esk6_3(esk1_0,esk4_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_27]),c_0_28])])).

cnf(c_0_103,plain,
    ( v5_pre_topc(X3,X1,X2)
    | ~ v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,esk6_3(X1,X2,X3)),X1)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_104,negated_conjecture,
    ( k8_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk4_0),esk3_0,X1) = k10_relat_1(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_82,c_0_34])).

cnf(c_0_105,negated_conjecture,
    ( v4_pre_topc(k10_relat_1(esk3_0,esk11_3(esk2_0,esk4_0,esk6_3(esk1_0,esk4_0,esk3_0))),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_99]),c_0_100])])).

cnf(c_0_106,negated_conjecture,
    ( k10_relat_1(esk3_0,esk11_3(esk2_0,esk4_0,esk6_3(esk1_0,esk4_0,esk3_0))) = k10_relat_1(esk3_0,esk6_3(esk1_0,esk4_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_101,c_0_102])).

cnf(c_0_107,negated_conjecture,
    ( ~ v4_pre_topc(k10_relat_1(esk3_0,esk6_3(esk1_0,esk4_0,esk3_0)),esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_104]),c_0_34]),c_0_50]),c_0_51]),c_0_40]),c_0_52])]),c_0_53])).

cnf(c_0_108,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_105,c_0_106]),c_0_107]),
    [proof]).
%------------------------------------------------------------------------------
