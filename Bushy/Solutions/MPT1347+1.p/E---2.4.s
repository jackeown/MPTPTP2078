%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : tops_2__t72_tops_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:43 EDT 2019

% Result     : Theorem 2.88s
% Output     : CNFRefutation 2.88s
% Verified   : 
% Statistics : Number of formulae       :  166 (34922 expanded)
%              Number of clauses        :  120 (12182 expanded)
%              Number of leaves         :   23 (8628 expanded)
%              Depth                    :   29
%              Number of atoms          :  632 (434222 expanded)
%              Number of equality atoms :  135 (82366 expanded)
%              Maximal formula depth    :   20 (   4 average)
%              Maximal clause size      :   46 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t72_tops_2,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/tops_2__t72_tops_2.p',t72_tops_2)).

fof(d1_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( ( ( X2 = k1_xboole_0
           => X1 = k1_xboole_0 )
         => ( v1_funct_2(X3,X1,X2)
          <=> X1 = k1_relset_1(X1,X2,X3) ) )
        & ( X2 = k1_xboole_0
         => ( X1 = k1_xboole_0
            | ( v1_funct_2(X3,X1,X2)
            <=> X3 = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t72_tops_2.p',d1_funct_2)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t72_tops_2.p',fc2_struct_0)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t72_tops_2.p',fc1_xboole_0)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t72_tops_2.p',dt_l1_pre_topc)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t72_tops_2.p',redefinition_k2_relset_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t72_tops_2.p',cc1_relset_1)).

fof(redefinition_k7_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k7_relset_1(X1,X2,X3,X4) = k9_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t72_tops_2.p',redefinition_k7_relset_1)).

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
    file('/export/starexec/sandbox2/benchmark/tops_2__t72_tops_2.p',d5_tops_2)).

fof(t147_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( r1_tarski(X1,k2_relat_1(X2))
       => k9_relat_1(X2,k10_relat_1(X2,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t72_tops_2.p',t147_funct_1)).

fof(d3_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => k2_struct_0(X1) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t72_tops_2.p',d3_struct_0)).

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
    file('/export/starexec/sandbox2/benchmark/tops_2__t72_tops_2.p',d12_pre_topc)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t72_tops_2.p',t3_subset)).

fof(dt_k8_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => m1_subset_1(k8_relset_1(X1,X2,X3,X4),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t72_tops_2.p',dt_k8_relset_1)).

fof(redefinition_k8_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k8_relset_1(X1,X2,X3,X4) = k10_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t72_tops_2.p',redefinition_k8_relset_1)).

fof(dt_k2_tops_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( v1_funct_1(k2_tops_2(X1,X2,X3))
        & v1_funct_2(k2_tops_2(X1,X2,X3),X2,X1)
        & m1_subset_1(k2_tops_2(X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t72_tops_2.p',dt_k2_tops_2)).

fof(d4_tops_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( ( k2_relset_1(X1,X2,X3) = X2
          & v2_funct_1(X3) )
       => k2_tops_2(X1,X2,X3) = k2_funct_1(X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t72_tops_2.p',d4_tops_2)).

fof(t154_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( v2_funct_1(X2)
       => k9_relat_1(X2,X1) = k10_relat_1(k2_funct_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t72_tops_2.p',t154_funct_1)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t72_tops_2.p',redefinition_k1_relset_1)).

fof(t146_funct_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X1,k1_relat_1(X2))
       => r1_tarski(X1,k10_relat_1(X2,k9_relat_1(X2,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t72_tops_2.p',t146_funct_1)).

fof(t152_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( v2_funct_1(X2)
       => r1_tarski(k10_relat_1(X2,k9_relat_1(X2,X1)),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t72_tops_2.p',t152_funct_1)).

fof(dt_k7_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => m1_subset_1(k7_relset_1(X1,X2,X3,X4),k1_zfmisc_1(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t72_tops_2.p',dt_k7_relset_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t72_tops_2.p',d10_xboole_0)).

fof(c_0_23,negated_conjecture,(
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
                <=> ( k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) = k2_struct_0(X1)
                    & k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) = k2_struct_0(X2)
                    & v2_funct_1(X3)
                    & ! [X4] :
                        ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                       => ( v4_pre_topc(X4,X1)
                        <=> v4_pre_topc(k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4),X2) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t72_tops_2])).

fof(c_0_24,plain,(
    ! [X19,X20,X21] :
      ( ( ~ v1_funct_2(X21,X19,X20)
        | X19 = k1_relset_1(X19,X20,X21)
        | X20 = k1_xboole_0
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20))) )
      & ( X19 != k1_relset_1(X19,X20,X21)
        | v1_funct_2(X21,X19,X20)
        | X20 = k1_xboole_0
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20))) )
      & ( ~ v1_funct_2(X21,X19,X20)
        | X19 = k1_relset_1(X19,X20,X21)
        | X19 != k1_xboole_0
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20))) )
      & ( X19 != k1_relset_1(X19,X20,X21)
        | v1_funct_2(X21,X19,X20)
        | X19 != k1_xboole_0
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20))) )
      & ( ~ v1_funct_2(X21,X19,X20)
        | X21 = k1_xboole_0
        | X19 = k1_xboole_0
        | X20 != k1_xboole_0
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20))) )
      & ( X21 != k1_xboole_0
        | v1_funct_2(X21,X19,X20)
        | X19 = k1_xboole_0
        | X20 != k1_xboole_0
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

fof(c_0_25,negated_conjecture,(
    ! [X9] :
      ( l1_pre_topc(esk1_0)
      & ~ v2_struct_0(esk2_0)
      & l1_pre_topc(esk2_0)
      & v1_funct_1(esk3_0)
      & v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0))
      & m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))
      & ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
        | k1_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0) != k2_struct_0(esk1_0)
        | k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0) != k2_struct_0(esk2_0)
        | ~ v2_funct_1(esk3_0)
        | ~ v3_tops_2(esk3_0,esk1_0,esk2_0) )
      & ( ~ v4_pre_topc(esk4_0,esk1_0)
        | ~ v4_pre_topc(k7_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,esk4_0),esk2_0)
        | k1_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0) != k2_struct_0(esk1_0)
        | k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0) != k2_struct_0(esk2_0)
        | ~ v2_funct_1(esk3_0)
        | ~ v3_tops_2(esk3_0,esk1_0,esk2_0) )
      & ( v4_pre_topc(esk4_0,esk1_0)
        | v4_pre_topc(k7_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,esk4_0),esk2_0)
        | k1_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0) != k2_struct_0(esk1_0)
        | k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0) != k2_struct_0(esk2_0)
        | ~ v2_funct_1(esk3_0)
        | ~ v3_tops_2(esk3_0,esk1_0,esk2_0) )
      & ( k1_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0) = k2_struct_0(esk1_0)
        | v3_tops_2(esk3_0,esk1_0,esk2_0) )
      & ( k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0) = k2_struct_0(esk2_0)
        | v3_tops_2(esk3_0,esk1_0,esk2_0) )
      & ( v2_funct_1(esk3_0)
        | v3_tops_2(esk3_0,esk1_0,esk2_0) )
      & ( ~ v4_pre_topc(X9,esk1_0)
        | v4_pre_topc(k7_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,X9),esk2_0)
        | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(esk1_0)))
        | v3_tops_2(esk3_0,esk1_0,esk2_0) )
      & ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,X9),esk2_0)
        | v4_pre_topc(X9,esk1_0)
        | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(esk1_0)))
        | v3_tops_2(esk3_0,esk1_0,esk2_0) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_23])])])])])])).

cnf(c_0_26,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_27,negated_conjecture,
    ( v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_29,negated_conjecture,
    ( k1_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0) = k2_struct_0(esk1_0)
    | v3_tops_2(esk3_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_30,negated_conjecture,
    ( k1_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0) = u1_struct_0(esk1_0)
    | k1_xboole_0 = u1_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28])])).

fof(c_0_31,plain,(
    ! [X95] :
      ( v2_struct_0(X95)
      | ~ l1_struct_0(X95)
      | ~ v1_xboole_0(u1_struct_0(X95)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_32,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_33,negated_conjecture,
    ( k2_struct_0(esk1_0) = u1_struct_0(esk1_0)
    | k1_xboole_0 = u1_struct_0(esk2_0)
    | v3_tops_2(esk3_0,esk1_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_34,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_35,negated_conjecture,
    ( k2_struct_0(esk1_0) = u1_struct_0(esk1_0)
    | v1_xboole_0(u1_struct_0(esk2_0))
    | v3_tops_2(esk3_0,esk1_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_36,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_37,plain,(
    ! [X48] :
      ( ~ l1_pre_topc(X48)
      | l1_struct_0(X48) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

fof(c_0_38,plain,(
    ! [X56,X57,X58] :
      ( ~ m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(X56,X57)))
      | k2_relset_1(X56,X57,X58) = k2_relat_1(X58) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

fof(c_0_39,plain,(
    ! [X92,X93,X94] :
      ( ~ m1_subset_1(X94,k1_zfmisc_1(k2_zfmisc_1(X92,X93)))
      | v1_relat_1(X94) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_40,plain,(
    ! [X59,X60,X61,X62] :
      ( ~ m1_subset_1(X61,k1_zfmisc_1(k2_zfmisc_1(X59,X60)))
      | k7_relset_1(X59,X60,X61,X62) = k9_relat_1(X61,X62) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).

fof(c_0_41,plain,(
    ! [X26,X27,X28] :
      ( ( k1_relset_1(u1_struct_0(X26),u1_struct_0(X27),X28) = k2_struct_0(X26)
        | ~ v3_tops_2(X28,X26,X27)
        | ~ v1_funct_1(X28)
        | ~ v1_funct_2(X28,u1_struct_0(X26),u1_struct_0(X27))
        | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X26),u1_struct_0(X27))))
        | ~ l1_pre_topc(X27)
        | ~ l1_pre_topc(X26) )
      & ( k2_relset_1(u1_struct_0(X26),u1_struct_0(X27),X28) = k2_struct_0(X27)
        | ~ v3_tops_2(X28,X26,X27)
        | ~ v1_funct_1(X28)
        | ~ v1_funct_2(X28,u1_struct_0(X26),u1_struct_0(X27))
        | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X26),u1_struct_0(X27))))
        | ~ l1_pre_topc(X27)
        | ~ l1_pre_topc(X26) )
      & ( v2_funct_1(X28)
        | ~ v3_tops_2(X28,X26,X27)
        | ~ v1_funct_1(X28)
        | ~ v1_funct_2(X28,u1_struct_0(X26),u1_struct_0(X27))
        | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X26),u1_struct_0(X27))))
        | ~ l1_pre_topc(X27)
        | ~ l1_pre_topc(X26) )
      & ( v5_pre_topc(X28,X26,X27)
        | ~ v3_tops_2(X28,X26,X27)
        | ~ v1_funct_1(X28)
        | ~ v1_funct_2(X28,u1_struct_0(X26),u1_struct_0(X27))
        | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X26),u1_struct_0(X27))))
        | ~ l1_pre_topc(X27)
        | ~ l1_pre_topc(X26) )
      & ( v5_pre_topc(k2_tops_2(u1_struct_0(X26),u1_struct_0(X27),X28),X27,X26)
        | ~ v3_tops_2(X28,X26,X27)
        | ~ v1_funct_1(X28)
        | ~ v1_funct_2(X28,u1_struct_0(X26),u1_struct_0(X27))
        | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X26),u1_struct_0(X27))))
        | ~ l1_pre_topc(X27)
        | ~ l1_pre_topc(X26) )
      & ( k1_relset_1(u1_struct_0(X26),u1_struct_0(X27),X28) != k2_struct_0(X26)
        | k2_relset_1(u1_struct_0(X26),u1_struct_0(X27),X28) != k2_struct_0(X27)
        | ~ v2_funct_1(X28)
        | ~ v5_pre_topc(X28,X26,X27)
        | ~ v5_pre_topc(k2_tops_2(u1_struct_0(X26),u1_struct_0(X27),X28),X27,X26)
        | v3_tops_2(X28,X26,X27)
        | ~ v1_funct_1(X28)
        | ~ v1_funct_2(X28,u1_struct_0(X26),u1_struct_0(X27))
        | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X26),u1_struct_0(X27))))
        | ~ l1_pre_topc(X27)
        | ~ l1_pre_topc(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_tops_2])])])])).

cnf(c_0_42,negated_conjecture,
    ( k2_struct_0(esk1_0) = u1_struct_0(esk1_0)
    | v3_tops_2(esk3_0,esk1_0,esk2_0)
    | ~ l1_struct_0(esk2_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36])).

cnf(c_0_43,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_44,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_45,plain,(
    ! [X69,X70] :
      ( ~ v1_relat_1(X70)
      | ~ v1_funct_1(X70)
      | ~ r1_tarski(X69,k2_relat_1(X70))
      | k9_relat_1(X70,k10_relat_1(X70,X69)) = X69 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t147_funct_1])])).

cnf(c_0_46,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_47,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_48,plain,
    ( k7_relset_1(X2,X3,X1,X4) = k9_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_49,plain,
    ( k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) = k2_struct_0(X1)
    | ~ v3_tops_2(X3,X1,X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_50,negated_conjecture,
    ( k2_struct_0(esk1_0) = u1_struct_0(esk1_0)
    | v3_tops_2(esk3_0,esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_44])])).

cnf(c_0_51,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_52,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_53,plain,
    ( k9_relat_1(X1,k10_relat_1(X1,X2)) = X2
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r1_tarski(X2,k2_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_54,negated_conjecture,
    ( k2_relat_1(esk3_0) = k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_28])).

cnf(c_0_55,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_28])).

cnf(c_0_56,negated_conjecture,
    ( k9_relat_1(esk3_0,X1) = k7_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_48,c_0_28])).

fof(c_0_57,plain,(
    ! [X22] :
      ( ~ l1_struct_0(X22)
      | k2_struct_0(X22) = u1_struct_0(X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

fof(c_0_58,plain,(
    ! [X14,X15,X16,X17] :
      ( ( ~ v5_pre_topc(X16,X14,X15)
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X15)))
        | ~ v4_pre_topc(X17,X15)
        | v4_pre_topc(k8_relset_1(u1_struct_0(X14),u1_struct_0(X15),X16,X17),X14)
        | ~ v1_funct_1(X16)
        | ~ v1_funct_2(X16,u1_struct_0(X14),u1_struct_0(X15))
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X14),u1_struct_0(X15))))
        | ~ l1_pre_topc(X15)
        | ~ l1_pre_topc(X14) )
      & ( m1_subset_1(esk5_3(X14,X15,X16),k1_zfmisc_1(u1_struct_0(X15)))
        | v5_pre_topc(X16,X14,X15)
        | ~ v1_funct_1(X16)
        | ~ v1_funct_2(X16,u1_struct_0(X14),u1_struct_0(X15))
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X14),u1_struct_0(X15))))
        | ~ l1_pre_topc(X15)
        | ~ l1_pre_topc(X14) )
      & ( v4_pre_topc(esk5_3(X14,X15,X16),X15)
        | v5_pre_topc(X16,X14,X15)
        | ~ v1_funct_1(X16)
        | ~ v1_funct_2(X16,u1_struct_0(X14),u1_struct_0(X15))
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X14),u1_struct_0(X15))))
        | ~ l1_pre_topc(X15)
        | ~ l1_pre_topc(X14) )
      & ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X14),u1_struct_0(X15),X16,esk5_3(X14,X15,X16)),X14)
        | v5_pre_topc(X16,X14,X15)
        | ~ v1_funct_1(X16)
        | ~ v1_funct_2(X16,u1_struct_0(X14),u1_struct_0(X15))
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X14),u1_struct_0(X15))))
        | ~ l1_pre_topc(X15)
        | ~ l1_pre_topc(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_pre_topc])])])])])).

cnf(c_0_59,negated_conjecture,
    ( k1_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0) = k2_struct_0(esk1_0)
    | k2_struct_0(esk1_0) = u1_struct_0(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_28]),c_0_27]),c_0_51]),c_0_44]),c_0_52])])).

cnf(c_0_60,negated_conjecture,
    ( k7_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,k10_relat_1(esk3_0,X1)) = X1
    | ~ r1_tarski(X1,k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0)) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_55]),c_0_51])]),c_0_56])).

cnf(c_0_61,negated_conjecture,
    ( k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0) = k2_struct_0(esk2_0)
    | v3_tops_2(esk3_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_62,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

fof(c_0_63,plain,(
    ! [X79,X80] :
      ( ( ~ m1_subset_1(X79,k1_zfmisc_1(X80))
        | r1_tarski(X79,X80) )
      & ( ~ r1_tarski(X79,X80)
        | m1_subset_1(X79,k1_zfmisc_1(X80)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_64,plain,
    ( m1_subset_1(esk5_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X2)))
    | v5_pre_topc(X3,X1,X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

fof(c_0_65,plain,(
    ! [X44,X45,X46,X47] :
      ( ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X45)))
      | m1_subset_1(k8_relset_1(X44,X45,X46,X47),k1_zfmisc_1(X44)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k8_relset_1])])).

fof(c_0_66,plain,(
    ! [X63,X64,X65,X66] :
      ( ~ m1_subset_1(X65,k1_zfmisc_1(k2_zfmisc_1(X63,X64)))
      | k8_relset_1(X63,X64,X65,X66) = k10_relat_1(X65,X66) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k8_relset_1])])).

cnf(c_0_67,negated_conjecture,
    ( k2_struct_0(esk1_0) = u1_struct_0(esk1_0)
    | k1_xboole_0 = u1_struct_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_59])).

fof(c_0_68,plain,(
    ! [X37,X38,X39] :
      ( ( v1_funct_1(k2_tops_2(X37,X38,X39))
        | ~ v1_funct_1(X39)
        | ~ v1_funct_2(X39,X37,X38)
        | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38))) )
      & ( v1_funct_2(k2_tops_2(X37,X38,X39),X38,X37)
        | ~ v1_funct_1(X39)
        | ~ v1_funct_2(X39,X37,X38)
        | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38))) )
      & ( m1_subset_1(k2_tops_2(X37,X38,X39),k1_zfmisc_1(k2_zfmisc_1(X38,X37)))
        | ~ v1_funct_1(X39)
        | ~ v1_funct_2(X39,X37,X38)
        | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_tops_2])])])).

fof(c_0_69,plain,(
    ! [X23,X24,X25] :
      ( ~ v1_funct_1(X25)
      | ~ v1_funct_2(X25,X23,X24)
      | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))
      | k2_relset_1(X23,X24,X25) != X24
      | ~ v2_funct_1(X25)
      | k2_tops_2(X23,X24,X25) = k2_funct_1(X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tops_2])])).

cnf(c_0_70,negated_conjecture,
    ( k7_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,k10_relat_1(esk3_0,X1)) = X1
    | v3_tops_2(esk3_0,esk1_0,esk2_0)
    | ~ r1_tarski(X1,k2_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_71,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_62,c_0_43])).

cnf(c_0_72,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_73,negated_conjecture,
    ( v5_pre_topc(esk3_0,esk1_0,esk2_0)
    | m1_subset_1(esk5_3(esk1_0,esk2_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_27]),c_0_28]),c_0_51]),c_0_44]),c_0_52])])).

cnf(c_0_74,plain,
    ( m1_subset_1(k8_relset_1(X2,X3,X1,X4),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_75,plain,
    ( k8_relset_1(X2,X3,X1,X4) = k10_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_76,negated_conjecture,
    ( k2_struct_0(esk1_0) = u1_struct_0(esk1_0)
    | v1_xboole_0(u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_67])).

cnf(c_0_77,plain,
    ( m1_subset_1(k2_tops_2(X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_78,plain,
    ( k2_tops_2(X2,X3,X1) = k2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | k2_relset_1(X2,X3,X1) != X3
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_79,negated_conjecture,
    ( v2_funct_1(esk3_0)
    | v3_tops_2(esk3_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_80,negated_conjecture,
    ( k7_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,k10_relat_1(esk3_0,X1)) = X1
    | v3_tops_2(esk3_0,esk1_0,esk2_0)
    | ~ r1_tarski(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_44])])).

cnf(c_0_81,negated_conjecture,
    ( v5_pre_topc(esk3_0,esk1_0,esk2_0)
    | r1_tarski(esk5_3(esk1_0,esk2_0,esk3_0),u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_82,negated_conjecture,
    ( m1_subset_1(k8_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,X1),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_74,c_0_28])).

cnf(c_0_83,negated_conjecture,
    ( k8_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,X1) = k10_relat_1(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_75,c_0_28])).

cnf(c_0_84,plain,
    ( v4_pre_topc(esk5_3(X1,X2,X3),X2)
    | v5_pre_topc(X3,X1,X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_85,plain,
    ( v5_pre_topc(X3,X1,X2)
    | ~ v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,esk5_3(X1,X2,X3)),X1)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_86,negated_conjecture,
    ( k2_struct_0(esk1_0) = u1_struct_0(esk1_0)
    | ~ l1_struct_0(esk2_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_76]),c_0_36])).

cnf(c_0_87,negated_conjecture,
    ( m1_subset_1(k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_27]),c_0_28]),c_0_51])])).

cnf(c_0_88,plain,
    ( v1_funct_2(k2_tops_2(X1,X2,X3),X2,X1)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_89,plain,
    ( v1_funct_1(k2_tops_2(X1,X2,X3))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

fof(c_0_90,plain,(
    ! [X73,X74] :
      ( ~ v1_relat_1(X74)
      | ~ v1_funct_1(X74)
      | ~ v2_funct_1(X74)
      | k9_relat_1(X74,X73) = k10_relat_1(k2_funct_1(X74),X73) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t154_funct_1])])).

cnf(c_0_91,negated_conjecture,
    ( k2_funct_1(esk3_0) = k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0)
    | v3_tops_2(esk3_0,esk1_0,esk2_0)
    | k2_struct_0(esk2_0) != u1_struct_0(esk2_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_61]),c_0_28]),c_0_27]),c_0_51])]),c_0_79])).

cnf(c_0_92,negated_conjecture,
    ( v4_pre_topc(X1,esk1_0)
    | v3_tops_2(esk3_0,esk1_0,esk2_0)
    | ~ v4_pre_topc(k7_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,X1),esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_93,negated_conjecture,
    ( k7_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,k10_relat_1(esk3_0,esk5_3(esk1_0,esk2_0,esk3_0))) = esk5_3(esk1_0,esk2_0,esk3_0)
    | v5_pre_topc(esk3_0,esk1_0,esk2_0)
    | v3_tops_2(esk3_0,esk1_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_80,c_0_81])).

cnf(c_0_94,negated_conjecture,
    ( m1_subset_1(k10_relat_1(esk3_0,X1),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(rw,[status(thm)],[c_0_82,c_0_83])).

cnf(c_0_95,negated_conjecture,
    ( v5_pre_topc(esk3_0,esk1_0,esk2_0)
    | v4_pre_topc(esk5_3(esk1_0,esk2_0,esk3_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_27]),c_0_28]),c_0_51]),c_0_44]),c_0_52])])).

cnf(c_0_96,negated_conjecture,
    ( v5_pre_topc(esk3_0,esk1_0,esk2_0)
    | ~ v4_pre_topc(k10_relat_1(esk3_0,esk5_3(esk1_0,esk2_0,esk3_0)),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_83]),c_0_28]),c_0_27]),c_0_51]),c_0_44]),c_0_52])])).

cnf(c_0_97,negated_conjecture,
    ( k2_struct_0(esk1_0) = u1_struct_0(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_43]),c_0_44])])).

cnf(c_0_98,negated_conjecture,
    ( k8_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0),X1) = k10_relat_1(k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0),X1) ),
    inference(spm,[status(thm)],[c_0_75,c_0_87])).

cnf(c_0_99,negated_conjecture,
    ( v1_funct_2(k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0),u1_struct_0(esk2_0),u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_27]),c_0_28]),c_0_51])])).

cnf(c_0_100,negated_conjecture,
    ( v1_funct_1(k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_27]),c_0_28]),c_0_51])])).

cnf(c_0_101,plain,
    ( k9_relat_1(X1,X2) = k10_relat_1(k2_funct_1(X1),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_90])).

cnf(c_0_102,negated_conjecture,
    ( k2_funct_1(esk3_0) = k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0)
    | v3_tops_2(esk3_0,esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_71]),c_0_44])])).

cnf(c_0_103,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_104,negated_conjecture,
    ( v5_pre_topc(esk3_0,esk1_0,esk2_0)
    | v3_tops_2(esk3_0,esk1_0,esk2_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_93]),c_0_94])]),c_0_95]),c_0_96])).

cnf(c_0_105,negated_conjecture,
    ( k1_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0) = u1_struct_0(esk1_0)
    | v3_tops_2(esk3_0,esk1_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_29,c_0_97])).

cnf(c_0_106,negated_conjecture,
    ( v5_pre_topc(k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0),esk2_0,esk1_0)
    | ~ v4_pre_topc(k10_relat_1(k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0),esk5_3(esk2_0,esk1_0,k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0))),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_98]),c_0_87]),c_0_99]),c_0_100]),c_0_52]),c_0_44])])).

cnf(c_0_107,negated_conjecture,
    ( k10_relat_1(k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0),X1) = k7_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,X1)
    | v3_tops_2(esk3_0,esk1_0,esk2_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_102]),c_0_56]),c_0_55]),c_0_51])]),c_0_79])).

cnf(c_0_108,negated_conjecture,
    ( v3_tops_2(esk3_0,esk1_0,esk2_0)
    | ~ v5_pre_topc(k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0),esk2_0,esk1_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_104]),c_0_97]),c_0_28]),c_0_27]),c_0_51]),c_0_44]),c_0_52])]),c_0_79]),c_0_61]),c_0_105])).

fof(c_0_109,plain,(
    ! [X53,X54,X55] :
      ( ~ m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X53,X54)))
      | k1_relset_1(X53,X54,X55) = k1_relat_1(X55) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_110,negated_conjecture,
    ( v4_pre_topc(k7_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,X1),esk2_0)
    | v3_tops_2(esk3_0,esk1_0,esk2_0)
    | ~ v4_pre_topc(X1,esk1_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_111,negated_conjecture,
    ( v5_pre_topc(k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0),esk2_0,esk1_0)
    | v4_pre_topc(esk5_3(esk2_0,esk1_0,k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0)),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_99]),c_0_100]),c_0_52]),c_0_44])]),c_0_87])])).

cnf(c_0_112,negated_conjecture,
    ( v5_pre_topc(k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0),esk2_0,esk1_0)
    | m1_subset_1(esk5_3(esk2_0,esk1_0,k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0)),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_99]),c_0_100]),c_0_52]),c_0_44])]),c_0_87])])).

cnf(c_0_113,negated_conjecture,
    ( v3_tops_2(esk3_0,esk1_0,esk2_0)
    | ~ v4_pre_topc(k7_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,esk5_3(esk2_0,esk1_0,k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0))),esk2_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_107]),c_0_108])).

fof(c_0_114,plain,(
    ! [X67,X68] :
      ( ~ v1_relat_1(X68)
      | ~ r1_tarski(X67,k1_relat_1(X68))
      | r1_tarski(X67,k10_relat_1(X68,k9_relat_1(X68,X67))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_funct_1])])).

cnf(c_0_115,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_109])).

cnf(c_0_116,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | k1_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0) != k2_struct_0(esk1_0)
    | k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0) != k2_struct_0(esk2_0)
    | ~ v2_funct_1(esk3_0)
    | ~ v3_tops_2(esk3_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_117,negated_conjecture,
    ( v3_tops_2(esk3_0,esk1_0,esk2_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_110,c_0_111]),c_0_112]),c_0_113]),c_0_108])).

cnf(c_0_118,plain,
    ( k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) = k2_struct_0(X2)
    | ~ v3_tops_2(X3,X1,X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_119,plain,
    ( v2_funct_1(X1)
    | ~ v3_tops_2(X1,X2,X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_120,plain,
    ( r1_tarski(X2,k10_relat_1(X1,k9_relat_1(X1,X2)))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_114])).

cnf(c_0_121,negated_conjecture,
    ( k1_relat_1(esk3_0) = k1_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_115,c_0_28])).

cnf(c_0_122,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | k1_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0) != u1_struct_0(esk1_0)
    | k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0) != k2_struct_0(esk2_0)
    | ~ v2_funct_1(esk3_0)
    | ~ v3_tops_2(esk3_0,esk1_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_116,c_0_97])).

cnf(c_0_123,negated_conjecture,
    ( k1_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0) = u1_struct_0(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_117]),c_0_97]),c_0_28]),c_0_27]),c_0_51]),c_0_44]),c_0_52])])).

cnf(c_0_124,negated_conjecture,
    ( k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0) = k2_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_118,c_0_117]),c_0_28]),c_0_27]),c_0_51]),c_0_44]),c_0_52])])).

cnf(c_0_125,negated_conjecture,
    ( v2_funct_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119,c_0_117]),c_0_28]),c_0_27]),c_0_51]),c_0_44]),c_0_52])])).

cnf(c_0_126,negated_conjecture,
    ( r1_tarski(X1,k10_relat_1(esk3_0,k7_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,X1)))
    | ~ r1_tarski(X1,k1_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0)) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120,c_0_121]),c_0_55])]),c_0_56])).

cnf(c_0_127,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_122,c_0_117])]),c_0_123]),c_0_124]),c_0_125])])).

fof(c_0_128,plain,(
    ! [X71,X72] :
      ( ~ v1_relat_1(X72)
      | ~ v1_funct_1(X72)
      | ~ v2_funct_1(X72)
      | r1_tarski(k10_relat_1(X72,k9_relat_1(X72,X71)),X71) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t152_funct_1])])).

cnf(c_0_129,plain,
    ( v5_pre_topc(X1,X2,X3)
    | ~ v3_tops_2(X1,X2,X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_130,negated_conjecture,
    ( v4_pre_topc(esk4_0,esk1_0)
    | v4_pre_topc(k7_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,esk4_0),esk2_0)
    | k1_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0) != k2_struct_0(esk1_0)
    | k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0) != k2_struct_0(esk2_0)
    | ~ v2_funct_1(esk3_0)
    | ~ v3_tops_2(esk3_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_131,plain,(
    ! [X40,X41,X42,X43] :
      ( ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41)))
      | m1_subset_1(k7_relset_1(X40,X41,X42,X43),k1_zfmisc_1(X41)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relset_1])])).

fof(c_0_132,plain,(
    ! [X12,X13] :
      ( ( r1_tarski(X12,X13)
        | X12 != X13 )
      & ( r1_tarski(X13,X12)
        | X12 != X13 )
      & ( ~ r1_tarski(X12,X13)
        | ~ r1_tarski(X13,X12)
        | X12 = X13 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_133,negated_conjecture,
    ( k1_xboole_0 = u1_struct_0(esk2_0)
    | r1_tarski(X1,k10_relat_1(esk3_0,k7_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,X1)))
    | ~ r1_tarski(X1,u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_126,c_0_30])).

cnf(c_0_134,negated_conjecture,
    ( r1_tarski(esk4_0,u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_72,c_0_127])).

cnf(c_0_135,plain,
    ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X2)),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_128])).

cnf(c_0_136,plain,
    ( v4_pre_topc(k8_relset_1(u1_struct_0(X2),u1_struct_0(X3),X1,X4),X2)
    | ~ v5_pre_topc(X1,X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ v4_pre_topc(X4,X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_137,negated_conjecture,
    ( v5_pre_topc(esk3_0,esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_129,c_0_117]),c_0_28]),c_0_27]),c_0_51]),c_0_44]),c_0_52])])).

cnf(c_0_138,negated_conjecture,
    ( v4_pre_topc(k7_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,esk4_0),esk2_0)
    | v4_pre_topc(esk4_0,esk1_0)
    | k1_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0) != u1_struct_0(esk1_0)
    | k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0) != k2_struct_0(esk2_0)
    | ~ v2_funct_1(esk3_0)
    | ~ v3_tops_2(esk3_0,esk1_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_130,c_0_97])).

cnf(c_0_139,plain,
    ( m1_subset_1(k7_relset_1(X2,X3,X1,X4),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_131])).

cnf(c_0_140,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_132])).

cnf(c_0_141,negated_conjecture,
    ( k1_xboole_0 = u1_struct_0(esk2_0)
    | r1_tarski(esk4_0,k10_relat_1(esk3_0,k7_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,esk4_0))) ),
    inference(spm,[status(thm)],[c_0_133,c_0_134])).

cnf(c_0_142,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk3_0,k7_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,X1)),X1)
    | ~ v2_funct_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_135,c_0_56]),c_0_55]),c_0_51])])).

cnf(c_0_143,plain,
    ( v5_pre_topc(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3),X2,X1)
    | ~ v3_tops_2(X3,X1,X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_144,negated_conjecture,
    ( v4_pre_topc(k10_relat_1(esk3_0,X1),esk1_0)
    | ~ v4_pre_topc(X1,esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_136,c_0_137]),c_0_83]),c_0_28]),c_0_27]),c_0_51]),c_0_44]),c_0_52])])).

cnf(c_0_145,negated_conjecture,
    ( v4_pre_topc(k7_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,esk4_0),esk2_0)
    | v4_pre_topc(esk4_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_138,c_0_117])]),c_0_123]),c_0_124]),c_0_125])])).

cnf(c_0_146,negated_conjecture,
    ( m1_subset_1(k7_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,X1),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_139,c_0_28])).

cnf(c_0_147,negated_conjecture,
    ( k10_relat_1(esk3_0,k7_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,esk4_0)) = esk4_0
    | k1_xboole_0 = u1_struct_0(esk2_0)
    | ~ r1_tarski(k10_relat_1(esk3_0,k7_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,esk4_0)),esk4_0) ),
    inference(spm,[status(thm)],[c_0_140,c_0_141])).

cnf(c_0_148,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk3_0,k7_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,X1)),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_142,c_0_125])])).

cnf(c_0_149,negated_conjecture,
    ( ~ v4_pre_topc(esk4_0,esk1_0)
    | ~ v4_pre_topc(k7_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,esk4_0),esk2_0)
    | k1_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0) != k2_struct_0(esk1_0)
    | k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0) != k2_struct_0(esk2_0)
    | ~ v2_funct_1(esk3_0)
    | ~ v3_tops_2(esk3_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_150,negated_conjecture,
    ( v5_pre_topc(k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0),esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_143,c_0_117]),c_0_28]),c_0_27]),c_0_51]),c_0_44]),c_0_52])])).

cnf(c_0_151,negated_conjecture,
    ( v4_pre_topc(k10_relat_1(esk3_0,k7_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,esk4_0)),esk1_0)
    | v4_pre_topc(esk4_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_144,c_0_145]),c_0_146])])).

cnf(c_0_152,negated_conjecture,
    ( k10_relat_1(esk3_0,k7_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,esk4_0)) = esk4_0
    | k1_xboole_0 = u1_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_147,c_0_148])])).

cnf(c_0_153,negated_conjecture,
    ( k2_funct_1(esk3_0) = k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0)
    | k2_struct_0(esk2_0) != u1_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_124]),c_0_125]),c_0_28]),c_0_27]),c_0_51])])).

cnf(c_0_154,negated_conjecture,
    ( k1_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0) != u1_struct_0(esk1_0)
    | k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0) != k2_struct_0(esk2_0)
    | ~ v4_pre_topc(k7_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,esk4_0),esk2_0)
    | ~ v4_pre_topc(esk4_0,esk1_0)
    | ~ v2_funct_1(esk3_0)
    | ~ v3_tops_2(esk3_0,esk1_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_149,c_0_97])).

cnf(c_0_155,negated_conjecture,
    ( v4_pre_topc(k10_relat_1(k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0),X1),esk2_0)
    | ~ v4_pre_topc(X1,esk1_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_136,c_0_150]),c_0_98]),c_0_87]),c_0_99]),c_0_100]),c_0_52]),c_0_44])])).

cnf(c_0_156,negated_conjecture,
    ( k1_xboole_0 = u1_struct_0(esk2_0)
    | v4_pre_topc(esk4_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_151,c_0_152])).

cnf(c_0_157,negated_conjecture,
    ( k2_funct_1(esk3_0) = k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_153,c_0_71]),c_0_44])])).

cnf(c_0_158,negated_conjecture,
    ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,esk4_0),esk2_0)
    | ~ v4_pre_topc(esk4_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_154,c_0_117])]),c_0_123]),c_0_124]),c_0_125])])).

cnf(c_0_159,negated_conjecture,
    ( k1_xboole_0 = u1_struct_0(esk2_0)
    | v4_pre_topc(k10_relat_1(k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0),esk4_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_155,c_0_156]),c_0_127])])).

cnf(c_0_160,negated_conjecture,
    ( k10_relat_1(k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0),X1) = k7_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_157]),c_0_56]),c_0_55]),c_0_125]),c_0_51])])).

cnf(c_0_161,negated_conjecture,
    ( k1_xboole_0 = u1_struct_0(esk2_0)
    | ~ v4_pre_topc(k7_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,esk4_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_158,c_0_156])).

cnf(c_0_162,negated_conjecture,
    ( k1_xboole_0 = u1_struct_0(esk2_0) ),
    inference(csr,[status(thm)],[inference(rw,[status(thm)],[c_0_159,c_0_160]),c_0_161])).

cnf(c_0_163,plain,
    ( v1_xboole_0(u1_struct_0(esk2_0)) ),
    inference(rw,[status(thm)],[c_0_32,c_0_162])).

cnf(c_0_164,plain,
    ( ~ l1_struct_0(esk2_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_163]),c_0_36])).

cnf(c_0_165,plain,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_164,c_0_43]),c_0_44])]),
    [proof]).
%------------------------------------------------------------------------------
