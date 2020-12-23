%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1345+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:05 EST 2020

% Result     : Theorem 18.97s
% Output     : CNFRefutation 18.97s
% Verified   : 
% Statistics : Number of formulae       :  156 (2197 expanded)
%              Number of clauses        :   97 ( 785 expanded)
%              Number of leaves         :   29 ( 546 expanded)
%              Depth                    :   12
%              Number of atoms          :  520 (11909 expanded)
%              Number of equality atoms :  106 ( 542 expanded)
%              Maximal formula depth    :   20 (   4 average)
%              Maximal clause size      :   46 (   2 average)
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

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT016+2.ax',dt_l1_pre_topc)).

fof(cc2_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT007+2.ax',cc2_relat_1)).

fof(fc6_relat_1,axiom,(
    ! [X1,X2] : v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT007+2.ax',fc6_relat_1)).

fof(redefinition_k3_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k3_relset_1(X1,X2,X3) = k4_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT011+2.ax',redefinition_k3_relset_1)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT016+2.ax',fc2_struct_0)).

fof(d9_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => k2_funct_1(X1) = k4_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT008+2.ax',d9_funct_1)).

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

fof(t55_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => ( k2_relat_1(X1) = k1_relat_1(k2_funct_1(X1))
          & k1_relat_1(X1) = k2_relat_1(k2_funct_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT008+2.ax',t55_funct_1)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT011+2.ax',redefinition_k2_relset_1)).

fof(d3_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => k2_struct_0(X1) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT016+2.ax',d3_struct_0)).

fof(dt_k3_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => m1_subset_1(k3_relset_1(X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT011+2.ax',dt_k3_relset_1)).

fof(cc5_funct_2,axiom,(
    ! [X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
         => ( ( v1_funct_1(X3)
              & v1_funct_2(X3,X1,X2) )
           => ( v1_funct_1(X3)
              & v1_partfun1(X3,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT014+2.ax',cc5_funct_2)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT011+2.ax',cc2_relset_1)).

fof(rc4_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ? [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
          & ~ v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT016+2.ax',rc4_struct_0)).

fof(t169_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,k2_relat_1(X1)) = k1_relat_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT007+2.ax',t169_relat_1)).

fof(d4_partfun1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v4_relat_1(X2,X1) )
     => ( v1_partfun1(X2,X1)
      <=> k1_relat_1(X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT014+2.ax',d4_partfun1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT006+2.ax',t3_subset)).

fof(involutiveness_k4_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k4_relat_1(k4_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT007+2.ax',involutiveness_k4_relat_1)).

fof(dt_k2_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_relat_1(k2_funct_1(X1))
        & v1_funct_1(k2_funct_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT008+2.ax',dt_k2_funct_1)).

fof(t68_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ~ v1_xboole_0(X3)
     => ~ ( r1_tarski(X3,X1)
          & r1_tarski(X3,X2)
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT002+2.ax',t68_xboole_1)).

fof(cc1_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( ( v1_funct_1(X3)
          & v1_partfun1(X3,X1) )
       => ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT014+2.ax',cc1_funct_2)).

fof(t173_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( k10_relat_1(X2,X1) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT007+2.ax',t173_relat_1)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT011+2.ax',redefinition_k1_relset_1)).

fof(t65_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => k2_funct_1(k2_funct_1(X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT008+2.ax',t65_funct_1)).

fof(fc6_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1)
        & v2_funct_1(X1) )
     => ( v1_relat_1(k2_funct_1(X1))
        & v1_funct_1(k2_funct_1(X1))
        & v2_funct_1(k2_funct_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT008+2.ax',fc6_funct_1)).

fof(t24_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( k1_relset_1(X2,X1,k3_relset_1(X1,X2,X3)) = k2_relset_1(X1,X2,X3)
        & k2_relset_1(X2,X1,k3_relset_1(X1,X2,X3)) = k1_relset_1(X1,X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT011+2.ax',t24_relset_1)).

fof(d4_tops_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( ( k2_relset_1(X1,X2,X3) = X2
          & v2_funct_1(X3) )
       => k2_tops_2(X1,X2,X3) = k2_funct_1(X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).

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
    file('/export/starexec/sandbox/benchmark/Axioms/MPT014+2.ax',d1_funct_2)).

fof(c_0_29,negated_conjecture,(
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

fof(c_0_30,plain,(
    ! [X5917] :
      ( ~ l1_pre_topc(X5917)
      | l1_struct_0(X5917) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

fof(c_0_31,negated_conjecture,
    ( l1_pre_topc(esk755_0)
    & ~ v2_struct_0(esk756_0)
    & l1_pre_topc(esk756_0)
    & v1_funct_1(esk757_0)
    & v1_funct_2(esk757_0,u1_struct_0(esk755_0),u1_struct_0(esk756_0))
    & m1_subset_1(esk757_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk755_0),u1_struct_0(esk756_0))))
    & v3_tops_2(esk757_0,esk755_0,esk756_0)
    & ~ v3_tops_2(k2_tops_2(u1_struct_0(esk755_0),u1_struct_0(esk756_0),esk757_0),esk756_0,esk755_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_29])])])])).

fof(c_0_32,plain,(
    ! [X2097,X2098] :
      ( ~ v1_relat_1(X2097)
      | ~ m1_subset_1(X2098,k1_zfmisc_1(X2097))
      | v1_relat_1(X2098) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_33,plain,(
    ! [X2277,X2278] : v1_relat_1(k2_zfmisc_1(X2277,X2278)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

fof(c_0_34,plain,(
    ! [X3685,X3686,X3687] :
      ( ~ m1_subset_1(X3687,k1_zfmisc_1(k2_zfmisc_1(X3685,X3686)))
      | k3_relset_1(X3685,X3686,X3687) = k4_relat_1(X3687) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k3_relset_1])])).

fof(c_0_35,plain,(
    ! [X5932] :
      ( v2_struct_0(X5932)
      | ~ l1_struct_0(X5932)
      | ~ v1_xboole_0(u1_struct_0(X5932)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_36,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_37,negated_conjecture,
    ( l1_pre_topc(esk756_0) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_38,plain,(
    ! [X2784] :
      ( ~ v1_relat_1(X2784)
      | ~ v1_funct_1(X2784)
      | ~ v2_funct_1(X2784)
      | k2_funct_1(X2784) = k4_relat_1(X2784) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_funct_1])])).

cnf(c_0_39,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_40,negated_conjecture,
    ( m1_subset_1(esk757_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk755_0),u1_struct_0(esk756_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_41,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

fof(c_0_42,plain,(
    ! [X7104,X7105,X7106] :
      ( ( k1_relset_1(u1_struct_0(X7104),u1_struct_0(X7105),X7106) = k2_struct_0(X7104)
        | ~ v3_tops_2(X7106,X7104,X7105)
        | ~ v1_funct_1(X7106)
        | ~ v1_funct_2(X7106,u1_struct_0(X7104),u1_struct_0(X7105))
        | ~ m1_subset_1(X7106,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7104),u1_struct_0(X7105))))
        | ~ l1_pre_topc(X7105)
        | ~ l1_pre_topc(X7104) )
      & ( k2_relset_1(u1_struct_0(X7104),u1_struct_0(X7105),X7106) = k2_struct_0(X7105)
        | ~ v3_tops_2(X7106,X7104,X7105)
        | ~ v1_funct_1(X7106)
        | ~ v1_funct_2(X7106,u1_struct_0(X7104),u1_struct_0(X7105))
        | ~ m1_subset_1(X7106,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7104),u1_struct_0(X7105))))
        | ~ l1_pre_topc(X7105)
        | ~ l1_pre_topc(X7104) )
      & ( v2_funct_1(X7106)
        | ~ v3_tops_2(X7106,X7104,X7105)
        | ~ v1_funct_1(X7106)
        | ~ v1_funct_2(X7106,u1_struct_0(X7104),u1_struct_0(X7105))
        | ~ m1_subset_1(X7106,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7104),u1_struct_0(X7105))))
        | ~ l1_pre_topc(X7105)
        | ~ l1_pre_topc(X7104) )
      & ( v5_pre_topc(X7106,X7104,X7105)
        | ~ v3_tops_2(X7106,X7104,X7105)
        | ~ v1_funct_1(X7106)
        | ~ v1_funct_2(X7106,u1_struct_0(X7104),u1_struct_0(X7105))
        | ~ m1_subset_1(X7106,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7104),u1_struct_0(X7105))))
        | ~ l1_pre_topc(X7105)
        | ~ l1_pre_topc(X7104) )
      & ( v5_pre_topc(k2_tops_2(u1_struct_0(X7104),u1_struct_0(X7105),X7106),X7105,X7104)
        | ~ v3_tops_2(X7106,X7104,X7105)
        | ~ v1_funct_1(X7106)
        | ~ v1_funct_2(X7106,u1_struct_0(X7104),u1_struct_0(X7105))
        | ~ m1_subset_1(X7106,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7104),u1_struct_0(X7105))))
        | ~ l1_pre_topc(X7105)
        | ~ l1_pre_topc(X7104) )
      & ( k1_relset_1(u1_struct_0(X7104),u1_struct_0(X7105),X7106) != k2_struct_0(X7104)
        | k2_relset_1(u1_struct_0(X7104),u1_struct_0(X7105),X7106) != k2_struct_0(X7105)
        | ~ v2_funct_1(X7106)
        | ~ v5_pre_topc(X7106,X7104,X7105)
        | ~ v5_pre_topc(k2_tops_2(u1_struct_0(X7104),u1_struct_0(X7105),X7106),X7105,X7104)
        | v3_tops_2(X7106,X7104,X7105)
        | ~ v1_funct_1(X7106)
        | ~ v1_funct_2(X7106,u1_struct_0(X7104),u1_struct_0(X7105))
        | ~ m1_subset_1(X7106,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7104),u1_struct_0(X7105))))
        | ~ l1_pre_topc(X7105)
        | ~ l1_pre_topc(X7104) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_tops_2])])])])).

fof(c_0_43,plain,(
    ! [X3090] :
      ( ( k2_relat_1(X3090) = k1_relat_1(k2_funct_1(X3090))
        | ~ v2_funct_1(X3090)
        | ~ v1_relat_1(X3090)
        | ~ v1_funct_1(X3090) )
      & ( k1_relat_1(X3090) = k2_relat_1(k2_funct_1(X3090))
        | ~ v2_funct_1(X3090)
        | ~ v1_relat_1(X3090)
        | ~ v1_funct_1(X3090) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).

fof(c_0_44,plain,(
    ! [X3682,X3683,X3684] :
      ( ~ m1_subset_1(X3684,k1_zfmisc_1(k2_zfmisc_1(X3682,X3683)))
      | k2_relset_1(X3682,X3683,X3684) = k2_relat_1(X3684) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

fof(c_0_45,plain,(
    ! [X5896] :
      ( ~ l1_struct_0(X5896)
      | k2_struct_0(X5896) = u1_struct_0(X5896) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

fof(c_0_46,plain,(
    ! [X3641,X3642,X3643] :
      ( ~ m1_subset_1(X3643,k1_zfmisc_1(k2_zfmisc_1(X3641,X3642)))
      | m1_subset_1(k3_relset_1(X3641,X3642,X3643),k1_zfmisc_1(k2_zfmisc_1(X3642,X3641))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_relset_1])])).

cnf(c_0_47,plain,
    ( k3_relset_1(X2,X3,X1) = k4_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

fof(c_0_48,plain,(
    ! [X4814,X4815,X4816] :
      ( ( v1_funct_1(X4816)
        | ~ v1_funct_1(X4816)
        | ~ v1_funct_2(X4816,X4814,X4815)
        | ~ m1_subset_1(X4816,k1_zfmisc_1(k2_zfmisc_1(X4814,X4815)))
        | v1_xboole_0(X4815) )
      & ( v1_partfun1(X4816,X4814)
        | ~ v1_funct_1(X4816)
        | ~ v1_funct_2(X4816,X4814,X4815)
        | ~ m1_subset_1(X4816,k1_zfmisc_1(k2_zfmisc_1(X4814,X4815)))
        | v1_xboole_0(X4815) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc5_funct_2])])])])])).

cnf(c_0_49,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_50,negated_conjecture,
    ( l1_struct_0(esk756_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_51,negated_conjecture,
    ( ~ v2_struct_0(esk756_0) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_52,plain,(
    ! [X3618,X3619,X3620] :
      ( ( v4_relat_1(X3620,X3618)
        | ~ m1_subset_1(X3620,k1_zfmisc_1(k2_zfmisc_1(X3618,X3619))) )
      & ( v5_relat_1(X3620,X3619)
        | ~ m1_subset_1(X3620,k1_zfmisc_1(k2_zfmisc_1(X3618,X3619))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_53,plain,(
    ! [X5963] :
      ( ( m1_subset_1(esk614_1(X5963),k1_zfmisc_1(u1_struct_0(X5963)))
        | v2_struct_0(X5963)
        | ~ l1_struct_0(X5963) )
      & ( ~ v1_xboole_0(esk614_1(X5963))
        | v2_struct_0(X5963)
        | ~ l1_struct_0(X5963) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[rc4_struct_0])])])])])).

cnf(c_0_54,plain,
    ( k2_funct_1(X1) = k4_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_55,negated_conjecture,
    ( v1_funct_1(esk757_0) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_56,negated_conjecture,
    ( v1_relat_1(esk757_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_41])])).

cnf(c_0_57,plain,
    ( v2_funct_1(X1)
    | ~ v3_tops_2(X1,X2,X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_58,negated_conjecture,
    ( v1_funct_2(esk757_0,u1_struct_0(esk755_0),u1_struct_0(esk756_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_59,negated_conjecture,
    ( v3_tops_2(esk757_0,esk755_0,esk756_0) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_60,negated_conjecture,
    ( l1_pre_topc(esk755_0) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_61,plain,
    ( k2_relat_1(X1) = k1_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_62,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_63,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_64,plain,
    ( m1_subset_1(k3_relset_1(X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_65,negated_conjecture,
    ( k3_relset_1(u1_struct_0(esk755_0),u1_struct_0(esk756_0),esk757_0) = k4_relat_1(esk757_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_40])).

fof(c_0_66,plain,(
    ! [X2459] :
      ( ~ v1_relat_1(X2459)
      | k10_relat_1(X2459,k2_relat_1(X2459)) = k1_relat_1(X2459) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t169_relat_1])])).

fof(c_0_67,plain,(
    ! [X4881,X4882] :
      ( ( ~ v1_partfun1(X4882,X4881)
        | k1_relat_1(X4882) = X4881
        | ~ v1_relat_1(X4882)
        | ~ v4_relat_1(X4882,X4881) )
      & ( k1_relat_1(X4882) != X4881
        | v1_partfun1(X4882,X4881)
        | ~ v1_relat_1(X4882)
        | ~ v4_relat_1(X4882,X4881) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_partfun1])])])).

cnf(c_0_68,plain,
    ( v1_partfun1(X1,X2)
    | v1_xboole_0(X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_69,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk756_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_51])).

cnf(c_0_70,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

fof(c_0_71,plain,(
    ! [X2019,X2020] :
      ( ( ~ m1_subset_1(X2019,k1_zfmisc_1(X2020))
        | r1_tarski(X2019,X2020) )
      & ( ~ r1_tarski(X2019,X2020)
        | m1_subset_1(X2019,k1_zfmisc_1(X2020)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_72,plain,
    ( m1_subset_1(esk614_1(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

fof(c_0_73,plain,(
    ! [X2285] :
      ( ~ v1_relat_1(X2285)
      | k4_relat_1(k4_relat_1(X2285)) = X2285 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k4_relat_1])])).

cnf(c_0_74,negated_conjecture,
    ( k4_relat_1(esk757_0) = k2_funct_1(esk757_0)
    | ~ v2_funct_1(esk757_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_56])])).

cnf(c_0_75,negated_conjecture,
    ( v2_funct_1(esk757_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_59]),c_0_37]),c_0_60]),c_0_55]),c_0_40])])).

fof(c_0_76,plain,(
    ! [X2785] :
      ( ( v1_relat_1(k2_funct_1(X2785))
        | ~ v1_relat_1(X2785)
        | ~ v1_funct_1(X2785) )
      & ( v1_funct_1(k2_funct_1(X2785))
        | ~ v1_relat_1(X2785)
        | ~ v1_funct_1(X2785) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).

cnf(c_0_77,negated_conjecture,
    ( k1_relat_1(k2_funct_1(esk757_0)) = k2_relat_1(esk757_0)
    | ~ v2_funct_1(esk757_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_55]),c_0_56])])).

cnf(c_0_78,plain,
    ( k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) = k2_struct_0(X2)
    | ~ v3_tops_2(X3,X1,X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_79,negated_conjecture,
    ( k2_relset_1(u1_struct_0(esk755_0),u1_struct_0(esk756_0),esk757_0) = k2_relat_1(esk757_0) ),
    inference(spm,[status(thm)],[c_0_62,c_0_40])).

cnf(c_0_80,negated_conjecture,
    ( k2_struct_0(esk756_0) = u1_struct_0(esk756_0) ),
    inference(spm,[status(thm)],[c_0_63,c_0_50])).

cnf(c_0_81,negated_conjecture,
    ( m1_subset_1(k4_relat_1(esk757_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk756_0),u1_struct_0(esk755_0)))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_40]),c_0_65])).

cnf(c_0_82,plain,
    ( k10_relat_1(X1,k2_relat_1(X1)) = k1_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_83,plain,
    ( k1_relat_1(X1) = X2
    | ~ v1_partfun1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_84,negated_conjecture,
    ( v1_partfun1(esk757_0,u1_struct_0(esk755_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_58]),c_0_55]),c_0_40])]),c_0_69])).

cnf(c_0_85,negated_conjecture,
    ( v4_relat_1(esk757_0,u1_struct_0(esk755_0)) ),
    inference(spm,[status(thm)],[c_0_70,c_0_40])).

fof(c_0_86,plain,(
    ! [X352,X353,X354] :
      ( v1_xboole_0(X354)
      | ~ r1_tarski(X354,X352)
      | ~ r1_tarski(X354,X353)
      | ~ r1_xboole_0(X352,X353) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t68_xboole_1])])])).

cnf(c_0_87,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_88,negated_conjecture,
    ( m1_subset_1(esk614_1(esk756_0),k1_zfmisc_1(u1_struct_0(esk756_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_50]),c_0_51])).

cnf(c_0_89,plain,
    ( v2_struct_0(X1)
    | ~ v1_xboole_0(esk614_1(X1))
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_90,plain,
    ( k4_relat_1(k4_relat_1(X1)) = X1
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

fof(c_0_91,plain,(
    ! [X4796,X4797,X4798] :
      ( ( v1_funct_1(X4798)
        | ~ v1_funct_1(X4798)
        | ~ v1_partfun1(X4798,X4796)
        | ~ m1_subset_1(X4798,k1_zfmisc_1(k2_zfmisc_1(X4796,X4797))) )
      & ( v1_funct_2(X4798,X4796,X4797)
        | ~ v1_funct_1(X4798)
        | ~ v1_partfun1(X4798,X4796)
        | ~ m1_subset_1(X4798,k1_zfmisc_1(k2_zfmisc_1(X4796,X4797))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_funct_2])])])).

cnf(c_0_92,negated_conjecture,
    ( k4_relat_1(esk757_0) = k2_funct_1(esk757_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_74,c_0_75])])).

cnf(c_0_93,plain,
    ( v1_funct_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_76])).

cnf(c_0_94,plain,
    ( v1_partfun1(X1,X2)
    | k1_relat_1(X1) != X2
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_95,negated_conjecture,
    ( k1_relat_1(k2_funct_1(esk757_0)) = k2_relat_1(esk757_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_77,c_0_75])])).

cnf(c_0_96,negated_conjecture,
    ( k2_relat_1(esk757_0) = u1_struct_0(esk756_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_58]),c_0_79]),c_0_80]),c_0_59]),c_0_37]),c_0_60]),c_0_55]),c_0_40])])).

cnf(c_0_97,negated_conjecture,
    ( v4_relat_1(k4_relat_1(esk757_0),u1_struct_0(esk756_0)) ),
    inference(spm,[status(thm)],[c_0_70,c_0_81])).

cnf(c_0_98,plain,
    ( v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_76])).

fof(c_0_99,plain,(
    ! [X2464,X2465] :
      ( ( k10_relat_1(X2465,X2464) != k1_xboole_0
        | r1_xboole_0(k2_relat_1(X2465),X2464)
        | ~ v1_relat_1(X2465) )
      & ( ~ r1_xboole_0(k2_relat_1(X2465),X2464)
        | k10_relat_1(X2465,X2464) = k1_xboole_0
        | ~ v1_relat_1(X2465) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t173_relat_1])])])).

cnf(c_0_100,negated_conjecture,
    ( k10_relat_1(esk757_0,k2_relat_1(esk757_0)) = k1_relat_1(esk757_0) ),
    inference(spm,[status(thm)],[c_0_82,c_0_56])).

cnf(c_0_101,negated_conjecture,
    ( k1_relat_1(esk757_0) = u1_struct_0(esk755_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_84]),c_0_85]),c_0_56])])).

cnf(c_0_102,plain,
    ( v1_xboole_0(X1)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_86])).

cnf(c_0_103,negated_conjecture,
    ( r1_tarski(esk614_1(esk756_0),u1_struct_0(esk756_0)) ),
    inference(spm,[status(thm)],[c_0_87,c_0_88])).

cnf(c_0_104,negated_conjecture,
    ( ~ v1_xboole_0(esk614_1(esk756_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_50]),c_0_51])).

cnf(c_0_105,negated_conjecture,
    ( k4_relat_1(k4_relat_1(esk757_0)) = esk757_0 ),
    inference(spm,[status(thm)],[c_0_90,c_0_56])).

fof(c_0_106,plain,(
    ! [X3679,X3680,X3681] :
      ( ~ m1_subset_1(X3681,k1_zfmisc_1(k2_zfmisc_1(X3679,X3680)))
      | k1_relset_1(X3679,X3680,X3681) = k1_relat_1(X3681) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_107,plain,(
    ! [X3107] :
      ( ~ v1_relat_1(X3107)
      | ~ v1_funct_1(X3107)
      | ~ v2_funct_1(X3107)
      | k2_funct_1(k2_funct_1(X3107)) = X3107 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_funct_1])])).

fof(c_0_108,plain,(
    ! [X2808] :
      ( ( v1_relat_1(k2_funct_1(X2808))
        | ~ v1_relat_1(X2808)
        | ~ v1_funct_1(X2808)
        | ~ v2_funct_1(X2808) )
      & ( v1_funct_1(k2_funct_1(X2808))
        | ~ v1_relat_1(X2808)
        | ~ v1_funct_1(X2808)
        | ~ v2_funct_1(X2808) )
      & ( v2_funct_1(k2_funct_1(X2808))
        | ~ v1_relat_1(X2808)
        | ~ v1_funct_1(X2808)
        | ~ v2_funct_1(X2808) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc6_funct_1])])])).

cnf(c_0_109,plain,
    ( v1_funct_2(X1,X2,X3)
    | ~ v1_funct_1(X1)
    | ~ v1_partfun1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_91])).

cnf(c_0_110,negated_conjecture,
    ( m1_subset_1(k2_funct_1(esk757_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk756_0),u1_struct_0(esk755_0)))) ),
    inference(rw,[status(thm)],[c_0_81,c_0_92])).

cnf(c_0_111,negated_conjecture,
    ( v1_funct_1(k2_funct_1(esk757_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_55]),c_0_56])])).

cnf(c_0_112,plain,
    ( v1_partfun1(X1,k1_relat_1(X1))
    | ~ v4_relat_1(X1,k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_94])).

cnf(c_0_113,negated_conjecture,
    ( k1_relat_1(k2_funct_1(esk757_0)) = u1_struct_0(esk756_0) ),
    inference(rw,[status(thm)],[c_0_95,c_0_96])).

cnf(c_0_114,negated_conjecture,
    ( v4_relat_1(k2_funct_1(esk757_0),u1_struct_0(esk756_0)) ),
    inference(rw,[status(thm)],[c_0_97,c_0_92])).

cnf(c_0_115,negated_conjecture,
    ( v1_relat_1(k2_funct_1(esk757_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_55]),c_0_56])])).

cnf(c_0_116,plain,
    ( r1_xboole_0(k2_relat_1(X1),X2)
    | k10_relat_1(X1,X2) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_99])).

cnf(c_0_117,negated_conjecture,
    ( k10_relat_1(esk757_0,k2_relat_1(esk757_0)) = u1_struct_0(esk755_0) ),
    inference(rw,[status(thm)],[c_0_100,c_0_101])).

cnf(c_0_118,negated_conjecture,
    ( ~ r1_xboole_0(X1,u1_struct_0(esk756_0))
    | ~ r1_tarski(esk614_1(esk756_0),X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_103]),c_0_104])).

fof(c_0_119,plain,(
    ! [X3762,X3763,X3764] :
      ( ( k1_relset_1(X3763,X3762,k3_relset_1(X3762,X3763,X3764)) = k2_relset_1(X3762,X3763,X3764)
        | ~ m1_subset_1(X3764,k1_zfmisc_1(k2_zfmisc_1(X3762,X3763))) )
      & ( k2_relset_1(X3763,X3762,k3_relset_1(X3762,X3763,X3764)) = k1_relset_1(X3762,X3763,X3764)
        | ~ m1_subset_1(X3764,k1_zfmisc_1(k2_zfmisc_1(X3762,X3763))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t24_relset_1])])])).

cnf(c_0_120,negated_conjecture,
    ( k3_relset_1(u1_struct_0(esk756_0),u1_struct_0(esk755_0),k4_relat_1(esk757_0)) = esk757_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_81]),c_0_105])).

cnf(c_0_121,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_106])).

cnf(c_0_122,plain,
    ( k2_funct_1(k2_funct_1(X1)) = X1
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_107])).

cnf(c_0_123,plain,
    ( v2_funct_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_108])).

fof(c_0_124,plain,(
    ! [X7101,X7102,X7103] :
      ( ~ v1_funct_1(X7103)
      | ~ v1_funct_2(X7103,X7101,X7102)
      | ~ m1_subset_1(X7103,k1_zfmisc_1(k2_zfmisc_1(X7101,X7102)))
      | k2_relset_1(X7101,X7102,X7103) != X7102
      | ~ v2_funct_1(X7103)
      | k2_tops_2(X7101,X7102,X7103) = k2_funct_1(X7103) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tops_2])])).

fof(c_0_125,plain,(
    ! [X4860,X4861,X4862] :
      ( ( ~ v1_funct_2(X4862,X4860,X4861)
        | X4860 = k1_relset_1(X4860,X4861,X4862)
        | X4861 = k1_xboole_0
        | ~ m1_subset_1(X4862,k1_zfmisc_1(k2_zfmisc_1(X4860,X4861))) )
      & ( X4860 != k1_relset_1(X4860,X4861,X4862)
        | v1_funct_2(X4862,X4860,X4861)
        | X4861 = k1_xboole_0
        | ~ m1_subset_1(X4862,k1_zfmisc_1(k2_zfmisc_1(X4860,X4861))) )
      & ( ~ v1_funct_2(X4862,X4860,X4861)
        | X4860 = k1_relset_1(X4860,X4861,X4862)
        | X4860 != k1_xboole_0
        | ~ m1_subset_1(X4862,k1_zfmisc_1(k2_zfmisc_1(X4860,X4861))) )
      & ( X4860 != k1_relset_1(X4860,X4861,X4862)
        | v1_funct_2(X4862,X4860,X4861)
        | X4860 != k1_xboole_0
        | ~ m1_subset_1(X4862,k1_zfmisc_1(k2_zfmisc_1(X4860,X4861))) )
      & ( ~ v1_funct_2(X4862,X4860,X4861)
        | X4862 = k1_xboole_0
        | X4860 = k1_xboole_0
        | X4861 != k1_xboole_0
        | ~ m1_subset_1(X4862,k1_zfmisc_1(k2_zfmisc_1(X4860,X4861))) )
      & ( X4862 != k1_xboole_0
        | v1_funct_2(X4862,X4860,X4861)
        | X4860 = k1_xboole_0
        | X4861 != k1_xboole_0
        | ~ m1_subset_1(X4862,k1_zfmisc_1(k2_zfmisc_1(X4860,X4861))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

cnf(c_0_126,negated_conjecture,
    ( v1_funct_2(k2_funct_1(esk757_0),u1_struct_0(esk756_0),u1_struct_0(esk755_0))
    | ~ v1_partfun1(k2_funct_1(esk757_0),u1_struct_0(esk756_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_110]),c_0_111])])).

cnf(c_0_127,negated_conjecture,
    ( v1_partfun1(k2_funct_1(esk757_0),u1_struct_0(esk756_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112,c_0_113]),c_0_114]),c_0_115])])).

cnf(c_0_128,negated_conjecture,
    ( r1_xboole_0(k2_relat_1(esk757_0),k2_relat_1(esk757_0))
    | u1_struct_0(esk755_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116,c_0_117]),c_0_56])])).

cnf(c_0_129,negated_conjecture,
    ( ~ r1_xboole_0(u1_struct_0(esk756_0),u1_struct_0(esk756_0)) ),
    inference(spm,[status(thm)],[c_0_118,c_0_103])).

cnf(c_0_130,plain,
    ( k1_relset_1(X1,X2,k3_relset_1(X2,X1,X3)) = k2_relset_1(X2,X1,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_119])).

cnf(c_0_131,negated_conjecture,
    ( k3_relset_1(u1_struct_0(esk756_0),u1_struct_0(esk755_0),k2_funct_1(esk757_0)) = esk757_0 ),
    inference(rw,[status(thm)],[c_0_120,c_0_92])).

cnf(c_0_132,negated_conjecture,
    ( k1_relset_1(u1_struct_0(esk755_0),u1_struct_0(esk756_0),esk757_0) = k1_relat_1(esk757_0) ),
    inference(spm,[status(thm)],[c_0_121,c_0_40])).

cnf(c_0_133,negated_conjecture,
    ( k2_funct_1(k2_funct_1(esk757_0)) = esk757_0
    | ~ v2_funct_1(esk757_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_122,c_0_55]),c_0_56])])).

cnf(c_0_134,negated_conjecture,
    ( v2_funct_1(k2_funct_1(esk757_0))
    | ~ v2_funct_1(esk757_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_123,c_0_55]),c_0_56])])).

cnf(c_0_135,plain,
    ( k2_tops_2(X2,X3,X1) = k2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | k2_relset_1(X2,X3,X1) != X3
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_124])).

cnf(c_0_136,negated_conjecture,
    ( k2_relset_1(u1_struct_0(esk755_0),u1_struct_0(esk756_0),esk757_0) = u1_struct_0(esk756_0) ),
    inference(rw,[status(thm)],[c_0_79,c_0_96])).

cnf(c_0_137,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_125])).

cnf(c_0_138,negated_conjecture,
    ( v1_funct_2(k2_funct_1(esk757_0),u1_struct_0(esk756_0),u1_struct_0(esk755_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_126,c_0_127])])).

cnf(c_0_139,negated_conjecture,
    ( u1_struct_0(esk755_0) != k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_128,c_0_96]),c_0_96]),c_0_129])).

cnf(c_0_140,negated_conjecture,
    ( l1_struct_0(esk755_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_60])).

cnf(c_0_141,negated_conjecture,
    ( k2_relset_1(u1_struct_0(esk756_0),u1_struct_0(esk755_0),k2_funct_1(esk757_0)) = u1_struct_0(esk755_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_130,c_0_110]),c_0_131]),c_0_132]),c_0_101])).

cnf(c_0_142,negated_conjecture,
    ( k2_funct_1(k2_funct_1(esk757_0)) = esk757_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_133,c_0_75])])).

cnf(c_0_143,negated_conjecture,
    ( v2_funct_1(k2_funct_1(esk757_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_134,c_0_75])])).

cnf(c_0_144,plain,
    ( v5_pre_topc(X1,X2,X3)
    | ~ v3_tops_2(X1,X2,X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_145,plain,
    ( v5_pre_topc(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3),X2,X1)
    | ~ v3_tops_2(X3,X1,X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_146,negated_conjecture,
    ( k2_tops_2(u1_struct_0(esk755_0),u1_struct_0(esk756_0),esk757_0) = k2_funct_1(esk757_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_135,c_0_136]),c_0_58]),c_0_75]),c_0_55]),c_0_40])])).

cnf(c_0_147,negated_conjecture,
    ( ~ v3_tops_2(k2_tops_2(u1_struct_0(esk755_0),u1_struct_0(esk756_0),esk757_0),esk756_0,esk755_0) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_148,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_149,negated_conjecture,
    ( k1_relset_1(u1_struct_0(esk756_0),u1_struct_0(esk755_0),k2_funct_1(esk757_0)) = u1_struct_0(esk756_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_137,c_0_138]),c_0_110])]),c_0_139])).

cnf(c_0_150,negated_conjecture,
    ( k2_struct_0(esk755_0) = u1_struct_0(esk755_0) ),
    inference(spm,[status(thm)],[c_0_63,c_0_140])).

cnf(c_0_151,negated_conjecture,
    ( k2_tops_2(u1_struct_0(esk756_0),u1_struct_0(esk755_0),k2_funct_1(esk757_0)) = esk757_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_135,c_0_141]),c_0_142]),c_0_138]),c_0_143]),c_0_111]),c_0_110])])).

cnf(c_0_152,negated_conjecture,
    ( v5_pre_topc(esk757_0,esk755_0,esk756_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_144,c_0_58]),c_0_59]),c_0_37]),c_0_60]),c_0_55]),c_0_40])])).

cnf(c_0_153,negated_conjecture,
    ( v5_pre_topc(k2_funct_1(esk757_0),esk756_0,esk755_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_145,c_0_58]),c_0_146]),c_0_59]),c_0_37]),c_0_60]),c_0_55]),c_0_40])])).

cnf(c_0_154,negated_conjecture,
    ( ~ v3_tops_2(k2_funct_1(esk757_0),esk756_0,esk755_0) ),
    inference(rw,[status(thm)],[c_0_147,c_0_146])).

cnf(c_0_155,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_148,c_0_149]),c_0_80]),c_0_141]),c_0_150]),c_0_151]),c_0_152]),c_0_153]),c_0_60]),c_0_37]),c_0_138]),c_0_143]),c_0_111]),c_0_110])]),c_0_154]),
    [proof]).
%------------------------------------------------------------------------------
