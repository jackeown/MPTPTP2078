%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1340+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:05 EST 2020

% Result     : Theorem 8.64s
% Output     : CNFRefutation 8.64s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 482 expanded)
%              Number of clauses        :   59 ( 179 expanded)
%              Number of leaves         :   22 ( 122 expanded)
%              Depth                    :   12
%              Number of atoms          :  317 (2265 expanded)
%              Number of equality atoms :   66 ( 292 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t64_tops_2,conjecture,(
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
               => r2_funct_2(u1_struct_0(X1),u1_struct_0(X2),k2_tops_2(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3)),X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_tops_2)).

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

fof(d9_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => k2_funct_1(X1) = k4_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT008+2.ax',d9_funct_1)).

fof(dt_k4_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k4_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT007+2.ax',dt_k4_relat_1)).

fof(involutiveness_k4_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k4_relat_1(k4_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT007+2.ax',involutiveness_k4_relat_1)).

fof(d3_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => k2_struct_0(X1) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT016+2.ax',d3_struct_0)).

fof(redefinition_k3_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k3_relset_1(X1,X2,X3) = k4_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT011+2.ax',redefinition_k3_relset_1)).

fof(t37_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( k2_relat_1(X1) = k1_relat_1(k4_relat_1(X1))
        & k1_relat_1(X1) = k2_relat_1(k4_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT007+2.ax',t37_relat_1)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT016+2.ax',fc2_struct_0)).

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

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT011+2.ax',redefinition_k2_relset_1)).

fof(d4_partfun1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v4_relat_1(X2,X1) )
     => ( v1_partfun1(X2,X1)
      <=> k1_relat_1(X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT014+2.ax',d4_partfun1)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT011+2.ax',redefinition_k1_relset_1)).

fof(dt_k2_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_relat_1(k2_funct_1(X1))
        & v1_funct_1(k2_funct_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT008+2.ax',dt_k2_funct_1)).

fof(d4_tops_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( ( k2_relset_1(X1,X2,X3) = X2
          & v2_funct_1(X3) )
       => k2_tops_2(X1,X2,X3) = k2_funct_1(X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).

fof(t65_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => k2_funct_1(k2_funct_1(X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT008+2.ax',t65_funct_1)).

fof(t130_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( k1_relset_1(X1,X2,X3) = X1
       => ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT014+2.ax',t130_funct_2)).

fof(fc6_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1)
        & v2_funct_1(X1) )
     => ( v1_relat_1(k2_funct_1(X1))
        & v1_funct_1(k2_funct_1(X1))
        & v2_funct_1(k2_funct_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT008+2.ax',fc6_funct_1)).

fof(redefinition_r2_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r2_funct_2(X1,X2,X3,X4)
      <=> X3 = X4 ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT014+2.ax',redefinition_r2_funct_2)).

fof(c_0_22,negated_conjecture,(
    ~ ! [X1] :
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
                 => r2_funct_2(u1_struct_0(X1),u1_struct_0(X2),k2_tops_2(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3)),X3) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t64_tops_2])).

fof(c_0_23,plain,(
    ! [X2097,X2098] :
      ( ~ v1_relat_1(X2097)
      | ~ m1_subset_1(X2098,k1_zfmisc_1(X2097))
      | v1_relat_1(X2098) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_24,negated_conjecture,
    ( l1_struct_0(esk755_0)
    & ~ v2_struct_0(esk756_0)
    & l1_struct_0(esk756_0)
    & v1_funct_1(esk757_0)
    & v1_funct_2(esk757_0,u1_struct_0(esk755_0),u1_struct_0(esk756_0))
    & m1_subset_1(esk757_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk755_0),u1_struct_0(esk756_0))))
    & k2_relset_1(u1_struct_0(esk755_0),u1_struct_0(esk756_0),esk757_0) = k2_struct_0(esk756_0)
    & v2_funct_1(esk757_0)
    & ~ r2_funct_2(u1_struct_0(esk755_0),u1_struct_0(esk756_0),k2_tops_2(u1_struct_0(esk756_0),u1_struct_0(esk755_0),k2_tops_2(u1_struct_0(esk755_0),u1_struct_0(esk756_0),esk757_0)),esk757_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_22])])])])).

fof(c_0_25,plain,(
    ! [X2277,X2278] : v1_relat_1(k2_zfmisc_1(X2277,X2278)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

fof(c_0_26,plain,(
    ! [X2784] :
      ( ~ v1_relat_1(X2784)
      | ~ v1_funct_1(X2784)
      | ~ v2_funct_1(X2784)
      | k2_funct_1(X2784) = k4_relat_1(X2784) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_funct_1])])).

cnf(c_0_27,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(esk757_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk755_0),u1_struct_0(esk756_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_29,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_30,plain,(
    ! [X2231] :
      ( ~ v1_relat_1(X2231)
      | v1_relat_1(k4_relat_1(X2231)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_relat_1])])).

fof(c_0_31,plain,(
    ! [X2285] :
      ( ~ v1_relat_1(X2285)
      | k4_relat_1(k4_relat_1(X2285)) = X2285 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k4_relat_1])])).

fof(c_0_32,plain,(
    ! [X5896] :
      ( ~ l1_struct_0(X5896)
      | k2_struct_0(X5896) = u1_struct_0(X5896) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

fof(c_0_33,plain,(
    ! [X3685,X3686,X3687] :
      ( ~ m1_subset_1(X3687,k1_zfmisc_1(k2_zfmisc_1(X3685,X3686)))
      | k3_relset_1(X3685,X3686,X3687) = k4_relat_1(X3687) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k3_relset_1])])).

cnf(c_0_34,plain,
    ( k2_funct_1(X1) = k4_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_35,negated_conjecture,
    ( v1_funct_1(esk757_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_36,negated_conjecture,
    ( v2_funct_1(esk757_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_37,negated_conjecture,
    ( v1_relat_1(esk757_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29])])).

fof(c_0_38,plain,(
    ! [X2622] :
      ( ( k2_relat_1(X2622) = k1_relat_1(k4_relat_1(X2622))
        | ~ v1_relat_1(X2622) )
      & ( k1_relat_1(X2622) = k2_relat_1(k4_relat_1(X2622))
        | ~ v1_relat_1(X2622) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_relat_1])])])).

cnf(c_0_39,plain,
    ( v1_relat_1(k4_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_40,plain,
    ( k4_relat_1(k4_relat_1(X1)) = X1
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_41,plain,(
    ! [X5932] :
      ( v2_struct_0(X5932)
      | ~ l1_struct_0(X5932)
      | ~ v1_xboole_0(u1_struct_0(X5932)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_42,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_43,negated_conjecture,
    ( l1_struct_0(esk756_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_44,plain,(
    ! [X3641,X3642,X3643] :
      ( ~ m1_subset_1(X3643,k1_zfmisc_1(k2_zfmisc_1(X3641,X3642)))
      | m1_subset_1(k3_relset_1(X3641,X3642,X3643),k1_zfmisc_1(k2_zfmisc_1(X3642,X3641))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_relset_1])])).

cnf(c_0_45,plain,
    ( k3_relset_1(X2,X3,X1) = k4_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_46,negated_conjecture,
    ( k4_relat_1(esk757_0) = k2_funct_1(esk757_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36]),c_0_37])])).

cnf(c_0_47,plain,
    ( k2_relat_1(X1) = k1_relat_1(k4_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_48,negated_conjecture,
    ( v1_relat_1(k4_relat_1(esk757_0)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_37])).

cnf(c_0_49,negated_conjecture,
    ( k4_relat_1(k4_relat_1(esk757_0)) = esk757_0 ),
    inference(spm,[status(thm)],[c_0_40,c_0_37])).

fof(c_0_50,plain,(
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

cnf(c_0_51,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_52,negated_conjecture,
    ( ~ v2_struct_0(esk756_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_53,plain,(
    ! [X3618,X3619,X3620] :
      ( ( v4_relat_1(X3620,X3618)
        | ~ m1_subset_1(X3620,k1_zfmisc_1(k2_zfmisc_1(X3618,X3619))) )
      & ( v5_relat_1(X3620,X3619)
        | ~ m1_subset_1(X3620,k1_zfmisc_1(k2_zfmisc_1(X3618,X3619))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_54,plain,(
    ! [X3682,X3683,X3684] :
      ( ~ m1_subset_1(X3684,k1_zfmisc_1(k2_zfmisc_1(X3682,X3683)))
      | k2_relset_1(X3682,X3683,X3684) = k2_relat_1(X3684) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

cnf(c_0_55,negated_conjecture,
    ( k2_relset_1(u1_struct_0(esk755_0),u1_struct_0(esk756_0),esk757_0) = k2_struct_0(esk756_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_56,negated_conjecture,
    ( k2_struct_0(esk756_0) = u1_struct_0(esk756_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_57,plain,
    ( m1_subset_1(k3_relset_1(X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_58,negated_conjecture,
    ( k3_relset_1(u1_struct_0(esk755_0),u1_struct_0(esk756_0),esk757_0) = k2_funct_1(esk757_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_28]),c_0_46])).

cnf(c_0_59,negated_conjecture,
    ( k2_relat_1(k4_relat_1(esk757_0)) = k1_relat_1(esk757_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_49])).

fof(c_0_60,plain,(
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

cnf(c_0_61,plain,
    ( v1_partfun1(X1,X2)
    | v1_xboole_0(X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_62,negated_conjecture,
    ( v1_funct_2(esk757_0,u1_struct_0(esk755_0),u1_struct_0(esk756_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_63,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk756_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_43]),c_0_52])).

cnf(c_0_64,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

fof(c_0_65,plain,(
    ! [X3679,X3680,X3681] :
      ( ~ m1_subset_1(X3681,k1_zfmisc_1(k2_zfmisc_1(X3679,X3680)))
      | k1_relset_1(X3679,X3680,X3681) = k1_relat_1(X3681) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_66,negated_conjecture,
    ( k1_relat_1(k4_relat_1(esk757_0)) = k2_relat_1(esk757_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_37])).

cnf(c_0_67,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_68,negated_conjecture,
    ( k2_relset_1(u1_struct_0(esk755_0),u1_struct_0(esk756_0),esk757_0) = u1_struct_0(esk756_0) ),
    inference(rw,[status(thm)],[c_0_55,c_0_56])).

fof(c_0_69,plain,(
    ! [X2785] :
      ( ( v1_relat_1(k2_funct_1(X2785))
        | ~ v1_relat_1(X2785)
        | ~ v1_funct_1(X2785) )
      & ( v1_funct_1(k2_funct_1(X2785))
        | ~ v1_relat_1(X2785)
        | ~ v1_funct_1(X2785) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).

fof(c_0_70,plain,(
    ! [X7101,X7102,X7103] :
      ( ~ v1_funct_1(X7103)
      | ~ v1_funct_2(X7103,X7101,X7102)
      | ~ m1_subset_1(X7103,k1_zfmisc_1(k2_zfmisc_1(X7101,X7102)))
      | k2_relset_1(X7101,X7102,X7103) != X7102
      | ~ v2_funct_1(X7103)
      | k2_tops_2(X7101,X7102,X7103) = k2_funct_1(X7103) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tops_2])])).

cnf(c_0_71,negated_conjecture,
    ( m1_subset_1(k2_funct_1(esk757_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk756_0),u1_struct_0(esk755_0)))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_28]),c_0_58])).

cnf(c_0_72,negated_conjecture,
    ( k2_relat_1(k2_funct_1(esk757_0)) = k1_relat_1(esk757_0) ),
    inference(rw,[status(thm)],[c_0_59,c_0_46])).

cnf(c_0_73,plain,
    ( k1_relat_1(X1) = X2
    | ~ v1_partfun1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_74,negated_conjecture,
    ( v1_partfun1(esk757_0,u1_struct_0(esk755_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_35]),c_0_28])]),c_0_63])).

cnf(c_0_75,negated_conjecture,
    ( v4_relat_1(esk757_0,u1_struct_0(esk755_0)) ),
    inference(spm,[status(thm)],[c_0_64,c_0_28])).

fof(c_0_76,plain,(
    ! [X3107] :
      ( ~ v1_relat_1(X3107)
      | ~ v1_funct_1(X3107)
      | ~ v2_funct_1(X3107)
      | k2_funct_1(k2_funct_1(X3107)) = X3107 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_funct_1])])).

fof(c_0_77,plain,(
    ! [X5170,X5171,X5172] :
      ( ( v1_funct_1(X5172)
        | k1_relset_1(X5170,X5171,X5172) != X5170
        | ~ v1_funct_1(X5172)
        | ~ m1_subset_1(X5172,k1_zfmisc_1(k2_zfmisc_1(X5170,X5171))) )
      & ( v1_funct_2(X5172,X5170,X5171)
        | k1_relset_1(X5170,X5171,X5172) != X5170
        | ~ v1_funct_1(X5172)
        | ~ m1_subset_1(X5172,k1_zfmisc_1(k2_zfmisc_1(X5170,X5171))) )
      & ( m1_subset_1(X5172,k1_zfmisc_1(k2_zfmisc_1(X5170,X5171)))
        | k1_relset_1(X5170,X5171,X5172) != X5170
        | ~ v1_funct_1(X5172)
        | ~ m1_subset_1(X5172,k1_zfmisc_1(k2_zfmisc_1(X5170,X5171))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t130_funct_2])])])).

cnf(c_0_78,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_79,negated_conjecture,
    ( k1_relat_1(k2_funct_1(esk757_0)) = k2_relat_1(esk757_0) ),
    inference(rw,[status(thm)],[c_0_66,c_0_46])).

cnf(c_0_80,negated_conjecture,
    ( k2_relat_1(esk757_0) = u1_struct_0(esk756_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_28]),c_0_68])).

cnf(c_0_81,plain,
    ( v1_funct_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

fof(c_0_82,plain,(
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

cnf(c_0_83,plain,
    ( k2_tops_2(X2,X3,X1) = k2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | k2_relset_1(X2,X3,X1) != X3
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_84,negated_conjecture,
    ( k2_relset_1(u1_struct_0(esk756_0),u1_struct_0(esk755_0),k2_funct_1(esk757_0)) = k1_relat_1(esk757_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_71]),c_0_72])).

cnf(c_0_85,negated_conjecture,
    ( k1_relat_1(esk757_0) = u1_struct_0(esk755_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_75]),c_0_37])])).

cnf(c_0_86,plain,
    ( k2_funct_1(k2_funct_1(X1)) = X1
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_76])).

cnf(c_0_87,plain,
    ( v1_funct_2(X1,X2,X3)
    | k1_relset_1(X2,X3,X1) != X2
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_77])).

cnf(c_0_88,negated_conjecture,
    ( k1_relset_1(u1_struct_0(esk756_0),u1_struct_0(esk755_0),k2_funct_1(esk757_0)) = u1_struct_0(esk756_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_71]),c_0_79]),c_0_80])).

cnf(c_0_89,negated_conjecture,
    ( v1_funct_1(k2_funct_1(esk757_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_35]),c_0_37])])).

cnf(c_0_90,plain,
    ( v2_funct_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_82])).

fof(c_0_91,plain,(
    ! [X5111,X5112,X5113,X5114] :
      ( ( ~ r2_funct_2(X5111,X5112,X5113,X5114)
        | X5113 = X5114
        | ~ v1_funct_1(X5113)
        | ~ v1_funct_2(X5113,X5111,X5112)
        | ~ m1_subset_1(X5113,k1_zfmisc_1(k2_zfmisc_1(X5111,X5112)))
        | ~ v1_funct_1(X5114)
        | ~ v1_funct_2(X5114,X5111,X5112)
        | ~ m1_subset_1(X5114,k1_zfmisc_1(k2_zfmisc_1(X5111,X5112))) )
      & ( X5113 != X5114
        | r2_funct_2(X5111,X5112,X5113,X5114)
        | ~ v1_funct_1(X5113)
        | ~ v1_funct_2(X5113,X5111,X5112)
        | ~ m1_subset_1(X5113,k1_zfmisc_1(k2_zfmisc_1(X5111,X5112)))
        | ~ v1_funct_1(X5114)
        | ~ v1_funct_2(X5114,X5111,X5112)
        | ~ m1_subset_1(X5114,k1_zfmisc_1(k2_zfmisc_1(X5111,X5112))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_funct_2])])])).

cnf(c_0_92,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(esk755_0),u1_struct_0(esk756_0),k2_tops_2(u1_struct_0(esk756_0),u1_struct_0(esk755_0),k2_tops_2(u1_struct_0(esk755_0),u1_struct_0(esk756_0),esk757_0)),esk757_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_93,negated_conjecture,
    ( k2_tops_2(u1_struct_0(esk755_0),u1_struct_0(esk756_0),esk757_0) = k2_funct_1(esk757_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_68]),c_0_62]),c_0_36]),c_0_35]),c_0_28])])).

cnf(c_0_94,negated_conjecture,
    ( k2_relset_1(u1_struct_0(esk756_0),u1_struct_0(esk755_0),k2_funct_1(esk757_0)) = u1_struct_0(esk755_0) ),
    inference(rw,[status(thm)],[c_0_84,c_0_85])).

cnf(c_0_95,negated_conjecture,
    ( k2_funct_1(k2_funct_1(esk757_0)) = esk757_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_35]),c_0_36]),c_0_37])])).

cnf(c_0_96,negated_conjecture,
    ( v1_funct_2(k2_funct_1(esk757_0),u1_struct_0(esk756_0),u1_struct_0(esk755_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_88]),c_0_89]),c_0_71])])).

cnf(c_0_97,negated_conjecture,
    ( v2_funct_1(k2_funct_1(esk757_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_35]),c_0_36]),c_0_37])])).

cnf(c_0_98,plain,
    ( r2_funct_2(X3,X4,X1,X2)
    | X1 != X2
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X3,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X3,X4)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_91])).

cnf(c_0_99,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(esk755_0),u1_struct_0(esk756_0),k2_tops_2(u1_struct_0(esk756_0),u1_struct_0(esk755_0),k2_funct_1(esk757_0)),esk757_0) ),
    inference(rw,[status(thm)],[c_0_92,c_0_93])).

cnf(c_0_100,negated_conjecture,
    ( k2_tops_2(u1_struct_0(esk756_0),u1_struct_0(esk755_0),k2_funct_1(esk757_0)) = esk757_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_94]),c_0_95]),c_0_96]),c_0_97]),c_0_89]),c_0_71])])).

cnf(c_0_101,plain,
    ( r2_funct_2(X1,X2,X3,X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(er,[status(thm)],[c_0_98])).

cnf(c_0_102,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(esk755_0),u1_struct_0(esk756_0),esk757_0,esk757_0) ),
    inference(rw,[status(thm)],[c_0_99,c_0_100])).

cnf(c_0_103,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_62]),c_0_35]),c_0_28])]),c_0_102]),
    [proof]).
%------------------------------------------------------------------------------
