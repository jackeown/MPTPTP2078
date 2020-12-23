%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1338+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:05 EST 2020

% Result     : Theorem 6.30s
% Output     : CNFRefutation 6.30s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 396 expanded)
%              Number of clauses        :   63 ( 149 expanded)
%              Number of leaves         :   21 (  98 expanded)
%              Depth                    :   14
%              Number of atoms          :  324 (2119 expanded)
%              Number of equality atoms :   88 ( 569 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t62_tops_2,conjecture,(
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

fof(d3_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => k2_struct_0(X1) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT016+2.ax',d3_struct_0)).

fof(rc4_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ? [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
          & ~ v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT016+2.ax',rc4_struct_0)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT006+2.ax',t3_subset)).

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

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT011+2.ax',redefinition_k2_relset_1)).

fof(t68_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ~ v1_xboole_0(X3)
     => ~ ( r1_tarski(X3,X1)
          & r1_tarski(X3,X2)
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT002+2.ax',t68_xboole_1)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT016+2.ax',fc2_struct_0)).

fof(t169_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,k2_relat_1(X1)) = k1_relat_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT007+2.ax',t169_relat_1)).

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

fof(t173_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( k10_relat_1(X2,X1) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT007+2.ax',t173_relat_1)).

fof(d4_partfun1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v4_relat_1(X2,X1) )
     => ( v1_partfun1(X2,X1)
      <=> k1_relat_1(X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT014+2.ax',d4_partfun1)).

fof(dt_k2_tops_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( v1_funct_1(k2_tops_2(X1,X2,X3))
        & v1_funct_2(k2_tops_2(X1,X2,X3),X2,X1)
        & m1_subset_1(k2_tops_2(X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_2)).

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

fof(t37_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( k2_relat_1(X1) = k1_relat_1(k4_relat_1(X1))
        & k1_relat_1(X1) = k2_relat_1(k4_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT007+2.ax',t37_relat_1)).

fof(d9_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => k2_funct_1(X1) = k4_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT008+2.ax',d9_funct_1)).

fof(d4_tops_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( ( k2_relset_1(X1,X2,X3) = X2
          & v2_funct_1(X3) )
       => k2_tops_2(X1,X2,X3) = k2_funct_1(X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).

fof(c_0_21,negated_conjecture,(
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
                 => ( k1_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3)) = k2_struct_0(X2)
                    & k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3)) = k2_struct_0(X1) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t62_tops_2])).

fof(c_0_22,plain,(
    ! [X5896] :
      ( ~ l1_struct_0(X5896)
      | k2_struct_0(X5896) = u1_struct_0(X5896) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

fof(c_0_23,negated_conjecture,
    ( l1_struct_0(esk755_0)
    & ~ v2_struct_0(esk756_0)
    & l1_struct_0(esk756_0)
    & v1_funct_1(esk757_0)
    & v1_funct_2(esk757_0,u1_struct_0(esk755_0),u1_struct_0(esk756_0))
    & m1_subset_1(esk757_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk755_0),u1_struct_0(esk756_0))))
    & k2_relset_1(u1_struct_0(esk755_0),u1_struct_0(esk756_0),esk757_0) = k2_struct_0(esk756_0)
    & v2_funct_1(esk757_0)
    & ( k1_relset_1(u1_struct_0(esk756_0),u1_struct_0(esk755_0),k2_tops_2(u1_struct_0(esk755_0),u1_struct_0(esk756_0),esk757_0)) != k2_struct_0(esk756_0)
      | k2_relset_1(u1_struct_0(esk756_0),u1_struct_0(esk755_0),k2_tops_2(u1_struct_0(esk755_0),u1_struct_0(esk756_0),esk757_0)) != k2_struct_0(esk755_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_21])])])])).

fof(c_0_24,plain,(
    ! [X5963] :
      ( ( m1_subset_1(esk614_1(X5963),k1_zfmisc_1(u1_struct_0(X5963)))
        | v2_struct_0(X5963)
        | ~ l1_struct_0(X5963) )
      & ( ~ v1_xboole_0(esk614_1(X5963))
        | v2_struct_0(X5963)
        | ~ l1_struct_0(X5963) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[rc4_struct_0])])])])])).

cnf(c_0_25,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_26,negated_conjecture,
    ( l1_struct_0(esk756_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_27,plain,(
    ! [X2019,X2020] :
      ( ( ~ m1_subset_1(X2019,k1_zfmisc_1(X2020))
        | r1_tarski(X2019,X2020) )
      & ( ~ r1_tarski(X2019,X2020)
        | m1_subset_1(X2019,k1_zfmisc_1(X2020)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_28,plain,
    ( m1_subset_1(esk614_1(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_29,negated_conjecture,
    ( ~ v2_struct_0(esk756_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_30,plain,(
    ! [X2097,X2098] :
      ( ~ v1_relat_1(X2097)
      | ~ m1_subset_1(X2098,k1_zfmisc_1(X2097))
      | v1_relat_1(X2098) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_31,plain,(
    ! [X2277,X2278] : v1_relat_1(k2_zfmisc_1(X2277,X2278)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

fof(c_0_32,plain,(
    ! [X3682,X3683,X3684] :
      ( ~ m1_subset_1(X3684,k1_zfmisc_1(k2_zfmisc_1(X3682,X3683)))
      | k2_relset_1(X3682,X3683,X3684) = k2_relat_1(X3684) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

cnf(c_0_33,negated_conjecture,
    ( k2_relset_1(u1_struct_0(esk755_0),u1_struct_0(esk756_0),esk757_0) = k2_struct_0(esk756_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_34,negated_conjecture,
    ( k2_struct_0(esk756_0) = u1_struct_0(esk756_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

fof(c_0_35,plain,(
    ! [X352,X353,X354] :
      ( v1_xboole_0(X354)
      | ~ r1_tarski(X354,X352)
      | ~ r1_tarski(X354,X353)
      | ~ r1_xboole_0(X352,X353) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t68_xboole_1])])])).

cnf(c_0_36,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_37,negated_conjecture,
    ( m1_subset_1(esk614_1(esk756_0),k1_zfmisc_1(u1_struct_0(esk756_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_26]),c_0_29])).

cnf(c_0_38,plain,
    ( v2_struct_0(X1)
    | ~ v1_xboole_0(esk614_1(X1))
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_39,plain,(
    ! [X5932] :
      ( v2_struct_0(X5932)
      | ~ l1_struct_0(X5932)
      | ~ v1_xboole_0(u1_struct_0(X5932)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

fof(c_0_40,plain,(
    ! [X2459] :
      ( ~ v1_relat_1(X2459)
      | k10_relat_1(X2459,k2_relat_1(X2459)) = k1_relat_1(X2459) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t169_relat_1])])).

cnf(c_0_41,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_42,negated_conjecture,
    ( m1_subset_1(esk757_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk755_0),u1_struct_0(esk756_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_43,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_44,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_45,negated_conjecture,
    ( k2_relset_1(u1_struct_0(esk755_0),u1_struct_0(esk756_0),esk757_0) = u1_struct_0(esk756_0) ),
    inference(rw,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_46,plain,
    ( v1_xboole_0(X1)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_47,negated_conjecture,
    ( r1_tarski(esk614_1(esk756_0),u1_struct_0(esk756_0)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_48,negated_conjecture,
    ( ~ v1_xboole_0(esk614_1(esk756_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_26]),c_0_29])).

fof(c_0_49,plain,(
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

cnf(c_0_50,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

fof(c_0_51,plain,(
    ! [X3618,X3619,X3620] :
      ( ( v4_relat_1(X3620,X3618)
        | ~ m1_subset_1(X3620,k1_zfmisc_1(k2_zfmisc_1(X3618,X3619))) )
      & ( v5_relat_1(X3620,X3619)
        | ~ m1_subset_1(X3620,k1_zfmisc_1(k2_zfmisc_1(X3618,X3619))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_52,plain,(
    ! [X2464,X2465] :
      ( ( k10_relat_1(X2465,X2464) != k1_xboole_0
        | r1_xboole_0(k2_relat_1(X2465),X2464)
        | ~ v1_relat_1(X2465) )
      & ( ~ r1_xboole_0(k2_relat_1(X2465),X2464)
        | k10_relat_1(X2465,X2464) = k1_xboole_0
        | ~ v1_relat_1(X2465) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t173_relat_1])])])).

cnf(c_0_53,plain,
    ( k10_relat_1(X1,k2_relat_1(X1)) = k1_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_54,negated_conjecture,
    ( v1_relat_1(esk757_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_43])])).

cnf(c_0_55,negated_conjecture,
    ( k2_relat_1(esk757_0) = u1_struct_0(esk756_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_42]),c_0_45])).

cnf(c_0_56,negated_conjecture,
    ( ~ r1_xboole_0(X1,u1_struct_0(esk756_0))
    | ~ r1_tarski(esk614_1(esk756_0),X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_48])).

fof(c_0_57,plain,(
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

cnf(c_0_58,plain,
    ( v1_partfun1(X1,X2)
    | v1_xboole_0(X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_59,negated_conjecture,
    ( v1_funct_2(esk757_0,u1_struct_0(esk755_0),u1_struct_0(esk756_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_60,negated_conjecture,
    ( v1_funct_1(esk757_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_61,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk756_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_26]),c_0_29])).

cnf(c_0_62,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

fof(c_0_63,plain,(
    ! [X7112,X7113,X7114] :
      ( ( v1_funct_1(k2_tops_2(X7112,X7113,X7114))
        | ~ v1_funct_1(X7114)
        | ~ v1_funct_2(X7114,X7112,X7113)
        | ~ m1_subset_1(X7114,k1_zfmisc_1(k2_zfmisc_1(X7112,X7113))) )
      & ( v1_funct_2(k2_tops_2(X7112,X7113,X7114),X7113,X7112)
        | ~ v1_funct_1(X7114)
        | ~ v1_funct_2(X7114,X7112,X7113)
        | ~ m1_subset_1(X7114,k1_zfmisc_1(k2_zfmisc_1(X7112,X7113))) )
      & ( m1_subset_1(k2_tops_2(X7112,X7113,X7114),k1_zfmisc_1(k2_zfmisc_1(X7113,X7112)))
        | ~ v1_funct_1(X7114)
        | ~ v1_funct_2(X7114,X7112,X7113)
        | ~ m1_subset_1(X7114,k1_zfmisc_1(k2_zfmisc_1(X7112,X7113))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_tops_2])])])).

cnf(c_0_64,plain,
    ( r1_xboole_0(k2_relat_1(X1),X2)
    | k10_relat_1(X1,X2) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_65,negated_conjecture,
    ( k10_relat_1(esk757_0,u1_struct_0(esk756_0)) = k1_relat_1(esk757_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_55])).

cnf(c_0_66,negated_conjecture,
    ( ~ r1_xboole_0(u1_struct_0(esk756_0),u1_struct_0(esk756_0)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_47])).

cnf(c_0_67,plain,
    ( k1_relat_1(X1) = X2
    | ~ v1_partfun1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_68,negated_conjecture,
    ( v1_partfun1(esk757_0,u1_struct_0(esk755_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_60]),c_0_42])]),c_0_61])).

cnf(c_0_69,negated_conjecture,
    ( v4_relat_1(esk757_0,u1_struct_0(esk755_0)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_42])).

fof(c_0_70,plain,(
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

cnf(c_0_71,plain,
    ( v1_funct_2(k2_tops_2(X1,X2,X3),X2,X1)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_72,negated_conjecture,
    ( k1_relat_1(esk757_0) != k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_55]),c_0_54])]),c_0_66])).

cnf(c_0_73,negated_conjecture,
    ( k1_relat_1(esk757_0) = u1_struct_0(esk755_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_69]),c_0_54])])).

cnf(c_0_74,negated_conjecture,
    ( l1_struct_0(esk755_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_75,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_76,negated_conjecture,
    ( v1_funct_2(k2_tops_2(u1_struct_0(esk755_0),u1_struct_0(esk756_0),esk757_0),u1_struct_0(esk756_0),u1_struct_0(esk755_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_59]),c_0_60]),c_0_42])])).

cnf(c_0_77,negated_conjecture,
    ( u1_struct_0(esk755_0) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_78,plain,
    ( m1_subset_1(k2_tops_2(X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

fof(c_0_79,plain,(
    ! [X2231] :
      ( ~ v1_relat_1(X2231)
      | v1_relat_1(k4_relat_1(X2231)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_relat_1])])).

fof(c_0_80,plain,(
    ! [X2285] :
      ( ~ v1_relat_1(X2285)
      | k4_relat_1(k4_relat_1(X2285)) = X2285 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k4_relat_1])])).

cnf(c_0_81,negated_conjecture,
    ( k1_relset_1(u1_struct_0(esk756_0),u1_struct_0(esk755_0),k2_tops_2(u1_struct_0(esk755_0),u1_struct_0(esk756_0),esk757_0)) != k2_struct_0(esk756_0)
    | k2_relset_1(u1_struct_0(esk756_0),u1_struct_0(esk755_0),k2_tops_2(u1_struct_0(esk755_0),u1_struct_0(esk756_0),esk757_0)) != k2_struct_0(esk755_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_82,negated_conjecture,
    ( k2_struct_0(esk755_0) = u1_struct_0(esk755_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_74])).

cnf(c_0_83,negated_conjecture,
    ( k1_relset_1(u1_struct_0(esk756_0),u1_struct_0(esk755_0),k2_tops_2(u1_struct_0(esk755_0),u1_struct_0(esk756_0),esk757_0)) = u1_struct_0(esk756_0)
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(esk755_0),u1_struct_0(esk756_0),esk757_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk756_0),u1_struct_0(esk755_0)))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_77])).

cnf(c_0_84,negated_conjecture,
    ( m1_subset_1(k2_tops_2(u1_struct_0(esk755_0),u1_struct_0(esk756_0),esk757_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk756_0),u1_struct_0(esk755_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_59]),c_0_60]),c_0_42])])).

fof(c_0_85,plain,(
    ! [X2622] :
      ( ( k2_relat_1(X2622) = k1_relat_1(k4_relat_1(X2622))
        | ~ v1_relat_1(X2622) )
      & ( k1_relat_1(X2622) = k2_relat_1(k4_relat_1(X2622))
        | ~ v1_relat_1(X2622) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_relat_1])])])).

cnf(c_0_86,plain,
    ( v1_relat_1(k4_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_79])).

cnf(c_0_87,plain,
    ( k4_relat_1(k4_relat_1(X1)) = X1
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_80])).

fof(c_0_88,plain,(
    ! [X2784] :
      ( ~ v1_relat_1(X2784)
      | ~ v1_funct_1(X2784)
      | ~ v2_funct_1(X2784)
      | k2_funct_1(X2784) = k4_relat_1(X2784) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_funct_1])])).

cnf(c_0_89,negated_conjecture,
    ( k1_relset_1(u1_struct_0(esk756_0),u1_struct_0(esk755_0),k2_tops_2(u1_struct_0(esk755_0),u1_struct_0(esk756_0),esk757_0)) != u1_struct_0(esk756_0)
    | k2_relset_1(u1_struct_0(esk756_0),u1_struct_0(esk755_0),k2_tops_2(u1_struct_0(esk755_0),u1_struct_0(esk756_0),esk757_0)) != u1_struct_0(esk755_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_81,c_0_34]),c_0_82])).

cnf(c_0_90,negated_conjecture,
    ( k1_relset_1(u1_struct_0(esk756_0),u1_struct_0(esk755_0),k2_tops_2(u1_struct_0(esk755_0),u1_struct_0(esk756_0),esk757_0)) = u1_struct_0(esk756_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_83,c_0_84])])).

fof(c_0_91,plain,(
    ! [X7101,X7102,X7103] :
      ( ~ v1_funct_1(X7103)
      | ~ v1_funct_2(X7103,X7101,X7102)
      | ~ m1_subset_1(X7103,k1_zfmisc_1(k2_zfmisc_1(X7101,X7102)))
      | k2_relset_1(X7101,X7102,X7103) != X7102
      | ~ v2_funct_1(X7103)
      | k2_tops_2(X7101,X7102,X7103) = k2_funct_1(X7103) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tops_2])])).

cnf(c_0_92,plain,
    ( k2_relat_1(X1) = k1_relat_1(k4_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_85])).

cnf(c_0_93,negated_conjecture,
    ( v1_relat_1(k4_relat_1(esk757_0)) ),
    inference(spm,[status(thm)],[c_0_86,c_0_54])).

cnf(c_0_94,negated_conjecture,
    ( k4_relat_1(k4_relat_1(esk757_0)) = esk757_0 ),
    inference(spm,[status(thm)],[c_0_87,c_0_54])).

cnf(c_0_95,plain,
    ( k2_funct_1(X1) = k4_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_88])).

cnf(c_0_96,negated_conjecture,
    ( v2_funct_1(esk757_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_97,negated_conjecture,
    ( k2_relset_1(u1_struct_0(esk756_0),u1_struct_0(esk755_0),k2_tops_2(u1_struct_0(esk755_0),u1_struct_0(esk756_0),esk757_0)) != u1_struct_0(esk755_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_89,c_0_90])])).

cnf(c_0_98,negated_conjecture,
    ( k2_relset_1(u1_struct_0(esk756_0),u1_struct_0(esk755_0),k2_tops_2(u1_struct_0(esk755_0),u1_struct_0(esk756_0),esk757_0)) = k2_relat_1(k2_tops_2(u1_struct_0(esk755_0),u1_struct_0(esk756_0),esk757_0)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_84])).

cnf(c_0_99,plain,
    ( k2_tops_2(X2,X3,X1) = k2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | k2_relset_1(X2,X3,X1) != X3
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_91])).

cnf(c_0_100,negated_conjecture,
    ( k2_relat_1(k4_relat_1(esk757_0)) = k1_relat_1(esk757_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_93]),c_0_94])).

cnf(c_0_101,negated_conjecture,
    ( k4_relat_1(esk757_0) = k2_funct_1(esk757_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_60]),c_0_96]),c_0_54])])).

cnf(c_0_102,negated_conjecture,
    ( k2_relat_1(k2_tops_2(u1_struct_0(esk755_0),u1_struct_0(esk756_0),esk757_0)) != u1_struct_0(esk755_0) ),
    inference(rw,[status(thm)],[c_0_97,c_0_98])).

cnf(c_0_103,negated_conjecture,
    ( k2_tops_2(u1_struct_0(esk755_0),u1_struct_0(esk756_0),esk757_0) = k2_funct_1(esk757_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_45]),c_0_59]),c_0_96]),c_0_60]),c_0_42])])).

cnf(c_0_104,negated_conjecture,
    ( k2_relat_1(k2_funct_1(esk757_0)) = k1_relat_1(esk757_0) ),
    inference(rw,[status(thm)],[c_0_100,c_0_101])).

cnf(c_0_105,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_102,c_0_103]),c_0_104]),c_0_73])]),
    [proof]).
%------------------------------------------------------------------------------
