%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:18:22 EST 2020

% Result     : Theorem 0.38s
% Output     : CNFRefutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 463 expanded)
%              Number of clauses        :   45 ( 168 expanded)
%              Number of leaves         :   10 ( 117 expanded)
%              Depth                    :   12
%              Number of atoms          :  405 (3194 expanded)
%              Number of equality atoms :   41 ( 467 expanded)
%              Maximal formula depth    :   27 (   6 average)
%              Maximal clause size      :   90 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t114_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => ( u1_struct_0(k8_tmap_1(X1,X2)) = u1_struct_0(X1)
            & ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ( X3 = u1_struct_0(X2)
                 => u1_pre_topc(k8_tmap_1(X1,X2)) = k5_tmap_1(X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t114_tmap_1)).

fof(t1_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

fof(t116_tmap_1,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => ( ( v1_tsep_1(X2,X1)
              & m1_pre_topc(X2,X1) )
          <=> g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k8_tmap_1(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_tmap_1)).

fof(abstractness_v1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ( v1_pre_topc(X1)
       => X1 = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

fof(dt_k8_tmap_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_pre_topc(X2,X1) )
     => ( v1_pre_topc(k8_tmap_1(X1,X2))
        & v2_pre_topc(k8_tmap_1(X1,X2))
        & l1_pre_topc(k8_tmap_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_tmap_1)).

fof(t103_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( r2_hidden(X2,u1_pre_topc(X1))
          <=> u1_pre_topc(X1) = k5_tmap_1(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_tmap_1)).

fof(d5_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_pre_topc(X2,X1)
          <=> r2_hidden(X2,u1_pre_topc(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_pre_topc)).

fof(d1_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ( v1_tsep_1(X2,X1)
          <=> ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ( X3 = u1_struct_0(X2)
                 => v3_pre_topc(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tsep_1)).

fof(d1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ( v2_pre_topc(X1)
      <=> ( r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))
          & ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
             => ( r1_tarski(X2,u1_pre_topc(X1))
               => r2_hidden(k5_setfam_1(u1_struct_0(X1),X2),u1_pre_topc(X1)) ) )
          & ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( r2_hidden(X2,u1_pre_topc(X1))
                      & r2_hidden(X3,u1_pre_topc(X1)) )
                   => r2_hidden(k9_subset_1(u1_struct_0(X1),X2,X3),u1_pre_topc(X1)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_pre_topc)).

fof(t2_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_pre_topc(X1,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

fof(c_0_10,plain,(
    ! [X22,X23,X24] :
      ( ( u1_struct_0(k8_tmap_1(X22,X23)) = u1_struct_0(X22)
        | v2_struct_0(X23)
        | ~ m1_pre_topc(X23,X22)
        | v2_struct_0(X22)
        | ~ v2_pre_topc(X22)
        | ~ l1_pre_topc(X22) )
      & ( ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X22)))
        | X24 != u1_struct_0(X23)
        | u1_pre_topc(k8_tmap_1(X22,X23)) = k5_tmap_1(X22,X24)
        | v2_struct_0(X23)
        | ~ m1_pre_topc(X23,X22)
        | v2_struct_0(X22)
        | ~ v2_pre_topc(X22)
        | ~ l1_pre_topc(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t114_tmap_1])])])])])).

fof(c_0_11,plain,(
    ! [X25,X26] :
      ( ~ l1_pre_topc(X25)
      | ~ m1_pre_topc(X26,X25)
      | m1_subset_1(u1_struct_0(X26),k1_zfmisc_1(u1_struct_0(X25))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & m1_pre_topc(X2,X1) )
           => ( ( v1_tsep_1(X2,X1)
                & m1_pre_topc(X2,X1) )
            <=> g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k8_tmap_1(X1,X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t116_tmap_1])).

fof(c_0_13,plain,(
    ! [X4] :
      ( ~ l1_pre_topc(X4)
      | ~ v1_pre_topc(X4)
      | X4 = g1_pre_topc(u1_struct_0(X4),u1_pre_topc(X4)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[abstractness_v1_pre_topc])])).

fof(c_0_14,plain,(
    ! [X18,X19] :
      ( ( v1_pre_topc(k8_tmap_1(X18,X19))
        | v2_struct_0(X18)
        | ~ v2_pre_topc(X18)
        | ~ l1_pre_topc(X18)
        | ~ m1_pre_topc(X19,X18) )
      & ( v2_pre_topc(k8_tmap_1(X18,X19))
        | v2_struct_0(X18)
        | ~ v2_pre_topc(X18)
        | ~ l1_pre_topc(X18)
        | ~ m1_pre_topc(X19,X18) )
      & ( l1_pre_topc(k8_tmap_1(X18,X19))
        | v2_struct_0(X18)
        | ~ v2_pre_topc(X18)
        | ~ l1_pre_topc(X18)
        | ~ m1_pre_topc(X19,X18) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k8_tmap_1])])])])).

fof(c_0_15,plain,(
    ! [X20,X21] :
      ( ( ~ r2_hidden(X21,u1_pre_topc(X20))
        | u1_pre_topc(X20) = k5_tmap_1(X20,X21)
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))
        | v2_struct_0(X20)
        | ~ v2_pre_topc(X20)
        | ~ l1_pre_topc(X20) )
      & ( u1_pre_topc(X20) != k5_tmap_1(X20,X21)
        | r2_hidden(X21,u1_pre_topc(X20))
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))
        | v2_struct_0(X20)
        | ~ v2_pre_topc(X20)
        | ~ l1_pre_topc(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t103_tmap_1])])])])])).

cnf(c_0_16,plain,
    ( u1_pre_topc(k8_tmap_1(X2,X3)) = k5_tmap_1(X2,X1)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | X1 != u1_struct_0(X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,plain,
    ( m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_18,negated_conjecture,
    ( ~ v2_struct_0(esk5_0)
    & v2_pre_topc(esk5_0)
    & l1_pre_topc(esk5_0)
    & ~ v2_struct_0(esk6_0)
    & m1_pre_topc(esk6_0,esk5_0)
    & ( ~ v1_tsep_1(esk6_0,esk5_0)
      | ~ m1_pre_topc(esk6_0,esk5_0)
      | g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)) != k8_tmap_1(esk5_0,esk6_0) )
    & ( v1_tsep_1(esk6_0,esk5_0)
      | g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)) = k8_tmap_1(esk5_0,esk6_0) )
    & ( m1_pre_topc(esk6_0,esk5_0)
      | g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)) = k8_tmap_1(esk5_0,esk6_0) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_12])])])])])).

cnf(c_0_19,plain,
    ( X1 = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ l1_pre_topc(X1)
    | ~ v1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( u1_struct_0(k8_tmap_1(X1,X2)) = u1_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_21,plain,
    ( l1_pre_topc(k8_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,plain,
    ( v1_pre_topc(k8_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,plain,
    ( u1_pre_topc(X2) = k5_tmap_1(X2,X1)
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,u1_pre_topc(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,plain,
    ( k5_tmap_1(X1,u1_struct_0(X2)) = u1_pre_topc(k8_tmap_1(X1,X2))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_16]),c_0_17])).

cnf(c_0_25,negated_conjecture,
    ( m1_pre_topc(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,negated_conjecture,
    ( l1_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,plain,
    ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(k8_tmap_1(X1,X2))) = k8_tmap_1(X1,X2)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21]),c_0_22])).

cnf(c_0_28,plain,
    ( u1_pre_topc(k8_tmap_1(X1,X2)) = u1_pre_topc(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ r2_hidden(u1_struct_0(X2),u1_pre_topc(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_17])).

fof(c_0_29,plain,(
    ! [X12,X13] :
      ( ( ~ v3_pre_topc(X13,X12)
        | r2_hidden(X13,u1_pre_topc(X12))
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))
        | ~ l1_pre_topc(X12) )
      & ( ~ r2_hidden(X13,u1_pre_topc(X12))
        | v3_pre_topc(X13,X12)
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))
        | ~ l1_pre_topc(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_pre_topc])])])])).

fof(c_0_30,plain,(
    ! [X14,X15,X16] :
      ( ( ~ v1_tsep_1(X15,X14)
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X14)))
        | X16 != u1_struct_0(X15)
        | v3_pre_topc(X16,X14)
        | ~ m1_pre_topc(X15,X14)
        | ~ l1_pre_topc(X14) )
      & ( m1_subset_1(esk4_2(X14,X15),k1_zfmisc_1(u1_struct_0(X14)))
        | v1_tsep_1(X15,X14)
        | ~ m1_pre_topc(X15,X14)
        | ~ l1_pre_topc(X14) )
      & ( esk4_2(X14,X15) = u1_struct_0(X15)
        | v1_tsep_1(X15,X14)
        | ~ m1_pre_topc(X15,X14)
        | ~ l1_pre_topc(X14) )
      & ( ~ v3_pre_topc(esk4_2(X14,X15),X14)
        | v1_tsep_1(X15,X14)
        | ~ m1_pre_topc(X15,X14)
        | ~ l1_pre_topc(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tsep_1])])])])])).

cnf(c_0_31,plain,
    ( r2_hidden(X2,u1_pre_topc(X1))
    | v2_struct_0(X1)
    | u1_pre_topc(X1) != k5_tmap_1(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_32,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk6_0),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_25]),c_0_26])])).

cnf(c_0_33,negated_conjecture,
    ( v2_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_34,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_35,negated_conjecture,
    ( v1_tsep_1(esk6_0,esk5_0)
    | g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)) = k8_tmap_1(esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_36,plain,
    ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k8_tmap_1(X1,X2)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ r2_hidden(u1_struct_0(X2),u1_pre_topc(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_37,plain,
    ( r2_hidden(X1,u1_pre_topc(X2))
    | ~ v3_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_38,plain,
    ( v3_pre_topc(X3,X2)
    | ~ v1_tsep_1(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | X3 != u1_struct_0(X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(u1_struct_0(esk6_0),u1_pre_topc(esk5_0))
    | k5_tmap_1(esk5_0,u1_struct_0(esk6_0)) != u1_pre_topc(esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33]),c_0_26])]),c_0_34])).

cnf(c_0_40,negated_conjecture,
    ( ~ v2_struct_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_41,negated_conjecture,
    ( k8_tmap_1(esk5_0,X1) = k8_tmap_1(esk5_0,esk6_0)
    | v2_struct_0(X1)
    | v1_tsep_1(esk6_0,esk5_0)
    | ~ m1_pre_topc(X1,esk5_0)
    | ~ r2_hidden(u1_struct_0(X1),u1_pre_topc(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_33]),c_0_26])]),c_0_34])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(u1_struct_0(esk6_0),u1_pre_topc(esk5_0))
    | ~ v3_pre_topc(u1_struct_0(esk6_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_32]),c_0_26])])).

cnf(c_0_43,plain,
    ( v3_pre_topc(u1_struct_0(X1),X2)
    | ~ v1_tsep_1(X1,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_38]),c_0_17])).

fof(c_0_44,plain,(
    ! [X5,X6,X7,X8] :
      ( ( r2_hidden(u1_struct_0(X5),u1_pre_topc(X5))
        | ~ v2_pre_topc(X5)
        | ~ l1_pre_topc(X5) )
      & ( ~ m1_subset_1(X6,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X5))))
        | ~ r1_tarski(X6,u1_pre_topc(X5))
        | r2_hidden(k5_setfam_1(u1_struct_0(X5),X6),u1_pre_topc(X5))
        | ~ v2_pre_topc(X5)
        | ~ l1_pre_topc(X5) )
      & ( ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X5)))
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X5)))
        | ~ r2_hidden(X7,u1_pre_topc(X5))
        | ~ r2_hidden(X8,u1_pre_topc(X5))
        | r2_hidden(k9_subset_1(u1_struct_0(X5),X7,X8),u1_pre_topc(X5))
        | ~ v2_pre_topc(X5)
        | ~ l1_pre_topc(X5) )
      & ( m1_subset_1(esk2_1(X5),k1_zfmisc_1(u1_struct_0(X5)))
        | m1_subset_1(esk1_1(X5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X5))))
        | ~ r2_hidden(u1_struct_0(X5),u1_pre_topc(X5))
        | v2_pre_topc(X5)
        | ~ l1_pre_topc(X5) )
      & ( m1_subset_1(esk3_1(X5),k1_zfmisc_1(u1_struct_0(X5)))
        | m1_subset_1(esk1_1(X5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X5))))
        | ~ r2_hidden(u1_struct_0(X5),u1_pre_topc(X5))
        | v2_pre_topc(X5)
        | ~ l1_pre_topc(X5) )
      & ( r2_hidden(esk2_1(X5),u1_pre_topc(X5))
        | m1_subset_1(esk1_1(X5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X5))))
        | ~ r2_hidden(u1_struct_0(X5),u1_pre_topc(X5))
        | v2_pre_topc(X5)
        | ~ l1_pre_topc(X5) )
      & ( r2_hidden(esk3_1(X5),u1_pre_topc(X5))
        | m1_subset_1(esk1_1(X5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X5))))
        | ~ r2_hidden(u1_struct_0(X5),u1_pre_topc(X5))
        | v2_pre_topc(X5)
        | ~ l1_pre_topc(X5) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X5),esk2_1(X5),esk3_1(X5)),u1_pre_topc(X5))
        | m1_subset_1(esk1_1(X5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X5))))
        | ~ r2_hidden(u1_struct_0(X5),u1_pre_topc(X5))
        | v2_pre_topc(X5)
        | ~ l1_pre_topc(X5) )
      & ( m1_subset_1(esk2_1(X5),k1_zfmisc_1(u1_struct_0(X5)))
        | r1_tarski(esk1_1(X5),u1_pre_topc(X5))
        | ~ r2_hidden(u1_struct_0(X5),u1_pre_topc(X5))
        | v2_pre_topc(X5)
        | ~ l1_pre_topc(X5) )
      & ( m1_subset_1(esk3_1(X5),k1_zfmisc_1(u1_struct_0(X5)))
        | r1_tarski(esk1_1(X5),u1_pre_topc(X5))
        | ~ r2_hidden(u1_struct_0(X5),u1_pre_topc(X5))
        | v2_pre_topc(X5)
        | ~ l1_pre_topc(X5) )
      & ( r2_hidden(esk2_1(X5),u1_pre_topc(X5))
        | r1_tarski(esk1_1(X5),u1_pre_topc(X5))
        | ~ r2_hidden(u1_struct_0(X5),u1_pre_topc(X5))
        | v2_pre_topc(X5)
        | ~ l1_pre_topc(X5) )
      & ( r2_hidden(esk3_1(X5),u1_pre_topc(X5))
        | r1_tarski(esk1_1(X5),u1_pre_topc(X5))
        | ~ r2_hidden(u1_struct_0(X5),u1_pre_topc(X5))
        | v2_pre_topc(X5)
        | ~ l1_pre_topc(X5) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X5),esk2_1(X5),esk3_1(X5)),u1_pre_topc(X5))
        | r1_tarski(esk1_1(X5),u1_pre_topc(X5))
        | ~ r2_hidden(u1_struct_0(X5),u1_pre_topc(X5))
        | v2_pre_topc(X5)
        | ~ l1_pre_topc(X5) )
      & ( m1_subset_1(esk2_1(X5),k1_zfmisc_1(u1_struct_0(X5)))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X5),esk1_1(X5)),u1_pre_topc(X5))
        | ~ r2_hidden(u1_struct_0(X5),u1_pre_topc(X5))
        | v2_pre_topc(X5)
        | ~ l1_pre_topc(X5) )
      & ( m1_subset_1(esk3_1(X5),k1_zfmisc_1(u1_struct_0(X5)))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X5),esk1_1(X5)),u1_pre_topc(X5))
        | ~ r2_hidden(u1_struct_0(X5),u1_pre_topc(X5))
        | v2_pre_topc(X5)
        | ~ l1_pre_topc(X5) )
      & ( r2_hidden(esk2_1(X5),u1_pre_topc(X5))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X5),esk1_1(X5)),u1_pre_topc(X5))
        | ~ r2_hidden(u1_struct_0(X5),u1_pre_topc(X5))
        | v2_pre_topc(X5)
        | ~ l1_pre_topc(X5) )
      & ( r2_hidden(esk3_1(X5),u1_pre_topc(X5))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X5),esk1_1(X5)),u1_pre_topc(X5))
        | ~ r2_hidden(u1_struct_0(X5),u1_pre_topc(X5))
        | v2_pre_topc(X5)
        | ~ l1_pre_topc(X5) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X5),esk2_1(X5),esk3_1(X5)),u1_pre_topc(X5))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X5),esk1_1(X5)),u1_pre_topc(X5))
        | ~ r2_hidden(u1_struct_0(X5),u1_pre_topc(X5))
        | v2_pre_topc(X5)
        | ~ l1_pre_topc(X5) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_pre_topc])])])])])).

cnf(c_0_45,negated_conjecture,
    ( ~ v1_tsep_1(esk6_0,esk5_0)
    | ~ m1_pre_topc(esk6_0,esk5_0)
    | g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)) != k8_tmap_1(esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_46,plain,
    ( v1_tsep_1(X2,X1)
    | ~ v3_pre_topc(esk4_2(X1,X2),X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_47,plain,
    ( esk4_2(X1,X2) = u1_struct_0(X2)
    | v1_tsep_1(X2,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_48,negated_conjecture,
    ( r2_hidden(u1_struct_0(esk6_0),u1_pre_topc(esk5_0))
    | u1_pre_topc(k8_tmap_1(esk5_0,esk6_0)) != u1_pre_topc(esk5_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_24]),c_0_25]),c_0_33]),c_0_26])]),c_0_34]),c_0_40])).

cnf(c_0_49,negated_conjecture,
    ( u1_pre_topc(k8_tmap_1(esk5_0,esk6_0)) = u1_pre_topc(esk5_0)
    | v2_struct_0(X1)
    | v1_tsep_1(esk6_0,esk5_0)
    | ~ m1_pre_topc(X1,esk5_0)
    | ~ r2_hidden(u1_struct_0(X1),u1_pre_topc(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_41]),c_0_33]),c_0_26])]),c_0_34])).

cnf(c_0_50,negated_conjecture,
    ( r2_hidden(u1_struct_0(esk6_0),u1_pre_topc(esk5_0))
    | ~ v1_tsep_1(esk6_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_25]),c_0_26])])).

cnf(c_0_51,plain,
    ( r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_52,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)) != k8_tmap_1(esk5_0,esk6_0)
    | ~ v1_tsep_1(esk6_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_25])])).

cnf(c_0_53,plain,
    ( v1_tsep_1(X1,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ v3_pre_topc(u1_struct_0(X1),X2)
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_54,plain,
    ( v3_pre_topc(X1,X2)
    | ~ r2_hidden(X1,u1_pre_topc(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_55,negated_conjecture,
    ( v2_struct_0(X1)
    | r2_hidden(u1_struct_0(esk6_0),u1_pre_topc(esk5_0))
    | ~ m1_pre_topc(X1,esk5_0)
    | ~ r2_hidden(u1_struct_0(X1),u1_pre_topc(esk5_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_50])).

cnf(c_0_56,negated_conjecture,
    ( r2_hidden(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_33]),c_0_26])])).

fof(c_0_57,plain,(
    ! [X27] :
      ( ~ l1_pre_topc(X27)
      | m1_pre_topc(X27,X27) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tsep_1])])).

cnf(c_0_58,negated_conjecture,
    ( v2_struct_0(X1)
    | k8_tmap_1(esk5_0,X1) != k8_tmap_1(esk5_0,esk6_0)
    | ~ v1_tsep_1(esk6_0,esk5_0)
    | ~ m1_pre_topc(X1,esk5_0)
    | ~ r2_hidden(u1_struct_0(X1),u1_pre_topc(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_36]),c_0_33]),c_0_26])]),c_0_34])).

cnf(c_0_59,plain,
    ( v1_tsep_1(X1,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ r2_hidden(u1_struct_0(X1),u1_pre_topc(X2))
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_17])).

cnf(c_0_60,negated_conjecture,
    ( r2_hidden(u1_struct_0(esk6_0),u1_pre_topc(esk5_0))
    | ~ m1_pre_topc(esk5_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_55]),c_0_56])])).

cnf(c_0_61,plain,
    ( m1_pre_topc(X1,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_62,negated_conjecture,
    ( v2_struct_0(X1)
    | k8_tmap_1(esk5_0,X1) != k8_tmap_1(esk5_0,esk6_0)
    | ~ m1_pre_topc(X1,esk5_0)
    | ~ r2_hidden(u1_struct_0(esk6_0),u1_pre_topc(esk5_0))
    | ~ r2_hidden(u1_struct_0(X1),u1_pre_topc(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_25]),c_0_26])])).

cnf(c_0_63,negated_conjecture,
    ( r2_hidden(u1_struct_0(esk6_0),u1_pre_topc(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_26])])).

cnf(c_0_64,negated_conjecture,
    ( v2_struct_0(X1)
    | k8_tmap_1(esk5_0,X1) != k8_tmap_1(esk5_0,esk6_0)
    | ~ m1_pre_topc(X1,esk5_0)
    | ~ r2_hidden(u1_struct_0(X1),u1_pre_topc(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_62,c_0_63])])).

cnf(c_0_65,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_63]),c_0_25])]),c_0_40]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:32:11 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.38/0.54  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S039A
% 0.38/0.54  # and selection function PSelectUnlessUniqMaxPos.
% 0.38/0.54  #
% 0.38/0.54  # Preprocessing time       : 0.028 s
% 0.38/0.54  # Presaturation interreduction done
% 0.38/0.54  
% 0.38/0.54  # Proof found!
% 0.38/0.54  # SZS status Theorem
% 0.38/0.54  # SZS output start CNFRefutation
% 0.38/0.54  fof(t114_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>(u1_struct_0(k8_tmap_1(X1,X2))=u1_struct_0(X1)&![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(X3=u1_struct_0(X2)=>u1_pre_topc(k8_tmap_1(X1,X2))=k5_tmap_1(X1,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t114_tmap_1)).
% 0.38/0.54  fof(t1_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 0.38/0.54  fof(t116_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>((v1_tsep_1(X2,X1)&m1_pre_topc(X2,X1))<=>g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))=k8_tmap_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t116_tmap_1)).
% 0.38/0.54  fof(abstractness_v1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>(v1_pre_topc(X1)=>X1=g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', abstractness_v1_pre_topc)).
% 0.38/0.54  fof(dt_k8_tmap_1, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_pre_topc(X2,X1))=>((v1_pre_topc(k8_tmap_1(X1,X2))&v2_pre_topc(k8_tmap_1(X1,X2)))&l1_pre_topc(k8_tmap_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k8_tmap_1)).
% 0.38/0.54  fof(t103_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(r2_hidden(X2,u1_pre_topc(X1))<=>u1_pre_topc(X1)=k5_tmap_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t103_tmap_1)).
% 0.38/0.54  fof(d5_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>r2_hidden(X2,u1_pre_topc(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_pre_topc)).
% 0.38/0.54  fof(d1_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>(v1_tsep_1(X2,X1)<=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(X3=u1_struct_0(X2)=>v3_pre_topc(X3,X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tsep_1)).
% 0.38/0.54  fof(d1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>(v2_pre_topc(X1)<=>((r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))&![X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>(r1_tarski(X2,u1_pre_topc(X1))=>r2_hidden(k5_setfam_1(u1_struct_0(X1),X2),u1_pre_topc(X1)))))&![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((r2_hidden(X2,u1_pre_topc(X1))&r2_hidden(X3,u1_pre_topc(X1)))=>r2_hidden(k9_subset_1(u1_struct_0(X1),X2,X3),u1_pre_topc(X1)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_pre_topc)).
% 0.38/0.54  fof(t2_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>m1_pre_topc(X1,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tsep_1)).
% 0.38/0.54  fof(c_0_10, plain, ![X22, X23, X24]:((u1_struct_0(k8_tmap_1(X22,X23))=u1_struct_0(X22)|(v2_struct_0(X23)|~m1_pre_topc(X23,X22))|(v2_struct_0(X22)|~v2_pre_topc(X22)|~l1_pre_topc(X22)))&(~m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X22)))|(X24!=u1_struct_0(X23)|u1_pre_topc(k8_tmap_1(X22,X23))=k5_tmap_1(X22,X24))|(v2_struct_0(X23)|~m1_pre_topc(X23,X22))|(v2_struct_0(X22)|~v2_pre_topc(X22)|~l1_pre_topc(X22)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t114_tmap_1])])])])])).
% 0.38/0.54  fof(c_0_11, plain, ![X25, X26]:(~l1_pre_topc(X25)|(~m1_pre_topc(X26,X25)|m1_subset_1(u1_struct_0(X26),k1_zfmisc_1(u1_struct_0(X25))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).
% 0.38/0.54  fof(c_0_12, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>((v1_tsep_1(X2,X1)&m1_pre_topc(X2,X1))<=>g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))=k8_tmap_1(X1,X2))))), inference(assume_negation,[status(cth)],[t116_tmap_1])).
% 0.38/0.54  fof(c_0_13, plain, ![X4]:(~l1_pre_topc(X4)|(~v1_pre_topc(X4)|X4=g1_pre_topc(u1_struct_0(X4),u1_pre_topc(X4)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[abstractness_v1_pre_topc])])).
% 0.38/0.54  fof(c_0_14, plain, ![X18, X19]:(((v1_pre_topc(k8_tmap_1(X18,X19))|(v2_struct_0(X18)|~v2_pre_topc(X18)|~l1_pre_topc(X18)|~m1_pre_topc(X19,X18)))&(v2_pre_topc(k8_tmap_1(X18,X19))|(v2_struct_0(X18)|~v2_pre_topc(X18)|~l1_pre_topc(X18)|~m1_pre_topc(X19,X18))))&(l1_pre_topc(k8_tmap_1(X18,X19))|(v2_struct_0(X18)|~v2_pre_topc(X18)|~l1_pre_topc(X18)|~m1_pre_topc(X19,X18)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k8_tmap_1])])])])).
% 0.38/0.54  fof(c_0_15, plain, ![X20, X21]:((~r2_hidden(X21,u1_pre_topc(X20))|u1_pre_topc(X20)=k5_tmap_1(X20,X21)|~m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))|(v2_struct_0(X20)|~v2_pre_topc(X20)|~l1_pre_topc(X20)))&(u1_pre_topc(X20)!=k5_tmap_1(X20,X21)|r2_hidden(X21,u1_pre_topc(X20))|~m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))|(v2_struct_0(X20)|~v2_pre_topc(X20)|~l1_pre_topc(X20)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t103_tmap_1])])])])])).
% 0.38/0.54  cnf(c_0_16, plain, (u1_pre_topc(k8_tmap_1(X2,X3))=k5_tmap_1(X2,X1)|v2_struct_0(X3)|v2_struct_0(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|X1!=u1_struct_0(X3)|~m1_pre_topc(X3,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.38/0.54  cnf(c_0_17, plain, (m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.38/0.54  fof(c_0_18, negated_conjecture, (((~v2_struct_0(esk5_0)&v2_pre_topc(esk5_0))&l1_pre_topc(esk5_0))&((~v2_struct_0(esk6_0)&m1_pre_topc(esk6_0,esk5_0))&((~v1_tsep_1(esk6_0,esk5_0)|~m1_pre_topc(esk6_0,esk5_0)|g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))!=k8_tmap_1(esk5_0,esk6_0))&((v1_tsep_1(esk6_0,esk5_0)|g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))=k8_tmap_1(esk5_0,esk6_0))&(m1_pre_topc(esk6_0,esk5_0)|g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))=k8_tmap_1(esk5_0,esk6_0)))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_12])])])])])).
% 0.38/0.54  cnf(c_0_19, plain, (X1=g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))|~l1_pre_topc(X1)|~v1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.38/0.54  cnf(c_0_20, plain, (u1_struct_0(k8_tmap_1(X1,X2))=u1_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.38/0.54  cnf(c_0_21, plain, (l1_pre_topc(k8_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.38/0.54  cnf(c_0_22, plain, (v1_pre_topc(k8_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.38/0.54  cnf(c_0_23, plain, (u1_pre_topc(X2)=k5_tmap_1(X2,X1)|v2_struct_0(X2)|~r2_hidden(X1,u1_pre_topc(X2))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.38/0.54  cnf(c_0_24, plain, (k5_tmap_1(X1,u1_struct_0(X2))=u1_pre_topc(k8_tmap_1(X1,X2))|v2_struct_0(X2)|v2_struct_0(X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_16]), c_0_17])).
% 0.38/0.54  cnf(c_0_25, negated_conjecture, (m1_pre_topc(esk6_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.38/0.54  cnf(c_0_26, negated_conjecture, (l1_pre_topc(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.38/0.54  cnf(c_0_27, plain, (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(k8_tmap_1(X1,X2)))=k8_tmap_1(X1,X2)|v2_struct_0(X1)|v2_struct_0(X2)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_21]), c_0_22])).
% 0.38/0.54  cnf(c_0_28, plain, (u1_pre_topc(k8_tmap_1(X1,X2))=u1_pre_topc(X1)|v2_struct_0(X2)|v2_struct_0(X1)|~m1_pre_topc(X2,X1)|~r2_hidden(u1_struct_0(X2),u1_pre_topc(X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_17])).
% 0.38/0.54  fof(c_0_29, plain, ![X12, X13]:((~v3_pre_topc(X13,X12)|r2_hidden(X13,u1_pre_topc(X12))|~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))|~l1_pre_topc(X12))&(~r2_hidden(X13,u1_pre_topc(X12))|v3_pre_topc(X13,X12)|~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))|~l1_pre_topc(X12))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_pre_topc])])])])).
% 0.38/0.54  fof(c_0_30, plain, ![X14, X15, X16]:((~v1_tsep_1(X15,X14)|(~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X14)))|(X16!=u1_struct_0(X15)|v3_pre_topc(X16,X14)))|~m1_pre_topc(X15,X14)|~l1_pre_topc(X14))&((m1_subset_1(esk4_2(X14,X15),k1_zfmisc_1(u1_struct_0(X14)))|v1_tsep_1(X15,X14)|~m1_pre_topc(X15,X14)|~l1_pre_topc(X14))&((esk4_2(X14,X15)=u1_struct_0(X15)|v1_tsep_1(X15,X14)|~m1_pre_topc(X15,X14)|~l1_pre_topc(X14))&(~v3_pre_topc(esk4_2(X14,X15),X14)|v1_tsep_1(X15,X14)|~m1_pre_topc(X15,X14)|~l1_pre_topc(X14))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tsep_1])])])])])).
% 0.38/0.54  cnf(c_0_31, plain, (r2_hidden(X2,u1_pre_topc(X1))|v2_struct_0(X1)|u1_pre_topc(X1)!=k5_tmap_1(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.38/0.54  cnf(c_0_32, negated_conjecture, (m1_subset_1(u1_struct_0(esk6_0),k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_25]), c_0_26])])).
% 0.38/0.54  cnf(c_0_33, negated_conjecture, (v2_pre_topc(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.38/0.54  cnf(c_0_34, negated_conjecture, (~v2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.38/0.54  cnf(c_0_35, negated_conjecture, (v1_tsep_1(esk6_0,esk5_0)|g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))=k8_tmap_1(esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.38/0.54  cnf(c_0_36, plain, (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))=k8_tmap_1(X1,X2)|v2_struct_0(X2)|v2_struct_0(X1)|~m1_pre_topc(X2,X1)|~r2_hidden(u1_struct_0(X2),u1_pre_topc(X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.38/0.54  cnf(c_0_37, plain, (r2_hidden(X1,u1_pre_topc(X2))|~v3_pre_topc(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.38/0.54  cnf(c_0_38, plain, (v3_pre_topc(X3,X2)|~v1_tsep_1(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|X3!=u1_struct_0(X1)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.38/0.54  cnf(c_0_39, negated_conjecture, (r2_hidden(u1_struct_0(esk6_0),u1_pre_topc(esk5_0))|k5_tmap_1(esk5_0,u1_struct_0(esk6_0))!=u1_pre_topc(esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_33]), c_0_26])]), c_0_34])).
% 0.38/0.54  cnf(c_0_40, negated_conjecture, (~v2_struct_0(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.38/0.54  cnf(c_0_41, negated_conjecture, (k8_tmap_1(esk5_0,X1)=k8_tmap_1(esk5_0,esk6_0)|v2_struct_0(X1)|v1_tsep_1(esk6_0,esk5_0)|~m1_pre_topc(X1,esk5_0)|~r2_hidden(u1_struct_0(X1),u1_pre_topc(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_33]), c_0_26])]), c_0_34])).
% 0.38/0.54  cnf(c_0_42, negated_conjecture, (r2_hidden(u1_struct_0(esk6_0),u1_pre_topc(esk5_0))|~v3_pre_topc(u1_struct_0(esk6_0),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_32]), c_0_26])])).
% 0.38/0.54  cnf(c_0_43, plain, (v3_pre_topc(u1_struct_0(X1),X2)|~v1_tsep_1(X1,X2)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_38]), c_0_17])).
% 0.38/0.54  fof(c_0_44, plain, ![X5, X6, X7, X8]:((((r2_hidden(u1_struct_0(X5),u1_pre_topc(X5))|~v2_pre_topc(X5)|~l1_pre_topc(X5))&(~m1_subset_1(X6,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X5))))|(~r1_tarski(X6,u1_pre_topc(X5))|r2_hidden(k5_setfam_1(u1_struct_0(X5),X6),u1_pre_topc(X5)))|~v2_pre_topc(X5)|~l1_pre_topc(X5)))&(~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X5)))|(~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X5)))|(~r2_hidden(X7,u1_pre_topc(X5))|~r2_hidden(X8,u1_pre_topc(X5))|r2_hidden(k9_subset_1(u1_struct_0(X5),X7,X8),u1_pre_topc(X5))))|~v2_pre_topc(X5)|~l1_pre_topc(X5)))&(((m1_subset_1(esk2_1(X5),k1_zfmisc_1(u1_struct_0(X5)))|(m1_subset_1(esk1_1(X5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X5))))|~r2_hidden(u1_struct_0(X5),u1_pre_topc(X5)))|v2_pre_topc(X5)|~l1_pre_topc(X5))&((m1_subset_1(esk3_1(X5),k1_zfmisc_1(u1_struct_0(X5)))|(m1_subset_1(esk1_1(X5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X5))))|~r2_hidden(u1_struct_0(X5),u1_pre_topc(X5)))|v2_pre_topc(X5)|~l1_pre_topc(X5))&(((r2_hidden(esk2_1(X5),u1_pre_topc(X5))|(m1_subset_1(esk1_1(X5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X5))))|~r2_hidden(u1_struct_0(X5),u1_pre_topc(X5)))|v2_pre_topc(X5)|~l1_pre_topc(X5))&(r2_hidden(esk3_1(X5),u1_pre_topc(X5))|(m1_subset_1(esk1_1(X5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X5))))|~r2_hidden(u1_struct_0(X5),u1_pre_topc(X5)))|v2_pre_topc(X5)|~l1_pre_topc(X5)))&(~r2_hidden(k9_subset_1(u1_struct_0(X5),esk2_1(X5),esk3_1(X5)),u1_pre_topc(X5))|(m1_subset_1(esk1_1(X5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X5))))|~r2_hidden(u1_struct_0(X5),u1_pre_topc(X5)))|v2_pre_topc(X5)|~l1_pre_topc(X5)))))&(((m1_subset_1(esk2_1(X5),k1_zfmisc_1(u1_struct_0(X5)))|(r1_tarski(esk1_1(X5),u1_pre_topc(X5))|~r2_hidden(u1_struct_0(X5),u1_pre_topc(X5)))|v2_pre_topc(X5)|~l1_pre_topc(X5))&((m1_subset_1(esk3_1(X5),k1_zfmisc_1(u1_struct_0(X5)))|(r1_tarski(esk1_1(X5),u1_pre_topc(X5))|~r2_hidden(u1_struct_0(X5),u1_pre_topc(X5)))|v2_pre_topc(X5)|~l1_pre_topc(X5))&(((r2_hidden(esk2_1(X5),u1_pre_topc(X5))|(r1_tarski(esk1_1(X5),u1_pre_topc(X5))|~r2_hidden(u1_struct_0(X5),u1_pre_topc(X5)))|v2_pre_topc(X5)|~l1_pre_topc(X5))&(r2_hidden(esk3_1(X5),u1_pre_topc(X5))|(r1_tarski(esk1_1(X5),u1_pre_topc(X5))|~r2_hidden(u1_struct_0(X5),u1_pre_topc(X5)))|v2_pre_topc(X5)|~l1_pre_topc(X5)))&(~r2_hidden(k9_subset_1(u1_struct_0(X5),esk2_1(X5),esk3_1(X5)),u1_pre_topc(X5))|(r1_tarski(esk1_1(X5),u1_pre_topc(X5))|~r2_hidden(u1_struct_0(X5),u1_pre_topc(X5)))|v2_pre_topc(X5)|~l1_pre_topc(X5)))))&((m1_subset_1(esk2_1(X5),k1_zfmisc_1(u1_struct_0(X5)))|(~r2_hidden(k5_setfam_1(u1_struct_0(X5),esk1_1(X5)),u1_pre_topc(X5))|~r2_hidden(u1_struct_0(X5),u1_pre_topc(X5)))|v2_pre_topc(X5)|~l1_pre_topc(X5))&((m1_subset_1(esk3_1(X5),k1_zfmisc_1(u1_struct_0(X5)))|(~r2_hidden(k5_setfam_1(u1_struct_0(X5),esk1_1(X5)),u1_pre_topc(X5))|~r2_hidden(u1_struct_0(X5),u1_pre_topc(X5)))|v2_pre_topc(X5)|~l1_pre_topc(X5))&(((r2_hidden(esk2_1(X5),u1_pre_topc(X5))|(~r2_hidden(k5_setfam_1(u1_struct_0(X5),esk1_1(X5)),u1_pre_topc(X5))|~r2_hidden(u1_struct_0(X5),u1_pre_topc(X5)))|v2_pre_topc(X5)|~l1_pre_topc(X5))&(r2_hidden(esk3_1(X5),u1_pre_topc(X5))|(~r2_hidden(k5_setfam_1(u1_struct_0(X5),esk1_1(X5)),u1_pre_topc(X5))|~r2_hidden(u1_struct_0(X5),u1_pre_topc(X5)))|v2_pre_topc(X5)|~l1_pre_topc(X5)))&(~r2_hidden(k9_subset_1(u1_struct_0(X5),esk2_1(X5),esk3_1(X5)),u1_pre_topc(X5))|(~r2_hidden(k5_setfam_1(u1_struct_0(X5),esk1_1(X5)),u1_pre_topc(X5))|~r2_hidden(u1_struct_0(X5),u1_pre_topc(X5)))|v2_pre_topc(X5)|~l1_pre_topc(X5)))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_pre_topc])])])])])).
% 0.38/0.54  cnf(c_0_45, negated_conjecture, (~v1_tsep_1(esk6_0,esk5_0)|~m1_pre_topc(esk6_0,esk5_0)|g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))!=k8_tmap_1(esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.38/0.54  cnf(c_0_46, plain, (v1_tsep_1(X2,X1)|~v3_pre_topc(esk4_2(X1,X2),X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.38/0.54  cnf(c_0_47, plain, (esk4_2(X1,X2)=u1_struct_0(X2)|v1_tsep_1(X2,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.38/0.54  cnf(c_0_48, negated_conjecture, (r2_hidden(u1_struct_0(esk6_0),u1_pre_topc(esk5_0))|u1_pre_topc(k8_tmap_1(esk5_0,esk6_0))!=u1_pre_topc(esk5_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_24]), c_0_25]), c_0_33]), c_0_26])]), c_0_34]), c_0_40])).
% 0.38/0.54  cnf(c_0_49, negated_conjecture, (u1_pre_topc(k8_tmap_1(esk5_0,esk6_0))=u1_pre_topc(esk5_0)|v2_struct_0(X1)|v1_tsep_1(esk6_0,esk5_0)|~m1_pre_topc(X1,esk5_0)|~r2_hidden(u1_struct_0(X1),u1_pre_topc(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_41]), c_0_33]), c_0_26])]), c_0_34])).
% 0.38/0.54  cnf(c_0_50, negated_conjecture, (r2_hidden(u1_struct_0(esk6_0),u1_pre_topc(esk5_0))|~v1_tsep_1(esk6_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_25]), c_0_26])])).
% 0.38/0.54  cnf(c_0_51, plain, (r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.38/0.54  cnf(c_0_52, negated_conjecture, (g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))!=k8_tmap_1(esk5_0,esk6_0)|~v1_tsep_1(esk6_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_45, c_0_25])])).
% 0.38/0.54  cnf(c_0_53, plain, (v1_tsep_1(X1,X2)|~m1_pre_topc(X1,X2)|~v3_pre_topc(u1_struct_0(X1),X2)|~l1_pre_topc(X2)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.38/0.54  cnf(c_0_54, plain, (v3_pre_topc(X1,X2)|~r2_hidden(X1,u1_pre_topc(X2))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.38/0.54  cnf(c_0_55, negated_conjecture, (v2_struct_0(X1)|r2_hidden(u1_struct_0(esk6_0),u1_pre_topc(esk5_0))|~m1_pre_topc(X1,esk5_0)|~r2_hidden(u1_struct_0(X1),u1_pre_topc(esk5_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_50])).
% 0.38/0.54  cnf(c_0_56, negated_conjecture, (r2_hidden(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_33]), c_0_26])])).
% 0.38/0.54  fof(c_0_57, plain, ![X27]:(~l1_pre_topc(X27)|m1_pre_topc(X27,X27)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tsep_1])])).
% 0.38/0.54  cnf(c_0_58, negated_conjecture, (v2_struct_0(X1)|k8_tmap_1(esk5_0,X1)!=k8_tmap_1(esk5_0,esk6_0)|~v1_tsep_1(esk6_0,esk5_0)|~m1_pre_topc(X1,esk5_0)|~r2_hidden(u1_struct_0(X1),u1_pre_topc(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_36]), c_0_33]), c_0_26])]), c_0_34])).
% 0.38/0.54  cnf(c_0_59, plain, (v1_tsep_1(X1,X2)|~m1_pre_topc(X1,X2)|~r2_hidden(u1_struct_0(X1),u1_pre_topc(X2))|~l1_pre_topc(X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_17])).
% 0.38/0.54  cnf(c_0_60, negated_conjecture, (r2_hidden(u1_struct_0(esk6_0),u1_pre_topc(esk5_0))|~m1_pre_topc(esk5_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_55]), c_0_56])])).
% 0.38/0.54  cnf(c_0_61, plain, (m1_pre_topc(X1,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.38/0.54  cnf(c_0_62, negated_conjecture, (v2_struct_0(X1)|k8_tmap_1(esk5_0,X1)!=k8_tmap_1(esk5_0,esk6_0)|~m1_pre_topc(X1,esk5_0)|~r2_hidden(u1_struct_0(esk6_0),u1_pre_topc(esk5_0))|~r2_hidden(u1_struct_0(X1),u1_pre_topc(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_25]), c_0_26])])).
% 0.38/0.54  cnf(c_0_63, negated_conjecture, (r2_hidden(u1_struct_0(esk6_0),u1_pre_topc(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_26])])).
% 0.38/0.54  cnf(c_0_64, negated_conjecture, (v2_struct_0(X1)|k8_tmap_1(esk5_0,X1)!=k8_tmap_1(esk5_0,esk6_0)|~m1_pre_topc(X1,esk5_0)|~r2_hidden(u1_struct_0(X1),u1_pre_topc(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_62, c_0_63])])).
% 0.38/0.54  cnf(c_0_65, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_63]), c_0_25])]), c_0_40]), ['proof']).
% 0.38/0.54  # SZS output end CNFRefutation
% 0.38/0.54  # Proof object total steps             : 66
% 0.38/0.54  # Proof object clause steps            : 45
% 0.38/0.54  # Proof object formula steps           : 21
% 0.38/0.54  # Proof object conjectures             : 26
% 0.38/0.54  # Proof object clause conjectures      : 23
% 0.38/0.54  # Proof object formula conjectures     : 3
% 0.38/0.54  # Proof object initial clauses used    : 22
% 0.38/0.54  # Proof object initial formulas used   : 10
% 0.38/0.54  # Proof object generating inferences   : 19
% 0.38/0.54  # Proof object simplifying inferences  : 54
% 0.38/0.54  # Training examples: 0 positive, 0 negative
% 0.38/0.54  # Parsed axioms                        : 10
% 0.38/0.54  # Removed by relevancy pruning/SinE    : 0
% 0.38/0.54  # Initial clauses                      : 42
% 0.38/0.54  # Removed in clause preprocessing      : 0
% 0.38/0.54  # Initial clauses in saturation        : 42
% 0.38/0.54  # Processed clauses                    : 1623
% 0.38/0.54  # ...of these trivial                  : 14
% 0.38/0.54  # ...subsumed                          : 1014
% 0.38/0.54  # ...remaining for further processing  : 595
% 0.38/0.54  # Other redundant clauses eliminated   : 2
% 0.38/0.54  # Clauses deleted for lack of memory   : 0
% 0.38/0.54  # Backward-subsumed                    : 50
% 0.38/0.54  # Backward-rewritten                   : 83
% 0.38/0.54  # Generated clauses                    : 5698
% 0.38/0.55  # ...of the previous two non-trivial   : 4325
% 0.38/0.55  # Contextual simplify-reflections      : 103
% 0.38/0.55  # Paramodulations                      : 5600
% 0.38/0.55  # Factorizations                       : 96
% 0.38/0.55  # Equation resolutions                 : 2
% 0.38/0.55  # Propositional unsat checks           : 0
% 0.38/0.55  #    Propositional check models        : 0
% 0.38/0.55  #    Propositional check unsatisfiable : 0
% 0.38/0.55  #    Propositional clauses             : 0
% 0.38/0.55  #    Propositional clauses after purity: 0
% 0.38/0.55  #    Propositional unsat core size     : 0
% 0.38/0.55  #    Propositional preprocessing time  : 0.000
% 0.38/0.55  #    Propositional encoding time       : 0.000
% 0.38/0.55  #    Propositional solver time         : 0.000
% 0.38/0.55  #    Success case prop preproc time    : 0.000
% 0.38/0.55  #    Success case prop encoding time   : 0.000
% 0.38/0.55  #    Success case prop solver time     : 0.000
% 0.38/0.55  # Current number of processed clauses  : 419
% 0.38/0.55  #    Positive orientable unit clauses  : 48
% 0.38/0.55  #    Positive unorientable unit clauses: 0
% 0.38/0.55  #    Negative unit clauses             : 2
% 0.38/0.55  #    Non-unit-clauses                  : 369
% 0.38/0.55  # Current number of unprocessed clauses: 2748
% 0.38/0.55  # ...number of literals in the above   : 23459
% 0.38/0.55  # Current number of archived formulas  : 0
% 0.38/0.55  # Current number of archived clauses   : 174
% 0.38/0.55  # Clause-clause subsumption calls (NU) : 44686
% 0.38/0.55  # Rec. Clause-clause subsumption calls : 4737
% 0.38/0.55  # Non-unit clause-clause subsumptions  : 1167
% 0.38/0.55  # Unit Clause-clause subsumption calls : 675
% 0.38/0.55  # Rewrite failures with RHS unbound    : 0
% 0.38/0.55  # BW rewrite match attempts            : 224
% 0.38/0.55  # BW rewrite match successes           : 16
% 0.38/0.55  # Condensation attempts                : 0
% 0.38/0.55  # Condensation successes               : 0
% 0.38/0.55  # Termbank termtop insertions          : 183154
% 0.38/0.55  
% 0.38/0.55  # -------------------------------------------------
% 0.38/0.55  # User time                : 0.195 s
% 0.38/0.55  # System time              : 0.011 s
% 0.38/0.55  # Total time               : 0.206 s
% 0.38/0.55  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
