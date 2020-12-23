%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:18:29 EST 2020

% Result     : Theorem 1.75s
% Output     : CNFRefutation 1.75s
% Verified   : 
% Statistics : Number of formulae       :  146 (86271 expanded)
%              Number of clauses        :  113 (29355 expanded)
%              Number of leaves         :   16 (21460 expanded)
%              Depth                    :   22
%              Number of atoms          :  727 (816768 expanded)
%              Number of equality atoms :   82 (15307 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   38 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t104_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( u1_struct_0(k6_tmap_1(X1,X2)) = u1_struct_0(X1)
            & u1_pre_topc(k6_tmap_1(X1,X2)) = k5_tmap_1(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_tmap_1)).

fof(t1_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

fof(t122_tmap_1,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ( ( v1_tsep_1(X2,X1)
              & m1_pre_topc(X2,X1) )
          <=> ( v1_funct_1(k9_tmap_1(X1,X2))
              & v1_funct_2(k9_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))
              & v5_pre_topc(k9_tmap_1(X1,X2),X1,k8_tmap_1(X1,X2))
              & m1_subset_1(k9_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2))))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t122_tmap_1)).

fof(dt_k6_tmap_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( v1_pre_topc(k6_tmap_1(X1,X2))
        & v2_pre_topc(k6_tmap_1(X1,X2))
        & l1_pre_topc(k6_tmap_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_tmap_1)).

fof(t2_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_pre_topc(X1,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

fof(d10_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k7_tmap_1(X1,X2) = k6_partfun1(u1_struct_0(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_tmap_1)).

fof(d11_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ! [X3] :
              ( ( v1_pre_topc(X3)
                & v2_pre_topc(X3)
                & l1_pre_topc(X3) )
             => ( X3 = k8_tmap_1(X1,X2)
              <=> ! [X4] :
                    ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                   => ( X4 = u1_struct_0(X2)
                     => X3 = k6_tmap_1(X1,X4) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_tmap_1)).

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

fof(dt_k7_tmap_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( v1_funct_1(k7_tmap_1(X1,X2))
        & v1_funct_2(k7_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))
        & m1_subset_1(k7_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2))))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_tmap_1)).

fof(t113_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_pre_topc(X2,X1)
          <=> ( v1_funct_1(k7_tmap_1(X1,X2))
              & v1_funct_2(k7_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))
              & v5_pre_topc(k7_tmap_1(X1,X2),X1,k6_tmap_1(X1,X2))
              & m1_subset_1(k7_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2))))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_tmap_1)).

fof(fc4_tmap_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ~ v2_struct_0(k6_tmap_1(X1,X2))
        & v1_pre_topc(k6_tmap_1(X1,X2))
        & v2_pre_topc(k6_tmap_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_tmap_1)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(d12_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2))))) )
             => ( X3 = k9_tmap_1(X1,X2)
              <=> ! [X4] :
                    ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                   => ( X4 = u1_struct_0(X2)
                     => r1_funct_2(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X4)),X3,k7_tmap_1(X1,X4)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_tmap_1)).

fof(reflexivity_r1_funct_2,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( ~ v1_xboole_0(X2)
        & ~ v1_xboole_0(X4)
        & v1_funct_1(X5)
        & v1_funct_2(X5,X1,X2)
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X6)
        & v1_funct_2(X6,X3,X4)
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
     => r1_funct_2(X1,X2,X3,X4,X5,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r1_funct_2)).

fof(dt_k9_tmap_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_pre_topc(X2,X1) )
     => ( v1_funct_1(k9_tmap_1(X1,X2))
        & v1_funct_2(k9_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))
        & m1_subset_1(k9_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2))))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_tmap_1)).

fof(c_0_16,plain,(
    ! [X42,X43] :
      ( ( u1_struct_0(k6_tmap_1(X42,X43)) = u1_struct_0(X42)
        | ~ m1_subset_1(X43,k1_zfmisc_1(u1_struct_0(X42)))
        | v2_struct_0(X42)
        | ~ v2_pre_topc(X42)
        | ~ l1_pre_topc(X42) )
      & ( u1_pre_topc(k6_tmap_1(X42,X43)) = k5_tmap_1(X42,X43)
        | ~ m1_subset_1(X43,k1_zfmisc_1(u1_struct_0(X42)))
        | v2_struct_0(X42)
        | ~ v2_pre_topc(X42)
        | ~ l1_pre_topc(X42) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t104_tmap_1])])])])])).

fof(c_0_17,plain,(
    ! [X46,X47] :
      ( ~ l1_pre_topc(X46)
      | ~ m1_pre_topc(X47,X46)
      | m1_subset_1(u1_struct_0(X47),k1_zfmisc_1(u1_struct_0(X46))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).

fof(c_0_18,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_pre_topc(X2,X1)
           => ( ( v1_tsep_1(X2,X1)
                & m1_pre_topc(X2,X1) )
            <=> ( v1_funct_1(k9_tmap_1(X1,X2))
                & v1_funct_2(k9_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))
                & v5_pre_topc(k9_tmap_1(X1,X2),X1,k8_tmap_1(X1,X2))
                & m1_subset_1(k9_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2))))) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t122_tmap_1])).

cnf(c_0_19,plain,
    ( u1_struct_0(k6_tmap_1(X1,X2)) = u1_struct_0(X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,plain,
    ( m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_21,negated_conjecture,
    ( ~ v2_struct_0(esk4_0)
    & v2_pre_topc(esk4_0)
    & l1_pre_topc(esk4_0)
    & m1_pre_topc(esk5_0,esk4_0)
    & ( ~ v1_tsep_1(esk5_0,esk4_0)
      | ~ m1_pre_topc(esk5_0,esk4_0)
      | ~ v1_funct_1(k9_tmap_1(esk4_0,esk5_0))
      | ~ v1_funct_2(k9_tmap_1(esk4_0,esk5_0),u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk4_0,esk5_0)))
      | ~ v5_pre_topc(k9_tmap_1(esk4_0,esk5_0),esk4_0,k8_tmap_1(esk4_0,esk5_0))
      | ~ m1_subset_1(k9_tmap_1(esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk4_0,esk5_0))))) )
    & ( v1_funct_1(k9_tmap_1(esk4_0,esk5_0))
      | v1_tsep_1(esk5_0,esk4_0) )
    & ( v1_funct_2(k9_tmap_1(esk4_0,esk5_0),u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk4_0,esk5_0)))
      | v1_tsep_1(esk5_0,esk4_0) )
    & ( v5_pre_topc(k9_tmap_1(esk4_0,esk5_0),esk4_0,k8_tmap_1(esk4_0,esk5_0))
      | v1_tsep_1(esk5_0,esk4_0) )
    & ( m1_subset_1(k9_tmap_1(esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk4_0,esk5_0)))))
      | v1_tsep_1(esk5_0,esk4_0) )
    & ( v1_funct_1(k9_tmap_1(esk4_0,esk5_0))
      | m1_pre_topc(esk5_0,esk4_0) )
    & ( v1_funct_2(k9_tmap_1(esk4_0,esk5_0),u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk4_0,esk5_0)))
      | m1_pre_topc(esk5_0,esk4_0) )
    & ( v5_pre_topc(k9_tmap_1(esk4_0,esk5_0),esk4_0,k8_tmap_1(esk4_0,esk5_0))
      | m1_pre_topc(esk5_0,esk4_0) )
    & ( m1_subset_1(k9_tmap_1(esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk4_0,esk5_0)))))
      | m1_pre_topc(esk5_0,esk4_0) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_18])])])])])).

fof(c_0_22,plain,(
    ! [X34,X35] :
      ( ( v1_pre_topc(k6_tmap_1(X34,X35))
        | v2_struct_0(X34)
        | ~ v2_pre_topc(X34)
        | ~ l1_pre_topc(X34)
        | ~ m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X34))) )
      & ( v2_pre_topc(k6_tmap_1(X34,X35))
        | v2_struct_0(X34)
        | ~ v2_pre_topc(X34)
        | ~ l1_pre_topc(X34)
        | ~ m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X34))) )
      & ( l1_pre_topc(k6_tmap_1(X34,X35))
        | v2_struct_0(X34)
        | ~ v2_pre_topc(X34)
        | ~ l1_pre_topc(X34)
        | ~ m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X34))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_tmap_1])])])])).

cnf(c_0_23,plain,
    ( u1_struct_0(k6_tmap_1(X1,u1_struct_0(X2))) = u1_struct_0(X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_24,negated_conjecture,
    ( m1_pre_topc(esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_25,negated_conjecture,
    ( v2_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_26,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,plain,
    ( l1_pre_topc(k6_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,negated_conjecture,
    ( u1_struct_0(k6_tmap_1(esk4_0,u1_struct_0(esk5_0))) = u1_struct_0(esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25]),c_0_26])]),c_0_27])).

fof(c_0_30,plain,(
    ! [X48] :
      ( ~ l1_pre_topc(X48)
      | m1_pre_topc(X48,X48) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tsep_1])])).

cnf(c_0_31,plain,
    ( v2_struct_0(X1)
    | l1_pre_topc(k6_tmap_1(X1,u1_struct_0(X2)))
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_20])).

fof(c_0_32,plain,(
    ! [X18,X19] :
      ( v2_struct_0(X18)
      | ~ v2_pre_topc(X18)
      | ~ l1_pre_topc(X18)
      | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))
      | k7_tmap_1(X18,X19) = k6_partfun1(u1_struct_0(X18)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d10_tmap_1])])])])).

fof(c_0_33,plain,(
    ! [X20,X21,X22,X23] :
      ( ( X22 != k8_tmap_1(X20,X21)
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X20)))
        | X23 != u1_struct_0(X21)
        | X22 = k6_tmap_1(X20,X23)
        | ~ v1_pre_topc(X22)
        | ~ v2_pre_topc(X22)
        | ~ l1_pre_topc(X22)
        | ~ m1_pre_topc(X21,X20)
        | v2_struct_0(X20)
        | ~ v2_pre_topc(X20)
        | ~ l1_pre_topc(X20) )
      & ( m1_subset_1(esk1_3(X20,X21,X22),k1_zfmisc_1(u1_struct_0(X20)))
        | X22 = k8_tmap_1(X20,X21)
        | ~ v1_pre_topc(X22)
        | ~ v2_pre_topc(X22)
        | ~ l1_pre_topc(X22)
        | ~ m1_pre_topc(X21,X20)
        | v2_struct_0(X20)
        | ~ v2_pre_topc(X20)
        | ~ l1_pre_topc(X20) )
      & ( esk1_3(X20,X21,X22) = u1_struct_0(X21)
        | X22 = k8_tmap_1(X20,X21)
        | ~ v1_pre_topc(X22)
        | ~ v2_pre_topc(X22)
        | ~ l1_pre_topc(X22)
        | ~ m1_pre_topc(X21,X20)
        | v2_struct_0(X20)
        | ~ v2_pre_topc(X20)
        | ~ l1_pre_topc(X20) )
      & ( X22 != k6_tmap_1(X20,esk1_3(X20,X21,X22))
        | X22 = k8_tmap_1(X20,X21)
        | ~ v1_pre_topc(X22)
        | ~ v2_pre_topc(X22)
        | ~ l1_pre_topc(X22)
        | ~ m1_pre_topc(X21,X20)
        | v2_struct_0(X20)
        | ~ v2_pre_topc(X20)
        | ~ l1_pre_topc(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d11_tmap_1])])])])])])).

cnf(c_0_34,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(k6_tmap_1(esk4_0,u1_struct_0(esk5_0)),X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_29])).

cnf(c_0_35,plain,
    ( m1_pre_topc(X1,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_36,negated_conjecture,
    ( l1_pre_topc(k6_tmap_1(esk4_0,u1_struct_0(esk5_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_24]),c_0_25]),c_0_26])]),c_0_27])).

fof(c_0_37,plain,(
    ! [X30,X31,X32] :
      ( ( ~ v1_tsep_1(X31,X30)
        | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X30)))
        | X32 != u1_struct_0(X31)
        | v3_pre_topc(X32,X30)
        | ~ m1_pre_topc(X31,X30)
        | ~ l1_pre_topc(X30) )
      & ( m1_subset_1(esk3_2(X30,X31),k1_zfmisc_1(u1_struct_0(X30)))
        | v1_tsep_1(X31,X30)
        | ~ m1_pre_topc(X31,X30)
        | ~ l1_pre_topc(X30) )
      & ( esk3_2(X30,X31) = u1_struct_0(X31)
        | v1_tsep_1(X31,X30)
        | ~ m1_pre_topc(X31,X30)
        | ~ l1_pre_topc(X30) )
      & ( ~ v3_pre_topc(esk3_2(X30,X31),X30)
        | v1_tsep_1(X31,X30)
        | ~ m1_pre_topc(X31,X30)
        | ~ l1_pre_topc(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tsep_1])])])])])).

cnf(c_0_38,plain,
    ( v2_struct_0(X1)
    | k7_tmap_1(X1,X2) = k6_partfun1(u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_39,plain,
    ( v1_pre_topc(k6_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_40,plain,
    ( v2_pre_topc(k6_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_41,plain,
    ( esk1_3(X1,X2,X3) = u1_struct_0(X2)
    | X3 = k8_tmap_1(X1,X2)
    | v2_struct_0(X1)
    | ~ v1_pre_topc(X3)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_42,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_29]),c_0_36])])).

cnf(c_0_43,plain,
    ( v2_struct_0(X1)
    | l1_pre_topc(k6_tmap_1(X1,u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_35])).

cnf(c_0_44,plain,
    ( m1_subset_1(esk3_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | v1_tsep_1(X2,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_45,plain,
    ( k7_tmap_1(X1,u1_struct_0(X2)) = k6_partfun1(u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_20])).

cnf(c_0_46,plain,
    ( v1_pre_topc(k6_tmap_1(X1,u1_struct_0(X2)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_20])).

cnf(c_0_47,plain,
    ( v2_pre_topc(k6_tmap_1(X1,u1_struct_0(X2)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_20])).

fof(c_0_48,plain,(
    ! [X36,X37] :
      ( ( v1_funct_1(k7_tmap_1(X36,X37))
        | v2_struct_0(X36)
        | ~ v2_pre_topc(X36)
        | ~ l1_pre_topc(X36)
        | ~ m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X36))) )
      & ( v1_funct_2(k7_tmap_1(X36,X37),u1_struct_0(X36),u1_struct_0(k6_tmap_1(X36,X37)))
        | v2_struct_0(X36)
        | ~ v2_pre_topc(X36)
        | ~ l1_pre_topc(X36)
        | ~ m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X36))) )
      & ( m1_subset_1(k7_tmap_1(X36,X37),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X36),u1_struct_0(k6_tmap_1(X36,X37)))))
        | v2_struct_0(X36)
        | ~ v2_pre_topc(X36)
        | ~ l1_pre_topc(X36)
        | ~ m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X36))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k7_tmap_1])])])])).

cnf(c_0_49,negated_conjecture,
    ( esk1_3(esk4_0,esk5_0,X1) = u1_struct_0(esk5_0)
    | X1 = k8_tmap_1(esk4_0,esk5_0)
    | ~ v1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_24]),c_0_25]),c_0_26])]),c_0_27])).

cnf(c_0_50,negated_conjecture,
    ( v1_pre_topc(k6_tmap_1(esk4_0,u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_42]),c_0_25]),c_0_26])]),c_0_27])).

cnf(c_0_51,negated_conjecture,
    ( v2_pre_topc(k6_tmap_1(esk4_0,u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_42]),c_0_25]),c_0_26])]),c_0_27])).

cnf(c_0_52,negated_conjecture,
    ( l1_pre_topc(k6_tmap_1(esk4_0,u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_25]),c_0_26])]),c_0_27])).

fof(c_0_53,plain,(
    ! [X44,X45] :
      ( ( v1_funct_1(k7_tmap_1(X44,X45))
        | ~ v3_pre_topc(X45,X44)
        | ~ m1_subset_1(X45,k1_zfmisc_1(u1_struct_0(X44)))
        | v2_struct_0(X44)
        | ~ v2_pre_topc(X44)
        | ~ l1_pre_topc(X44) )
      & ( v1_funct_2(k7_tmap_1(X44,X45),u1_struct_0(X44),u1_struct_0(k6_tmap_1(X44,X45)))
        | ~ v3_pre_topc(X45,X44)
        | ~ m1_subset_1(X45,k1_zfmisc_1(u1_struct_0(X44)))
        | v2_struct_0(X44)
        | ~ v2_pre_topc(X44)
        | ~ l1_pre_topc(X44) )
      & ( v5_pre_topc(k7_tmap_1(X44,X45),X44,k6_tmap_1(X44,X45))
        | ~ v3_pre_topc(X45,X44)
        | ~ m1_subset_1(X45,k1_zfmisc_1(u1_struct_0(X44)))
        | v2_struct_0(X44)
        | ~ v2_pre_topc(X44)
        | ~ l1_pre_topc(X44) )
      & ( m1_subset_1(k7_tmap_1(X44,X45),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X44),u1_struct_0(k6_tmap_1(X44,X45)))))
        | ~ v3_pre_topc(X45,X44)
        | ~ m1_subset_1(X45,k1_zfmisc_1(u1_struct_0(X44)))
        | v2_struct_0(X44)
        | ~ v2_pre_topc(X44)
        | ~ l1_pre_topc(X44) )
      & ( ~ v1_funct_1(k7_tmap_1(X44,X45))
        | ~ v1_funct_2(k7_tmap_1(X44,X45),u1_struct_0(X44),u1_struct_0(k6_tmap_1(X44,X45)))
        | ~ v5_pre_topc(k7_tmap_1(X44,X45),X44,k6_tmap_1(X44,X45))
        | ~ m1_subset_1(k7_tmap_1(X44,X45),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X44),u1_struct_0(k6_tmap_1(X44,X45)))))
        | v3_pre_topc(X45,X44)
        | ~ m1_subset_1(X45,k1_zfmisc_1(u1_struct_0(X44)))
        | v2_struct_0(X44)
        | ~ v2_pre_topc(X44)
        | ~ l1_pre_topc(X44) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t113_tmap_1])])])])])).

cnf(c_0_54,negated_conjecture,
    ( v1_tsep_1(esk5_0,esk4_0)
    | m1_subset_1(esk3_2(esk4_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_24]),c_0_26])])).

cnf(c_0_55,negated_conjecture,
    ( k6_partfun1(u1_struct_0(esk4_0)) = k7_tmap_1(esk4_0,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_24]),c_0_25]),c_0_26])]),c_0_27])).

cnf(c_0_56,negated_conjecture,
    ( v1_pre_topc(k6_tmap_1(esk4_0,u1_struct_0(esk5_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_24]),c_0_25]),c_0_26])]),c_0_27])).

cnf(c_0_57,negated_conjecture,
    ( v2_pre_topc(k6_tmap_1(esk4_0,u1_struct_0(esk5_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_24]),c_0_25]),c_0_26])]),c_0_27])).

cnf(c_0_58,plain,
    ( v1_funct_1(k7_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

fof(c_0_59,plain,(
    ! [X40,X41] :
      ( ( ~ v2_struct_0(k6_tmap_1(X40,X41))
        | v2_struct_0(X40)
        | ~ v2_pre_topc(X40)
        | ~ l1_pre_topc(X40)
        | ~ m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(X40))) )
      & ( v1_pre_topc(k6_tmap_1(X40,X41))
        | v2_struct_0(X40)
        | ~ v2_pre_topc(X40)
        | ~ l1_pre_topc(X40)
        | ~ m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(X40))) )
      & ( v2_pre_topc(k6_tmap_1(X40,X41))
        | v2_struct_0(X40)
        | ~ v2_pre_topc(X40)
        | ~ l1_pre_topc(X40)
        | ~ m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(X40))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc4_tmap_1])])])])).

cnf(c_0_60,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | X3 = k8_tmap_1(X1,X2)
    | v2_struct_0(X1)
    | ~ v1_pre_topc(X3)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_61,negated_conjecture,
    ( esk1_3(esk4_0,esk5_0,k6_tmap_1(esk4_0,u1_struct_0(esk4_0))) = u1_struct_0(esk5_0)
    | k6_tmap_1(esk4_0,u1_struct_0(esk4_0)) = k8_tmap_1(esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_51]),c_0_52])])).

cnf(c_0_62,plain,
    ( esk1_3(X1,X1,X2) = u1_struct_0(X1)
    | X2 = k8_tmap_1(X1,X1)
    | v2_struct_0(X1)
    | ~ v1_pre_topc(X2)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_35])).

cnf(c_0_63,plain,
    ( v3_pre_topc(X2,X1)
    | v2_struct_0(X1)
    | ~ v1_funct_1(k7_tmap_1(X1,X2))
    | ~ v1_funct_2(k7_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))
    | ~ v5_pre_topc(k7_tmap_1(X1,X2),X1,k6_tmap_1(X1,X2))
    | ~ m1_subset_1(k7_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_64,plain,
    ( m1_subset_1(k7_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_65,plain,
    ( v1_funct_2(k7_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_66,negated_conjecture,
    ( k7_tmap_1(esk4_0,esk3_2(esk4_0,esk5_0)) = k7_tmap_1(esk4_0,u1_struct_0(esk5_0))
    | v1_tsep_1(esk5_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_54]),c_0_55]),c_0_25]),c_0_26])]),c_0_27])).

cnf(c_0_67,negated_conjecture,
    ( k7_tmap_1(esk4_0,u1_struct_0(esk5_0)) = k7_tmap_1(esk4_0,u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_42]),c_0_55]),c_0_25]),c_0_26])]),c_0_27])).

cnf(c_0_68,plain,
    ( X1 = k8_tmap_1(X2,X3)
    | v2_struct_0(X2)
    | X1 != k6_tmap_1(X2,esk1_3(X2,X3,X1))
    | ~ v1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X3,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_69,negated_conjecture,
    ( esk1_3(esk4_0,esk5_0,k6_tmap_1(esk4_0,u1_struct_0(esk5_0))) = u1_struct_0(esk5_0)
    | k6_tmap_1(esk4_0,u1_struct_0(esk5_0)) = k8_tmap_1(esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_56]),c_0_57]),c_0_36])])).

cnf(c_0_70,plain,
    ( v1_funct_1(k7_tmap_1(X1,u1_struct_0(X2)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_58,c_0_20])).

fof(c_0_71,plain,(
    ! [X8] :
      ( v2_struct_0(X8)
      | ~ l1_struct_0(X8)
      | ~ v1_xboole_0(u1_struct_0(X8)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

fof(c_0_72,plain,(
    ! [X7] :
      ( ~ l1_pre_topc(X7)
      | l1_struct_0(X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_73,plain,
    ( v2_struct_0(X1)
    | ~ v2_struct_0(k6_tmap_1(X1,X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_74,negated_conjecture,
    ( k6_tmap_1(esk4_0,u1_struct_0(esk4_0)) = k8_tmap_1(esk4_0,esk5_0)
    | m1_subset_1(u1_struct_0(esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_50]),c_0_51]),c_0_25]),c_0_24]),c_0_52]),c_0_26])]),c_0_27])).

cnf(c_0_75,negated_conjecture,
    ( esk1_3(X1,X1,k6_tmap_1(esk4_0,u1_struct_0(esk4_0))) = u1_struct_0(X1)
    | k6_tmap_1(esk4_0,u1_struct_0(esk4_0)) = k8_tmap_1(X1,X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_50]),c_0_51]),c_0_52])])).

cnf(c_0_76,plain,
    ( v3_pre_topc(X1,X2)
    | v2_struct_0(X2)
    | ~ v5_pre_topc(k7_tmap_1(X2,X1),X2,k6_tmap_1(X2,X1))
    | ~ v2_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[c_0_63,c_0_64]),c_0_58]),c_0_65])).

cnf(c_0_77,negated_conjecture,
    ( k7_tmap_1(esk4_0,esk3_2(esk4_0,esk5_0)) = k7_tmap_1(esk4_0,u1_struct_0(esk4_0))
    | v1_tsep_1(esk5_0,esk4_0) ),
    inference(rw,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_78,negated_conjecture,
    ( k6_partfun1(u1_struct_0(esk4_0)) = k7_tmap_1(esk4_0,u1_struct_0(esk4_0)) ),
    inference(rw,[status(thm)],[c_0_55,c_0_67])).

cnf(c_0_79,plain,
    ( esk3_2(X1,X2) = u1_struct_0(X2)
    | v1_tsep_1(X2,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

fof(c_0_80,plain,(
    ! [X25,X26,X27,X28] :
      ( ( X27 != k9_tmap_1(X25,X26)
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X25)))
        | X28 != u1_struct_0(X26)
        | r1_funct_2(u1_struct_0(X25),u1_struct_0(k8_tmap_1(X25,X26)),u1_struct_0(X25),u1_struct_0(k6_tmap_1(X25,X28)),X27,k7_tmap_1(X25,X28))
        | ~ v1_funct_1(X27)
        | ~ v1_funct_2(X27,u1_struct_0(X25),u1_struct_0(k8_tmap_1(X25,X26)))
        | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X25),u1_struct_0(k8_tmap_1(X25,X26)))))
        | ~ m1_pre_topc(X26,X25)
        | v2_struct_0(X25)
        | ~ v2_pre_topc(X25)
        | ~ l1_pre_topc(X25) )
      & ( m1_subset_1(esk2_3(X25,X26,X27),k1_zfmisc_1(u1_struct_0(X25)))
        | X27 = k9_tmap_1(X25,X26)
        | ~ v1_funct_1(X27)
        | ~ v1_funct_2(X27,u1_struct_0(X25),u1_struct_0(k8_tmap_1(X25,X26)))
        | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X25),u1_struct_0(k8_tmap_1(X25,X26)))))
        | ~ m1_pre_topc(X26,X25)
        | v2_struct_0(X25)
        | ~ v2_pre_topc(X25)
        | ~ l1_pre_topc(X25) )
      & ( esk2_3(X25,X26,X27) = u1_struct_0(X26)
        | X27 = k9_tmap_1(X25,X26)
        | ~ v1_funct_1(X27)
        | ~ v1_funct_2(X27,u1_struct_0(X25),u1_struct_0(k8_tmap_1(X25,X26)))
        | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X25),u1_struct_0(k8_tmap_1(X25,X26)))))
        | ~ m1_pre_topc(X26,X25)
        | v2_struct_0(X25)
        | ~ v2_pre_topc(X25)
        | ~ l1_pre_topc(X25) )
      & ( ~ r1_funct_2(u1_struct_0(X25),u1_struct_0(k8_tmap_1(X25,X26)),u1_struct_0(X25),u1_struct_0(k6_tmap_1(X25,esk2_3(X25,X26,X27))),X27,k7_tmap_1(X25,esk2_3(X25,X26,X27)))
        | X27 = k9_tmap_1(X25,X26)
        | ~ v1_funct_1(X27)
        | ~ v1_funct_2(X27,u1_struct_0(X25),u1_struct_0(k8_tmap_1(X25,X26)))
        | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X25),u1_struct_0(k8_tmap_1(X25,X26)))))
        | ~ m1_pre_topc(X26,X25)
        | v2_struct_0(X25)
        | ~ v2_pre_topc(X25)
        | ~ l1_pre_topc(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d12_tmap_1])])])])])])).

cnf(c_0_81,negated_conjecture,
    ( k6_tmap_1(esk4_0,u1_struct_0(esk5_0)) = k8_tmap_1(esk4_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_56]),c_0_25]),c_0_57]),c_0_24]),c_0_26]),c_0_36])]),c_0_27])).

fof(c_0_82,plain,(
    ! [X12,X13,X14,X15,X16,X17] :
      ( v1_xboole_0(X13)
      | v1_xboole_0(X15)
      | ~ v1_funct_1(X16)
      | ~ v1_funct_2(X16,X12,X13)
      | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X12,X13)))
      | ~ v1_funct_1(X17)
      | ~ v1_funct_2(X17,X14,X15)
      | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X14,X15)))
      | r1_funct_2(X12,X13,X14,X15,X16,X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[reflexivity_r1_funct_2])])])).

cnf(c_0_83,negated_conjecture,
    ( u1_struct_0(k6_tmap_1(esk4_0,u1_struct_0(esk4_0))) = u1_struct_0(esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_42]),c_0_25]),c_0_26])]),c_0_27])).

cnf(c_0_84,plain,
    ( v1_funct_1(k7_tmap_1(X1,u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_70,c_0_35])).

cnf(c_0_85,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_86,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_87,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ v2_struct_0(k8_tmap_1(esk4_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_25]),c_0_42]),c_0_26])]),c_0_27])).

cnf(c_0_88,negated_conjecture,
    ( esk1_3(esk4_0,esk4_0,k6_tmap_1(esk4_0,u1_struct_0(esk4_0))) = u1_struct_0(esk4_0)
    | k6_tmap_1(esk4_0,u1_struct_0(esk4_0)) = k8_tmap_1(esk4_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_25]),c_0_26])]),c_0_27])).

cnf(c_0_89,negated_conjecture,
    ( v3_pre_topc(esk3_2(esk4_0,esk5_0),esk4_0)
    | v1_tsep_1(esk5_0,esk4_0)
    | ~ v5_pre_topc(k7_tmap_1(esk4_0,u1_struct_0(esk4_0)),esk4_0,k6_tmap_1(esk4_0,esk3_2(esk4_0,esk5_0))) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_25]),c_0_26])]),c_0_27]),c_0_54])).

cnf(c_0_90,negated_conjecture,
    ( k7_tmap_1(esk4_0,u1_struct_0(X1)) = k7_tmap_1(esk4_0,u1_struct_0(esk4_0))
    | ~ m1_pre_topc(X1,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_78]),c_0_25]),c_0_26])]),c_0_27])).

cnf(c_0_91,plain,
    ( v1_tsep_1(X2,X1)
    | ~ v3_pre_topc(esk3_2(X1,X2),X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_92,negated_conjecture,
    ( esk3_2(esk4_0,esk5_0) = u1_struct_0(esk5_0)
    | v1_tsep_1(esk5_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_24]),c_0_26])])).

cnf(c_0_93,plain,
    ( esk2_3(X1,X2,X3) = u1_struct_0(X2)
    | X3 = k9_tmap_1(X1,X2)
    | v2_struct_0(X1)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_80])).

cnf(c_0_94,negated_conjecture,
    ( u1_struct_0(k8_tmap_1(esk4_0,esk5_0)) = u1_struct_0(esk4_0) ),
    inference(rw,[status(thm)],[c_0_29,c_0_81])).

cnf(c_0_95,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | r1_funct_2(X4,X1,X6,X2,X3,X3)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X4,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,X6,X2)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X6,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_82])).

cnf(c_0_96,negated_conjecture,
    ( m1_subset_1(k7_tmap_1(esk4_0,u1_struct_0(esk4_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk4_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_83]),c_0_25]),c_0_42]),c_0_26])]),c_0_27])).

cnf(c_0_97,negated_conjecture,
    ( v1_funct_2(k7_tmap_1(esk4_0,u1_struct_0(esk4_0)),u1_struct_0(esk4_0),u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_83]),c_0_25]),c_0_42]),c_0_26])]),c_0_27])).

cnf(c_0_98,negated_conjecture,
    ( v1_funct_1(k7_tmap_1(esk4_0,u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_25]),c_0_26])]),c_0_27])).

cnf(c_0_99,plain,
    ( v2_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_85,c_0_86])).

cnf(c_0_100,negated_conjecture,
    ( l1_pre_topc(k8_tmap_1(esk4_0,esk5_0)) ),
    inference(rw,[status(thm)],[c_0_36,c_0_81])).

cnf(c_0_101,negated_conjecture,
    ( ~ v2_struct_0(k8_tmap_1(esk4_0,esk5_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_81]),c_0_25]),c_0_26])]),c_0_27]),c_0_87])).

fof(c_0_102,plain,(
    ! [X38,X39] :
      ( ( v1_funct_1(k9_tmap_1(X38,X39))
        | v2_struct_0(X38)
        | ~ v2_pre_topc(X38)
        | ~ l1_pre_topc(X38)
        | ~ m1_pre_topc(X39,X38) )
      & ( v1_funct_2(k9_tmap_1(X38,X39),u1_struct_0(X38),u1_struct_0(k8_tmap_1(X38,X39)))
        | v2_struct_0(X38)
        | ~ v2_pre_topc(X38)
        | ~ l1_pre_topc(X38)
        | ~ m1_pre_topc(X39,X38) )
      & ( m1_subset_1(k9_tmap_1(X38,X39),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X38),u1_struct_0(k8_tmap_1(X38,X39)))))
        | v2_struct_0(X38)
        | ~ v2_pre_topc(X38)
        | ~ l1_pre_topc(X38)
        | ~ m1_pre_topc(X39,X38) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k9_tmap_1])])])])).

cnf(c_0_103,negated_conjecture,
    ( k6_tmap_1(esk4_0,u1_struct_0(esk4_0)) = k8_tmap_1(esk4_0,esk4_0)
    | ~ m1_pre_topc(esk4_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_88]),c_0_50]),c_0_25]),c_0_51]),c_0_26]),c_0_52])]),c_0_27])).

cnf(c_0_104,negated_conjecture,
    ( v3_pre_topc(esk3_2(esk4_0,esk5_0),esk4_0)
    | v1_tsep_1(esk5_0,esk4_0)
    | ~ v5_pre_topc(k7_tmap_1(esk4_0,u1_struct_0(X1)),esk4_0,k6_tmap_1(esk4_0,esk3_2(esk4_0,esk5_0)))
    | ~ m1_pre_topc(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_89,c_0_90])).

cnf(c_0_105,negated_conjecture,
    ( v1_tsep_1(esk5_0,esk4_0)
    | ~ v3_pre_topc(u1_struct_0(esk5_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_92]),c_0_24]),c_0_26])])).

cnf(c_0_106,negated_conjecture,
    ( esk2_3(esk4_0,esk5_0,X1) = u1_struct_0(esk5_0)
    | X1 = k9_tmap_1(esk4_0,esk5_0)
    | ~ v1_funct_2(X1,u1_struct_0(esk4_0),u1_struct_0(esk4_0))
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk4_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_94]),c_0_25]),c_0_24]),c_0_26])]),c_0_27])).

cnf(c_0_107,negated_conjecture,
    ( r1_funct_2(X1,X2,u1_struct_0(esk4_0),u1_struct_0(esk4_0),X3,X3)
    | v1_xboole_0(u1_struct_0(esk4_0))
    | v1_xboole_0(X2)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_96]),c_0_97]),c_0_98])])).

cnf(c_0_108,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_94]),c_0_100])]),c_0_101])).

cnf(c_0_109,negated_conjecture,
    ( ~ v1_tsep_1(esk5_0,esk4_0)
    | ~ m1_pre_topc(esk5_0,esk4_0)
    | ~ v1_funct_1(k9_tmap_1(esk4_0,esk5_0))
    | ~ v1_funct_2(k9_tmap_1(esk4_0,esk5_0),u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk4_0,esk5_0)))
    | ~ v5_pre_topc(k9_tmap_1(esk4_0,esk5_0),esk4_0,k8_tmap_1(esk4_0,esk5_0))
    | ~ m1_subset_1(k9_tmap_1(esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk4_0,esk5_0))))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_110,plain,
    ( v1_funct_1(k9_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_102])).

cnf(c_0_111,negated_conjecture,
    ( k8_tmap_1(esk4_0,esk5_0) = k8_tmap_1(esk4_0,esk4_0)
    | m1_subset_1(u1_struct_0(esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ m1_pre_topc(esk4_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_74,c_0_103])).

cnf(c_0_112,negated_conjecture,
    ( v1_tsep_1(esk5_0,esk4_0)
    | ~ v5_pre_topc(k7_tmap_1(esk4_0,u1_struct_0(X1)),esk4_0,k8_tmap_1(esk4_0,esk5_0))
    | ~ m1_pre_topc(X1,esk4_0) ),
    inference(csr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_92]),c_0_81]),c_0_105])).

cnf(c_0_113,plain,
    ( X3 = k9_tmap_1(X1,X2)
    | v2_struct_0(X1)
    | ~ r1_funct_2(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,esk2_3(X1,X2,X3))),X3,k7_tmap_1(X1,esk2_3(X1,X2,X3)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_80])).

cnf(c_0_114,negated_conjecture,
    ( esk2_3(esk4_0,esk5_0,k7_tmap_1(esk4_0,u1_struct_0(esk4_0))) = u1_struct_0(esk5_0)
    | k7_tmap_1(esk4_0,u1_struct_0(esk4_0)) = k9_tmap_1(esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_96]),c_0_97]),c_0_98])])).

cnf(c_0_115,negated_conjecture,
    ( r1_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk4_0),k7_tmap_1(esk4_0,u1_struct_0(esk4_0)),k7_tmap_1(esk4_0,u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_96]),c_0_97]),c_0_98])]),c_0_108])).

cnf(c_0_116,negated_conjecture,
    ( ~ v5_pre_topc(k9_tmap_1(esk4_0,esk5_0),esk4_0,k8_tmap_1(esk4_0,esk5_0))
    | ~ v1_tsep_1(esk5_0,esk4_0)
    | ~ v1_funct_2(k9_tmap_1(esk4_0,esk5_0),u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk4_0,esk5_0)))
    | ~ v1_funct_1(k9_tmap_1(esk4_0,esk5_0))
    | ~ m1_subset_1(k9_tmap_1(esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk4_0,esk5_0))))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_109,c_0_24])])).

cnf(c_0_117,negated_conjecture,
    ( v1_funct_1(k9_tmap_1(esk4_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110,c_0_24]),c_0_25]),c_0_26])]),c_0_27])).

cnf(c_0_118,plain,
    ( v1_funct_2(k9_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_102])).

cnf(c_0_119,plain,
    ( m1_subset_1(k9_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_102])).

cnf(c_0_120,plain,
    ( v3_pre_topc(X3,X2)
    | ~ v1_tsep_1(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | X3 != u1_struct_0(X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_121,negated_conjecture,
    ( k8_tmap_1(esk4_0,esk5_0) = k8_tmap_1(esk4_0,esk4_0)
    | m1_subset_1(u1_struct_0(esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111,c_0_35]),c_0_26])])).

cnf(c_0_122,negated_conjecture,
    ( v1_tsep_1(esk5_0,esk4_0)
    | ~ v5_pre_topc(k7_tmap_1(esk4_0,u1_struct_0(esk4_0)),esk4_0,k8_tmap_1(esk4_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112,c_0_67]),c_0_24])])).

cnf(c_0_123,negated_conjecture,
    ( k7_tmap_1(esk4_0,u1_struct_0(esk4_0)) = k9_tmap_1(esk4_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113,c_0_114]),c_0_25]),c_0_94]),c_0_81]),c_0_94]),c_0_67]),c_0_115]),c_0_94]),c_0_97]),c_0_98]),c_0_94]),c_0_96]),c_0_24]),c_0_26])]),c_0_27])).

cnf(c_0_124,negated_conjecture,
    ( v5_pre_topc(k9_tmap_1(esk4_0,esk5_0),esk4_0,k8_tmap_1(esk4_0,esk5_0))
    | v1_tsep_1(esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_125,negated_conjecture,
    ( ~ v5_pre_topc(k9_tmap_1(esk4_0,esk5_0),esk4_0,k8_tmap_1(esk4_0,esk5_0))
    | ~ v1_tsep_1(esk5_0,esk4_0)
    | ~ v1_funct_2(k9_tmap_1(esk4_0,esk5_0),u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk4_0,esk5_0)))
    | ~ m1_subset_1(k9_tmap_1(esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk4_0,esk5_0))))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_116,c_0_117])])).

cnf(c_0_126,negated_conjecture,
    ( v1_funct_2(k9_tmap_1(esk4_0,esk5_0),u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk4_0,esk5_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_118,c_0_24]),c_0_25]),c_0_26])]),c_0_27])).

cnf(c_0_127,negated_conjecture,
    ( m1_subset_1(k9_tmap_1(esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk4_0,esk5_0))))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119,c_0_24]),c_0_25]),c_0_26])]),c_0_27])).

cnf(c_0_128,plain,
    ( v5_pre_topc(k7_tmap_1(X1,X2),X1,k6_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v3_pre_topc(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_129,negated_conjecture,
    ( k8_tmap_1(esk4_0,esk5_0) = k8_tmap_1(esk4_0,esk4_0)
    | v3_pre_topc(u1_struct_0(esk5_0),esk4_0)
    | u1_struct_0(esk5_0) != u1_struct_0(X1)
    | ~ v1_tsep_1(X1,esk4_0)
    | ~ m1_pre_topc(X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120,c_0_121]),c_0_26])])).

cnf(c_0_130,negated_conjecture,
    ( v1_tsep_1(esk5_0,esk4_0) ),
    inference(csr,[status(thm)],[inference(rw,[status(thm)],[c_0_122,c_0_123]),c_0_124])).

cnf(c_0_131,negated_conjecture,
    ( ~ v5_pre_topc(k9_tmap_1(esk4_0,esk5_0),esk4_0,k8_tmap_1(esk4_0,esk5_0))
    | ~ v1_tsep_1(esk5_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_125,c_0_126])]),c_0_127])])).

cnf(c_0_132,plain,
    ( v5_pre_topc(k7_tmap_1(X1,u1_struct_0(X2)),X1,k6_tmap_1(X1,u1_struct_0(X2)))
    | v2_struct_0(X1)
    | ~ v3_pre_topc(u1_struct_0(X2),X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_128,c_0_20])).

cnf(c_0_133,negated_conjecture,
    ( k8_tmap_1(esk4_0,esk5_0) = k8_tmap_1(esk4_0,esk4_0)
    | v3_pre_topc(u1_struct_0(esk5_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_129,c_0_130]),c_0_24])])).

cnf(c_0_134,negated_conjecture,
    ( ~ v5_pre_topc(k9_tmap_1(esk4_0,esk5_0),esk4_0,k8_tmap_1(esk4_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_131,c_0_130])])).

cnf(c_0_135,plain,
    ( v3_pre_topc(u1_struct_0(X1),X2)
    | u1_struct_0(X1) != u1_struct_0(X3)
    | ~ v1_tsep_1(X3,X2)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_120,c_0_20])).

cnf(c_0_136,negated_conjecture,
    ( v1_tsep_1(esk5_0,esk4_0)
    | m1_subset_1(u1_struct_0(esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_92]),c_0_24]),c_0_26])])).

cnf(c_0_137,negated_conjecture,
    ( k8_tmap_1(esk4_0,esk5_0) = k8_tmap_1(esk4_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_132,c_0_133]),c_0_67]),c_0_123]),c_0_81]),c_0_25]),c_0_24]),c_0_26])]),c_0_134]),c_0_27])).

cnf(c_0_138,negated_conjecture,
    ( v3_pre_topc(u1_struct_0(X1),esk4_0)
    | m1_subset_1(u1_struct_0(esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0)))
    | u1_struct_0(X1) != u1_struct_0(esk5_0)
    | ~ m1_pre_topc(X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_135,c_0_136]),c_0_24]),c_0_26])])).

cnf(c_0_139,negated_conjecture,
    ( k7_tmap_1(esk4_0,u1_struct_0(esk5_0)) = k9_tmap_1(esk4_0,esk5_0) ),
    inference(rw,[status(thm)],[c_0_67,c_0_123])).

cnf(c_0_140,negated_conjecture,
    ( ~ v5_pre_topc(k9_tmap_1(esk4_0,esk5_0),esk4_0,k8_tmap_1(esk4_0,esk4_0)) ),
    inference(rw,[status(thm)],[c_0_134,c_0_137])).

cnf(c_0_141,negated_conjecture,
    ( v3_pre_topc(u1_struct_0(esk5_0),esk4_0)
    | m1_subset_1(u1_struct_0(esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_138,c_0_24])).

cnf(c_0_142,negated_conjecture,
    ( ~ v3_pre_topc(u1_struct_0(esk5_0),esk4_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_132,c_0_139]),c_0_81]),c_0_137]),c_0_25]),c_0_24]),c_0_26])]),c_0_140]),c_0_27])).

cnf(c_0_143,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[c_0_141,c_0_142])).

cnf(c_0_144,negated_conjecture,
    ( u1_struct_0(esk5_0) != u1_struct_0(X1)
    | ~ v1_tsep_1(X1,esk4_0)
    | ~ m1_pre_topc(X1,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120,c_0_143]),c_0_26])]),c_0_142])).

cnf(c_0_145,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_144,c_0_130]),c_0_24])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 09:49:19 EST 2020
% 0.19/0.33  % CPUTime    : 
% 0.19/0.33  # Version: 2.5pre002
% 0.19/0.33  # No SInE strategy applied
% 0.19/0.33  # Trying AutoSched0 for 299 seconds
% 1.75/1.94  # AutoSched0-Mode selected heuristic G_E___302_C18_F1_URBAN_RG_S04BN
% 1.75/1.94  # and selection function PSelectComplexExceptUniqMaxHorn.
% 1.75/1.94  #
% 1.75/1.94  # Preprocessing time       : 0.043 s
% 1.75/1.94  
% 1.75/1.94  # Proof found!
% 1.75/1.94  # SZS status Theorem
% 1.75/1.94  # SZS output start CNFRefutation
% 1.75/1.94  fof(t104_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(u1_struct_0(k6_tmap_1(X1,X2))=u1_struct_0(X1)&u1_pre_topc(k6_tmap_1(X1,X2))=k5_tmap_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t104_tmap_1)).
% 1.75/1.94  fof(t1_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 1.75/1.94  fof(t122_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>((v1_tsep_1(X2,X1)&m1_pre_topc(X2,X1))<=>(((v1_funct_1(k9_tmap_1(X1,X2))&v1_funct_2(k9_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2))))&v5_pre_topc(k9_tmap_1(X1,X2),X1,k8_tmap_1(X1,X2)))&m1_subset_1(k9_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t122_tmap_1)).
% 1.75/1.94  fof(dt_k6_tmap_1, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>((v1_pre_topc(k6_tmap_1(X1,X2))&v2_pre_topc(k6_tmap_1(X1,X2)))&l1_pre_topc(k6_tmap_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_tmap_1)).
% 1.75/1.94  fof(t2_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>m1_pre_topc(X1,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tsep_1)).
% 1.75/1.94  fof(d10_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k7_tmap_1(X1,X2)=k6_partfun1(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_tmap_1)).
% 1.75/1.94  fof(d11_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(((v1_pre_topc(X3)&v2_pre_topc(X3))&l1_pre_topc(X3))=>(X3=k8_tmap_1(X1,X2)<=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>(X4=u1_struct_0(X2)=>X3=k6_tmap_1(X1,X4))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d11_tmap_1)).
% 1.75/1.94  fof(d1_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>(v1_tsep_1(X2,X1)<=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(X3=u1_struct_0(X2)=>v3_pre_topc(X3,X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tsep_1)).
% 1.75/1.94  fof(dt_k7_tmap_1, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>((v1_funct_1(k7_tmap_1(X1,X2))&v1_funct_2(k7_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2))))&m1_subset_1(k7_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_tmap_1)).
% 1.75/1.94  fof(t113_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>(((v1_funct_1(k7_tmap_1(X1,X2))&v1_funct_2(k7_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2))))&v5_pre_topc(k7_tmap_1(X1,X2),X1,k6_tmap_1(X1,X2)))&m1_subset_1(k7_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_tmap_1)).
% 1.75/1.94  fof(fc4_tmap_1, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>((~(v2_struct_0(k6_tmap_1(X1,X2)))&v1_pre_topc(k6_tmap_1(X1,X2)))&v2_pre_topc(k6_tmap_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_tmap_1)).
% 1.75/1.94  fof(fc2_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>~(v1_xboole_0(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 1.75/1.94  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 1.75/1.94  fof(d12_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2))))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2))))))=>(X3=k9_tmap_1(X1,X2)<=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>(X4=u1_struct_0(X2)=>r1_funct_2(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X4)),X3,k7_tmap_1(X1,X4)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_tmap_1)).
% 1.75/1.94  fof(reflexivity_r1_funct_2, axiom, ![X1, X2, X3, X4, X5, X6]:((((((((~(v1_xboole_0(X2))&~(v1_xboole_0(X4)))&v1_funct_1(X5))&v1_funct_2(X5,X1,X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X6))&v1_funct_2(X6,X3,X4))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=>r1_funct_2(X1,X2,X3,X4,X5,X5)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r1_funct_2)).
% 1.75/1.94  fof(dt_k9_tmap_1, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_pre_topc(X2,X1))=>((v1_funct_1(k9_tmap_1(X1,X2))&v1_funct_2(k9_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2))))&m1_subset_1(k9_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k9_tmap_1)).
% 1.75/1.94  fof(c_0_16, plain, ![X42, X43]:((u1_struct_0(k6_tmap_1(X42,X43))=u1_struct_0(X42)|~m1_subset_1(X43,k1_zfmisc_1(u1_struct_0(X42)))|(v2_struct_0(X42)|~v2_pre_topc(X42)|~l1_pre_topc(X42)))&(u1_pre_topc(k6_tmap_1(X42,X43))=k5_tmap_1(X42,X43)|~m1_subset_1(X43,k1_zfmisc_1(u1_struct_0(X42)))|(v2_struct_0(X42)|~v2_pre_topc(X42)|~l1_pre_topc(X42)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t104_tmap_1])])])])])).
% 1.75/1.94  fof(c_0_17, plain, ![X46, X47]:(~l1_pre_topc(X46)|(~m1_pre_topc(X47,X46)|m1_subset_1(u1_struct_0(X47),k1_zfmisc_1(u1_struct_0(X46))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).
% 1.75/1.94  fof(c_0_18, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>((v1_tsep_1(X2,X1)&m1_pre_topc(X2,X1))<=>(((v1_funct_1(k9_tmap_1(X1,X2))&v1_funct_2(k9_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2))))&v5_pre_topc(k9_tmap_1(X1,X2),X1,k8_tmap_1(X1,X2)))&m1_subset_1(k9_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))))))), inference(assume_negation,[status(cth)],[t122_tmap_1])).
% 1.75/1.94  cnf(c_0_19, plain, (u1_struct_0(k6_tmap_1(X1,X2))=u1_struct_0(X1)|v2_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 1.75/1.94  cnf(c_0_20, plain, (m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 1.75/1.94  fof(c_0_21, negated_conjecture, (((~v2_struct_0(esk4_0)&v2_pre_topc(esk4_0))&l1_pre_topc(esk4_0))&(m1_pre_topc(esk5_0,esk4_0)&((~v1_tsep_1(esk5_0,esk4_0)|~m1_pre_topc(esk5_0,esk4_0)|(~v1_funct_1(k9_tmap_1(esk4_0,esk5_0))|~v1_funct_2(k9_tmap_1(esk4_0,esk5_0),u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk4_0,esk5_0)))|~v5_pre_topc(k9_tmap_1(esk4_0,esk5_0),esk4_0,k8_tmap_1(esk4_0,esk5_0))|~m1_subset_1(k9_tmap_1(esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk4_0,esk5_0)))))))&(((((v1_funct_1(k9_tmap_1(esk4_0,esk5_0))|v1_tsep_1(esk5_0,esk4_0))&(v1_funct_2(k9_tmap_1(esk4_0,esk5_0),u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk4_0,esk5_0)))|v1_tsep_1(esk5_0,esk4_0)))&(v5_pre_topc(k9_tmap_1(esk4_0,esk5_0),esk4_0,k8_tmap_1(esk4_0,esk5_0))|v1_tsep_1(esk5_0,esk4_0)))&(m1_subset_1(k9_tmap_1(esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk4_0,esk5_0)))))|v1_tsep_1(esk5_0,esk4_0)))&((((v1_funct_1(k9_tmap_1(esk4_0,esk5_0))|m1_pre_topc(esk5_0,esk4_0))&(v1_funct_2(k9_tmap_1(esk4_0,esk5_0),u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk4_0,esk5_0)))|m1_pre_topc(esk5_0,esk4_0)))&(v5_pre_topc(k9_tmap_1(esk4_0,esk5_0),esk4_0,k8_tmap_1(esk4_0,esk5_0))|m1_pre_topc(esk5_0,esk4_0)))&(m1_subset_1(k9_tmap_1(esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk4_0,esk5_0)))))|m1_pre_topc(esk5_0,esk4_0))))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_18])])])])])).
% 1.75/1.94  fof(c_0_22, plain, ![X34, X35]:(((v1_pre_topc(k6_tmap_1(X34,X35))|(v2_struct_0(X34)|~v2_pre_topc(X34)|~l1_pre_topc(X34)|~m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X34)))))&(v2_pre_topc(k6_tmap_1(X34,X35))|(v2_struct_0(X34)|~v2_pre_topc(X34)|~l1_pre_topc(X34)|~m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X34))))))&(l1_pre_topc(k6_tmap_1(X34,X35))|(v2_struct_0(X34)|~v2_pre_topc(X34)|~l1_pre_topc(X34)|~m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X34)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_tmap_1])])])])).
% 1.75/1.94  cnf(c_0_23, plain, (u1_struct_0(k6_tmap_1(X1,u1_struct_0(X2)))=u1_struct_0(X1)|v2_struct_0(X1)|~v2_pre_topc(X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 1.75/1.94  cnf(c_0_24, negated_conjecture, (m1_pre_topc(esk5_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 1.75/1.94  cnf(c_0_25, negated_conjecture, (v2_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 1.75/1.94  cnf(c_0_26, negated_conjecture, (l1_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 1.75/1.94  cnf(c_0_27, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 1.75/1.94  cnf(c_0_28, plain, (l1_pre_topc(k6_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 1.75/1.94  cnf(c_0_29, negated_conjecture, (u1_struct_0(k6_tmap_1(esk4_0,u1_struct_0(esk5_0)))=u1_struct_0(esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_25]), c_0_26])]), c_0_27])).
% 1.75/1.94  fof(c_0_30, plain, ![X48]:(~l1_pre_topc(X48)|m1_pre_topc(X48,X48)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tsep_1])])).
% 1.75/1.94  cnf(c_0_31, plain, (v2_struct_0(X1)|l1_pre_topc(k6_tmap_1(X1,u1_struct_0(X2)))|~v2_pre_topc(X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_28, c_0_20])).
% 1.75/1.94  fof(c_0_32, plain, ![X18, X19]:(v2_struct_0(X18)|~v2_pre_topc(X18)|~l1_pre_topc(X18)|(~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))|k7_tmap_1(X18,X19)=k6_partfun1(u1_struct_0(X18)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d10_tmap_1])])])])).
% 1.75/1.94  fof(c_0_33, plain, ![X20, X21, X22, X23]:((X22!=k8_tmap_1(X20,X21)|(~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X20)))|(X23!=u1_struct_0(X21)|X22=k6_tmap_1(X20,X23)))|(~v1_pre_topc(X22)|~v2_pre_topc(X22)|~l1_pre_topc(X22))|~m1_pre_topc(X21,X20)|(v2_struct_0(X20)|~v2_pre_topc(X20)|~l1_pre_topc(X20)))&((m1_subset_1(esk1_3(X20,X21,X22),k1_zfmisc_1(u1_struct_0(X20)))|X22=k8_tmap_1(X20,X21)|(~v1_pre_topc(X22)|~v2_pre_topc(X22)|~l1_pre_topc(X22))|~m1_pre_topc(X21,X20)|(v2_struct_0(X20)|~v2_pre_topc(X20)|~l1_pre_topc(X20)))&((esk1_3(X20,X21,X22)=u1_struct_0(X21)|X22=k8_tmap_1(X20,X21)|(~v1_pre_topc(X22)|~v2_pre_topc(X22)|~l1_pre_topc(X22))|~m1_pre_topc(X21,X20)|(v2_struct_0(X20)|~v2_pre_topc(X20)|~l1_pre_topc(X20)))&(X22!=k6_tmap_1(X20,esk1_3(X20,X21,X22))|X22=k8_tmap_1(X20,X21)|(~v1_pre_topc(X22)|~v2_pre_topc(X22)|~l1_pre_topc(X22))|~m1_pre_topc(X21,X20)|(v2_struct_0(X20)|~v2_pre_topc(X20)|~l1_pre_topc(X20)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d11_tmap_1])])])])])])).
% 1.75/1.94  cnf(c_0_34, negated_conjecture, (m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(X1)))|~m1_pre_topc(k6_tmap_1(esk4_0,u1_struct_0(esk5_0)),X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_20, c_0_29])).
% 1.75/1.94  cnf(c_0_35, plain, (m1_pre_topc(X1,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 1.75/1.94  cnf(c_0_36, negated_conjecture, (l1_pre_topc(k6_tmap_1(esk4_0,u1_struct_0(esk5_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_24]), c_0_25]), c_0_26])]), c_0_27])).
% 1.75/1.94  fof(c_0_37, plain, ![X30, X31, X32]:((~v1_tsep_1(X31,X30)|(~m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X30)))|(X32!=u1_struct_0(X31)|v3_pre_topc(X32,X30)))|~m1_pre_topc(X31,X30)|~l1_pre_topc(X30))&((m1_subset_1(esk3_2(X30,X31),k1_zfmisc_1(u1_struct_0(X30)))|v1_tsep_1(X31,X30)|~m1_pre_topc(X31,X30)|~l1_pre_topc(X30))&((esk3_2(X30,X31)=u1_struct_0(X31)|v1_tsep_1(X31,X30)|~m1_pre_topc(X31,X30)|~l1_pre_topc(X30))&(~v3_pre_topc(esk3_2(X30,X31),X30)|v1_tsep_1(X31,X30)|~m1_pre_topc(X31,X30)|~l1_pre_topc(X30))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tsep_1])])])])])).
% 1.75/1.94  cnf(c_0_38, plain, (v2_struct_0(X1)|k7_tmap_1(X1,X2)=k6_partfun1(u1_struct_0(X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 1.75/1.94  cnf(c_0_39, plain, (v1_pre_topc(k6_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 1.75/1.94  cnf(c_0_40, plain, (v2_pre_topc(k6_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 1.75/1.94  cnf(c_0_41, plain, (esk1_3(X1,X2,X3)=u1_struct_0(X2)|X3=k8_tmap_1(X1,X2)|v2_struct_0(X1)|~v1_pre_topc(X3)|~v2_pre_topc(X3)|~l1_pre_topc(X3)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 1.75/1.94  cnf(c_0_42, negated_conjecture, (m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_29]), c_0_36])])).
% 1.75/1.94  cnf(c_0_43, plain, (v2_struct_0(X1)|l1_pre_topc(k6_tmap_1(X1,u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_31, c_0_35])).
% 1.75/1.94  cnf(c_0_44, plain, (m1_subset_1(esk3_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|v1_tsep_1(X2,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 1.75/1.94  cnf(c_0_45, plain, (k7_tmap_1(X1,u1_struct_0(X2))=k6_partfun1(u1_struct_0(X1))|v2_struct_0(X1)|~v2_pre_topc(X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_38, c_0_20])).
% 1.75/1.94  cnf(c_0_46, plain, (v1_pre_topc(k6_tmap_1(X1,u1_struct_0(X2)))|v2_struct_0(X1)|~v2_pre_topc(X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_39, c_0_20])).
% 1.75/1.94  cnf(c_0_47, plain, (v2_pre_topc(k6_tmap_1(X1,u1_struct_0(X2)))|v2_struct_0(X1)|~v2_pre_topc(X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_40, c_0_20])).
% 1.75/1.94  fof(c_0_48, plain, ![X36, X37]:(((v1_funct_1(k7_tmap_1(X36,X37))|(v2_struct_0(X36)|~v2_pre_topc(X36)|~l1_pre_topc(X36)|~m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X36)))))&(v1_funct_2(k7_tmap_1(X36,X37),u1_struct_0(X36),u1_struct_0(k6_tmap_1(X36,X37)))|(v2_struct_0(X36)|~v2_pre_topc(X36)|~l1_pre_topc(X36)|~m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X36))))))&(m1_subset_1(k7_tmap_1(X36,X37),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X36),u1_struct_0(k6_tmap_1(X36,X37)))))|(v2_struct_0(X36)|~v2_pre_topc(X36)|~l1_pre_topc(X36)|~m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X36)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k7_tmap_1])])])])).
% 1.75/1.94  cnf(c_0_49, negated_conjecture, (esk1_3(esk4_0,esk5_0,X1)=u1_struct_0(esk5_0)|X1=k8_tmap_1(esk4_0,esk5_0)|~v1_pre_topc(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_24]), c_0_25]), c_0_26])]), c_0_27])).
% 1.75/1.94  cnf(c_0_50, negated_conjecture, (v1_pre_topc(k6_tmap_1(esk4_0,u1_struct_0(esk4_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_42]), c_0_25]), c_0_26])]), c_0_27])).
% 1.75/1.94  cnf(c_0_51, negated_conjecture, (v2_pre_topc(k6_tmap_1(esk4_0,u1_struct_0(esk4_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_42]), c_0_25]), c_0_26])]), c_0_27])).
% 1.75/1.94  cnf(c_0_52, negated_conjecture, (l1_pre_topc(k6_tmap_1(esk4_0,u1_struct_0(esk4_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_25]), c_0_26])]), c_0_27])).
% 1.75/1.94  fof(c_0_53, plain, ![X44, X45]:(((((v1_funct_1(k7_tmap_1(X44,X45))|~v3_pre_topc(X45,X44)|~m1_subset_1(X45,k1_zfmisc_1(u1_struct_0(X44)))|(v2_struct_0(X44)|~v2_pre_topc(X44)|~l1_pre_topc(X44)))&(v1_funct_2(k7_tmap_1(X44,X45),u1_struct_0(X44),u1_struct_0(k6_tmap_1(X44,X45)))|~v3_pre_topc(X45,X44)|~m1_subset_1(X45,k1_zfmisc_1(u1_struct_0(X44)))|(v2_struct_0(X44)|~v2_pre_topc(X44)|~l1_pre_topc(X44))))&(v5_pre_topc(k7_tmap_1(X44,X45),X44,k6_tmap_1(X44,X45))|~v3_pre_topc(X45,X44)|~m1_subset_1(X45,k1_zfmisc_1(u1_struct_0(X44)))|(v2_struct_0(X44)|~v2_pre_topc(X44)|~l1_pre_topc(X44))))&(m1_subset_1(k7_tmap_1(X44,X45),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X44),u1_struct_0(k6_tmap_1(X44,X45)))))|~v3_pre_topc(X45,X44)|~m1_subset_1(X45,k1_zfmisc_1(u1_struct_0(X44)))|(v2_struct_0(X44)|~v2_pre_topc(X44)|~l1_pre_topc(X44))))&(~v1_funct_1(k7_tmap_1(X44,X45))|~v1_funct_2(k7_tmap_1(X44,X45),u1_struct_0(X44),u1_struct_0(k6_tmap_1(X44,X45)))|~v5_pre_topc(k7_tmap_1(X44,X45),X44,k6_tmap_1(X44,X45))|~m1_subset_1(k7_tmap_1(X44,X45),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X44),u1_struct_0(k6_tmap_1(X44,X45)))))|v3_pre_topc(X45,X44)|~m1_subset_1(X45,k1_zfmisc_1(u1_struct_0(X44)))|(v2_struct_0(X44)|~v2_pre_topc(X44)|~l1_pre_topc(X44)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t113_tmap_1])])])])])).
% 1.75/1.94  cnf(c_0_54, negated_conjecture, (v1_tsep_1(esk5_0,esk4_0)|m1_subset_1(esk3_2(esk4_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_24]), c_0_26])])).
% 1.75/1.94  cnf(c_0_55, negated_conjecture, (k6_partfun1(u1_struct_0(esk4_0))=k7_tmap_1(esk4_0,u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_24]), c_0_25]), c_0_26])]), c_0_27])).
% 1.75/1.94  cnf(c_0_56, negated_conjecture, (v1_pre_topc(k6_tmap_1(esk4_0,u1_struct_0(esk5_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_24]), c_0_25]), c_0_26])]), c_0_27])).
% 1.75/1.94  cnf(c_0_57, negated_conjecture, (v2_pre_topc(k6_tmap_1(esk4_0,u1_struct_0(esk5_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_24]), c_0_25]), c_0_26])]), c_0_27])).
% 1.75/1.94  cnf(c_0_58, plain, (v1_funct_1(k7_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_48])).
% 1.75/1.94  fof(c_0_59, plain, ![X40, X41]:(((~v2_struct_0(k6_tmap_1(X40,X41))|(v2_struct_0(X40)|~v2_pre_topc(X40)|~l1_pre_topc(X40)|~m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(X40)))))&(v1_pre_topc(k6_tmap_1(X40,X41))|(v2_struct_0(X40)|~v2_pre_topc(X40)|~l1_pre_topc(X40)|~m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(X40))))))&(v2_pre_topc(k6_tmap_1(X40,X41))|(v2_struct_0(X40)|~v2_pre_topc(X40)|~l1_pre_topc(X40)|~m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(X40)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc4_tmap_1])])])])).
% 1.75/1.94  cnf(c_0_60, plain, (m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))|X3=k8_tmap_1(X1,X2)|v2_struct_0(X1)|~v1_pre_topc(X3)|~v2_pre_topc(X3)|~l1_pre_topc(X3)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 1.75/1.94  cnf(c_0_61, negated_conjecture, (esk1_3(esk4_0,esk5_0,k6_tmap_1(esk4_0,u1_struct_0(esk4_0)))=u1_struct_0(esk5_0)|k6_tmap_1(esk4_0,u1_struct_0(esk4_0))=k8_tmap_1(esk4_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_51]), c_0_52])])).
% 1.75/1.94  cnf(c_0_62, plain, (esk1_3(X1,X1,X2)=u1_struct_0(X1)|X2=k8_tmap_1(X1,X1)|v2_struct_0(X1)|~v1_pre_topc(X2)|~v2_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_41, c_0_35])).
% 1.75/1.94  cnf(c_0_63, plain, (v3_pre_topc(X2,X1)|v2_struct_0(X1)|~v1_funct_1(k7_tmap_1(X1,X2))|~v1_funct_2(k7_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))|~v5_pre_topc(k7_tmap_1(X1,X2),X1,k6_tmap_1(X1,X2))|~m1_subset_1(k7_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 1.75/1.94  cnf(c_0_64, plain, (m1_subset_1(k7_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_48])).
% 1.75/1.94  cnf(c_0_65, plain, (v1_funct_2(k7_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_48])).
% 1.75/1.94  cnf(c_0_66, negated_conjecture, (k7_tmap_1(esk4_0,esk3_2(esk4_0,esk5_0))=k7_tmap_1(esk4_0,u1_struct_0(esk5_0))|v1_tsep_1(esk5_0,esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_54]), c_0_55]), c_0_25]), c_0_26])]), c_0_27])).
% 1.75/1.94  cnf(c_0_67, negated_conjecture, (k7_tmap_1(esk4_0,u1_struct_0(esk5_0))=k7_tmap_1(esk4_0,u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_42]), c_0_55]), c_0_25]), c_0_26])]), c_0_27])).
% 1.75/1.94  cnf(c_0_68, plain, (X1=k8_tmap_1(X2,X3)|v2_struct_0(X2)|X1!=k6_tmap_1(X2,esk1_3(X2,X3,X1))|~v1_pre_topc(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X3,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 1.75/1.94  cnf(c_0_69, negated_conjecture, (esk1_3(esk4_0,esk5_0,k6_tmap_1(esk4_0,u1_struct_0(esk5_0)))=u1_struct_0(esk5_0)|k6_tmap_1(esk4_0,u1_struct_0(esk5_0))=k8_tmap_1(esk4_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_56]), c_0_57]), c_0_36])])).
% 1.75/1.94  cnf(c_0_70, plain, (v1_funct_1(k7_tmap_1(X1,u1_struct_0(X2)))|v2_struct_0(X1)|~v2_pre_topc(X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_58, c_0_20])).
% 1.75/1.94  fof(c_0_71, plain, ![X8]:(v2_struct_0(X8)|~l1_struct_0(X8)|~v1_xboole_0(u1_struct_0(X8))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).
% 1.75/1.94  fof(c_0_72, plain, ![X7]:(~l1_pre_topc(X7)|l1_struct_0(X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 1.75/1.94  cnf(c_0_73, plain, (v2_struct_0(X1)|~v2_struct_0(k6_tmap_1(X1,X2))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_59])).
% 1.75/1.94  cnf(c_0_74, negated_conjecture, (k6_tmap_1(esk4_0,u1_struct_0(esk4_0))=k8_tmap_1(esk4_0,esk5_0)|m1_subset_1(u1_struct_0(esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_50]), c_0_51]), c_0_25]), c_0_24]), c_0_52]), c_0_26])]), c_0_27])).
% 1.75/1.94  cnf(c_0_75, negated_conjecture, (esk1_3(X1,X1,k6_tmap_1(esk4_0,u1_struct_0(esk4_0)))=u1_struct_0(X1)|k6_tmap_1(esk4_0,u1_struct_0(esk4_0))=k8_tmap_1(X1,X1)|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_50]), c_0_51]), c_0_52])])).
% 1.75/1.94  cnf(c_0_76, plain, (v3_pre_topc(X1,X2)|v2_struct_0(X2)|~v5_pre_topc(k7_tmap_1(X2,X1),X2,k6_tmap_1(X2,X1))|~v2_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[c_0_63, c_0_64]), c_0_58]), c_0_65])).
% 1.75/1.94  cnf(c_0_77, negated_conjecture, (k7_tmap_1(esk4_0,esk3_2(esk4_0,esk5_0))=k7_tmap_1(esk4_0,u1_struct_0(esk4_0))|v1_tsep_1(esk5_0,esk4_0)), inference(rw,[status(thm)],[c_0_66, c_0_67])).
% 1.75/1.94  cnf(c_0_78, negated_conjecture, (k6_partfun1(u1_struct_0(esk4_0))=k7_tmap_1(esk4_0,u1_struct_0(esk4_0))), inference(rw,[status(thm)],[c_0_55, c_0_67])).
% 1.75/1.94  cnf(c_0_79, plain, (esk3_2(X1,X2)=u1_struct_0(X2)|v1_tsep_1(X2,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 1.75/1.94  fof(c_0_80, plain, ![X25, X26, X27, X28]:((X27!=k9_tmap_1(X25,X26)|(~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X25)))|(X28!=u1_struct_0(X26)|r1_funct_2(u1_struct_0(X25),u1_struct_0(k8_tmap_1(X25,X26)),u1_struct_0(X25),u1_struct_0(k6_tmap_1(X25,X28)),X27,k7_tmap_1(X25,X28))))|(~v1_funct_1(X27)|~v1_funct_2(X27,u1_struct_0(X25),u1_struct_0(k8_tmap_1(X25,X26)))|~m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X25),u1_struct_0(k8_tmap_1(X25,X26))))))|~m1_pre_topc(X26,X25)|(v2_struct_0(X25)|~v2_pre_topc(X25)|~l1_pre_topc(X25)))&((m1_subset_1(esk2_3(X25,X26,X27),k1_zfmisc_1(u1_struct_0(X25)))|X27=k9_tmap_1(X25,X26)|(~v1_funct_1(X27)|~v1_funct_2(X27,u1_struct_0(X25),u1_struct_0(k8_tmap_1(X25,X26)))|~m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X25),u1_struct_0(k8_tmap_1(X25,X26))))))|~m1_pre_topc(X26,X25)|(v2_struct_0(X25)|~v2_pre_topc(X25)|~l1_pre_topc(X25)))&((esk2_3(X25,X26,X27)=u1_struct_0(X26)|X27=k9_tmap_1(X25,X26)|(~v1_funct_1(X27)|~v1_funct_2(X27,u1_struct_0(X25),u1_struct_0(k8_tmap_1(X25,X26)))|~m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X25),u1_struct_0(k8_tmap_1(X25,X26))))))|~m1_pre_topc(X26,X25)|(v2_struct_0(X25)|~v2_pre_topc(X25)|~l1_pre_topc(X25)))&(~r1_funct_2(u1_struct_0(X25),u1_struct_0(k8_tmap_1(X25,X26)),u1_struct_0(X25),u1_struct_0(k6_tmap_1(X25,esk2_3(X25,X26,X27))),X27,k7_tmap_1(X25,esk2_3(X25,X26,X27)))|X27=k9_tmap_1(X25,X26)|(~v1_funct_1(X27)|~v1_funct_2(X27,u1_struct_0(X25),u1_struct_0(k8_tmap_1(X25,X26)))|~m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X25),u1_struct_0(k8_tmap_1(X25,X26))))))|~m1_pre_topc(X26,X25)|(v2_struct_0(X25)|~v2_pre_topc(X25)|~l1_pre_topc(X25)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d12_tmap_1])])])])])])).
% 1.75/1.94  cnf(c_0_81, negated_conjecture, (k6_tmap_1(esk4_0,u1_struct_0(esk5_0))=k8_tmap_1(esk4_0,esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_56]), c_0_25]), c_0_57]), c_0_24]), c_0_26]), c_0_36])]), c_0_27])).
% 1.75/1.94  fof(c_0_82, plain, ![X12, X13, X14, X15, X16, X17]:(v1_xboole_0(X13)|v1_xboole_0(X15)|~v1_funct_1(X16)|~v1_funct_2(X16,X12,X13)|~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X12,X13)))|~v1_funct_1(X17)|~v1_funct_2(X17,X14,X15)|~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X14,X15)))|r1_funct_2(X12,X13,X14,X15,X16,X16)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[reflexivity_r1_funct_2])])])).
% 1.75/1.94  cnf(c_0_83, negated_conjecture, (u1_struct_0(k6_tmap_1(esk4_0,u1_struct_0(esk4_0)))=u1_struct_0(esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_42]), c_0_25]), c_0_26])]), c_0_27])).
% 1.75/1.94  cnf(c_0_84, plain, (v1_funct_1(k7_tmap_1(X1,u1_struct_0(X1)))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_70, c_0_35])).
% 1.75/1.94  cnf(c_0_85, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_71])).
% 1.75/1.94  cnf(c_0_86, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_72])).
% 1.75/1.94  cnf(c_0_87, negated_conjecture, (m1_subset_1(u1_struct_0(esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0)))|~v2_struct_0(k8_tmap_1(esk4_0,esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_25]), c_0_42]), c_0_26])]), c_0_27])).
% 1.75/1.94  cnf(c_0_88, negated_conjecture, (esk1_3(esk4_0,esk4_0,k6_tmap_1(esk4_0,u1_struct_0(esk4_0)))=u1_struct_0(esk4_0)|k6_tmap_1(esk4_0,u1_struct_0(esk4_0))=k8_tmap_1(esk4_0,esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_25]), c_0_26])]), c_0_27])).
% 1.75/1.94  cnf(c_0_89, negated_conjecture, (v3_pre_topc(esk3_2(esk4_0,esk5_0),esk4_0)|v1_tsep_1(esk5_0,esk4_0)|~v5_pre_topc(k7_tmap_1(esk4_0,u1_struct_0(esk4_0)),esk4_0,k6_tmap_1(esk4_0,esk3_2(esk4_0,esk5_0)))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_77]), c_0_25]), c_0_26])]), c_0_27]), c_0_54])).
% 1.75/1.94  cnf(c_0_90, negated_conjecture, (k7_tmap_1(esk4_0,u1_struct_0(X1))=k7_tmap_1(esk4_0,u1_struct_0(esk4_0))|~m1_pre_topc(X1,esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_78]), c_0_25]), c_0_26])]), c_0_27])).
% 1.75/1.94  cnf(c_0_91, plain, (v1_tsep_1(X2,X1)|~v3_pre_topc(esk3_2(X1,X2),X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 1.75/1.94  cnf(c_0_92, negated_conjecture, (esk3_2(esk4_0,esk5_0)=u1_struct_0(esk5_0)|v1_tsep_1(esk5_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_24]), c_0_26])])).
% 1.75/1.94  cnf(c_0_93, plain, (esk2_3(X1,X2,X3)=u1_struct_0(X2)|X3=k9_tmap_1(X1,X2)|v2_struct_0(X1)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_80])).
% 1.75/1.94  cnf(c_0_94, negated_conjecture, (u1_struct_0(k8_tmap_1(esk4_0,esk5_0))=u1_struct_0(esk4_0)), inference(rw,[status(thm)],[c_0_29, c_0_81])).
% 1.75/1.94  cnf(c_0_95, plain, (v1_xboole_0(X1)|v1_xboole_0(X2)|r1_funct_2(X4,X1,X6,X2,X3,X3)|~v1_funct_1(X3)|~v1_funct_2(X3,X4,X1)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))|~v1_funct_1(X5)|~v1_funct_2(X5,X6,X2)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X6,X2)))), inference(split_conjunct,[status(thm)],[c_0_82])).
% 1.75/1.94  cnf(c_0_96, negated_conjecture, (m1_subset_1(k7_tmap_1(esk4_0,u1_struct_0(esk4_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk4_0))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_83]), c_0_25]), c_0_42]), c_0_26])]), c_0_27])).
% 1.75/1.94  cnf(c_0_97, negated_conjecture, (v1_funct_2(k7_tmap_1(esk4_0,u1_struct_0(esk4_0)),u1_struct_0(esk4_0),u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_83]), c_0_25]), c_0_42]), c_0_26])]), c_0_27])).
% 1.75/1.94  cnf(c_0_98, negated_conjecture, (v1_funct_1(k7_tmap_1(esk4_0,u1_struct_0(esk4_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_25]), c_0_26])]), c_0_27])).
% 1.75/1.94  cnf(c_0_99, plain, (v2_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_85, c_0_86])).
% 1.75/1.94  cnf(c_0_100, negated_conjecture, (l1_pre_topc(k8_tmap_1(esk4_0,esk5_0))), inference(rw,[status(thm)],[c_0_36, c_0_81])).
% 1.75/1.94  cnf(c_0_101, negated_conjecture, (~v2_struct_0(k8_tmap_1(esk4_0,esk5_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_81]), c_0_25]), c_0_26])]), c_0_27]), c_0_87])).
% 1.75/1.94  fof(c_0_102, plain, ![X38, X39]:(((v1_funct_1(k9_tmap_1(X38,X39))|(v2_struct_0(X38)|~v2_pre_topc(X38)|~l1_pre_topc(X38)|~m1_pre_topc(X39,X38)))&(v1_funct_2(k9_tmap_1(X38,X39),u1_struct_0(X38),u1_struct_0(k8_tmap_1(X38,X39)))|(v2_struct_0(X38)|~v2_pre_topc(X38)|~l1_pre_topc(X38)|~m1_pre_topc(X39,X38))))&(m1_subset_1(k9_tmap_1(X38,X39),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X38),u1_struct_0(k8_tmap_1(X38,X39)))))|(v2_struct_0(X38)|~v2_pre_topc(X38)|~l1_pre_topc(X38)|~m1_pre_topc(X39,X38)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k9_tmap_1])])])])).
% 1.75/1.94  cnf(c_0_103, negated_conjecture, (k6_tmap_1(esk4_0,u1_struct_0(esk4_0))=k8_tmap_1(esk4_0,esk4_0)|~m1_pre_topc(esk4_0,esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_88]), c_0_50]), c_0_25]), c_0_51]), c_0_26]), c_0_52])]), c_0_27])).
% 1.75/1.94  cnf(c_0_104, negated_conjecture, (v3_pre_topc(esk3_2(esk4_0,esk5_0),esk4_0)|v1_tsep_1(esk5_0,esk4_0)|~v5_pre_topc(k7_tmap_1(esk4_0,u1_struct_0(X1)),esk4_0,k6_tmap_1(esk4_0,esk3_2(esk4_0,esk5_0)))|~m1_pre_topc(X1,esk4_0)), inference(spm,[status(thm)],[c_0_89, c_0_90])).
% 1.75/1.94  cnf(c_0_105, negated_conjecture, (v1_tsep_1(esk5_0,esk4_0)|~v3_pre_topc(u1_struct_0(esk5_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_92]), c_0_24]), c_0_26])])).
% 1.75/1.94  cnf(c_0_106, negated_conjecture, (esk2_3(esk4_0,esk5_0,X1)=u1_struct_0(esk5_0)|X1=k9_tmap_1(esk4_0,esk5_0)|~v1_funct_2(X1,u1_struct_0(esk4_0),u1_struct_0(esk4_0))|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk4_0))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_94]), c_0_25]), c_0_24]), c_0_26])]), c_0_27])).
% 1.75/1.94  cnf(c_0_107, negated_conjecture, (r1_funct_2(X1,X2,u1_struct_0(esk4_0),u1_struct_0(esk4_0),X3,X3)|v1_xboole_0(u1_struct_0(esk4_0))|v1_xboole_0(X2)|~v1_funct_2(X3,X1,X2)|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_96]), c_0_97]), c_0_98])])).
% 1.75/1.94  cnf(c_0_108, negated_conjecture, (~v1_xboole_0(u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_94]), c_0_100])]), c_0_101])).
% 1.75/1.94  cnf(c_0_109, negated_conjecture, (~v1_tsep_1(esk5_0,esk4_0)|~m1_pre_topc(esk5_0,esk4_0)|~v1_funct_1(k9_tmap_1(esk4_0,esk5_0))|~v1_funct_2(k9_tmap_1(esk4_0,esk5_0),u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk4_0,esk5_0)))|~v5_pre_topc(k9_tmap_1(esk4_0,esk5_0),esk4_0,k8_tmap_1(esk4_0,esk5_0))|~m1_subset_1(k9_tmap_1(esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk4_0,esk5_0)))))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 1.75/1.94  cnf(c_0_110, plain, (v1_funct_1(k9_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_102])).
% 1.75/1.94  cnf(c_0_111, negated_conjecture, (k8_tmap_1(esk4_0,esk5_0)=k8_tmap_1(esk4_0,esk4_0)|m1_subset_1(u1_struct_0(esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0)))|~m1_pre_topc(esk4_0,esk4_0)), inference(spm,[status(thm)],[c_0_74, c_0_103])).
% 1.75/1.94  cnf(c_0_112, negated_conjecture, (v1_tsep_1(esk5_0,esk4_0)|~v5_pre_topc(k7_tmap_1(esk4_0,u1_struct_0(X1)),esk4_0,k8_tmap_1(esk4_0,esk5_0))|~m1_pre_topc(X1,esk4_0)), inference(csr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104, c_0_92]), c_0_81]), c_0_105])).
% 1.75/1.94  cnf(c_0_113, plain, (X3=k9_tmap_1(X1,X2)|v2_struct_0(X1)|~r1_funct_2(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,esk2_3(X1,X2,X3))),X3,k7_tmap_1(X1,esk2_3(X1,X2,X3)))|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_80])).
% 1.75/1.94  cnf(c_0_114, negated_conjecture, (esk2_3(esk4_0,esk5_0,k7_tmap_1(esk4_0,u1_struct_0(esk4_0)))=u1_struct_0(esk5_0)|k7_tmap_1(esk4_0,u1_struct_0(esk4_0))=k9_tmap_1(esk4_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106, c_0_96]), c_0_97]), c_0_98])])).
% 1.75/1.94  cnf(c_0_115, negated_conjecture, (r1_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk4_0),k7_tmap_1(esk4_0,u1_struct_0(esk4_0)),k7_tmap_1(esk4_0,u1_struct_0(esk4_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107, c_0_96]), c_0_97]), c_0_98])]), c_0_108])).
% 1.75/1.94  cnf(c_0_116, negated_conjecture, (~v5_pre_topc(k9_tmap_1(esk4_0,esk5_0),esk4_0,k8_tmap_1(esk4_0,esk5_0))|~v1_tsep_1(esk5_0,esk4_0)|~v1_funct_2(k9_tmap_1(esk4_0,esk5_0),u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk4_0,esk5_0)))|~v1_funct_1(k9_tmap_1(esk4_0,esk5_0))|~m1_subset_1(k9_tmap_1(esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk4_0,esk5_0)))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_109, c_0_24])])).
% 1.75/1.94  cnf(c_0_117, negated_conjecture, (v1_funct_1(k9_tmap_1(esk4_0,esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110, c_0_24]), c_0_25]), c_0_26])]), c_0_27])).
% 1.75/1.94  cnf(c_0_118, plain, (v1_funct_2(k9_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_102])).
% 1.75/1.94  cnf(c_0_119, plain, (m1_subset_1(k9_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_102])).
% 1.75/1.94  cnf(c_0_120, plain, (v3_pre_topc(X3,X2)|~v1_tsep_1(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|X3!=u1_struct_0(X1)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 1.75/1.94  cnf(c_0_121, negated_conjecture, (k8_tmap_1(esk4_0,esk5_0)=k8_tmap_1(esk4_0,esk4_0)|m1_subset_1(u1_struct_0(esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111, c_0_35]), c_0_26])])).
% 1.75/1.94  cnf(c_0_122, negated_conjecture, (v1_tsep_1(esk5_0,esk4_0)|~v5_pre_topc(k7_tmap_1(esk4_0,u1_struct_0(esk4_0)),esk4_0,k8_tmap_1(esk4_0,esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112, c_0_67]), c_0_24])])).
% 1.75/1.94  cnf(c_0_123, negated_conjecture, (k7_tmap_1(esk4_0,u1_struct_0(esk4_0))=k9_tmap_1(esk4_0,esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113, c_0_114]), c_0_25]), c_0_94]), c_0_81]), c_0_94]), c_0_67]), c_0_115]), c_0_94]), c_0_97]), c_0_98]), c_0_94]), c_0_96]), c_0_24]), c_0_26])]), c_0_27])).
% 1.75/1.94  cnf(c_0_124, negated_conjecture, (v5_pre_topc(k9_tmap_1(esk4_0,esk5_0),esk4_0,k8_tmap_1(esk4_0,esk5_0))|v1_tsep_1(esk5_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 1.75/1.94  cnf(c_0_125, negated_conjecture, (~v5_pre_topc(k9_tmap_1(esk4_0,esk5_0),esk4_0,k8_tmap_1(esk4_0,esk5_0))|~v1_tsep_1(esk5_0,esk4_0)|~v1_funct_2(k9_tmap_1(esk4_0,esk5_0),u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk4_0,esk5_0)))|~m1_subset_1(k9_tmap_1(esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk4_0,esk5_0)))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_116, c_0_117])])).
% 1.75/1.94  cnf(c_0_126, negated_conjecture, (v1_funct_2(k9_tmap_1(esk4_0,esk5_0),u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk4_0,esk5_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_118, c_0_24]), c_0_25]), c_0_26])]), c_0_27])).
% 1.75/1.94  cnf(c_0_127, negated_conjecture, (m1_subset_1(k9_tmap_1(esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk4_0,esk5_0)))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119, c_0_24]), c_0_25]), c_0_26])]), c_0_27])).
% 1.75/1.94  cnf(c_0_128, plain, (v5_pre_topc(k7_tmap_1(X1,X2),X1,k6_tmap_1(X1,X2))|v2_struct_0(X1)|~v3_pre_topc(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 1.75/1.94  cnf(c_0_129, negated_conjecture, (k8_tmap_1(esk4_0,esk5_0)=k8_tmap_1(esk4_0,esk4_0)|v3_pre_topc(u1_struct_0(esk5_0),esk4_0)|u1_struct_0(esk5_0)!=u1_struct_0(X1)|~v1_tsep_1(X1,esk4_0)|~m1_pre_topc(X1,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120, c_0_121]), c_0_26])])).
% 1.75/1.94  cnf(c_0_130, negated_conjecture, (v1_tsep_1(esk5_0,esk4_0)), inference(csr,[status(thm)],[inference(rw,[status(thm)],[c_0_122, c_0_123]), c_0_124])).
% 1.75/1.94  cnf(c_0_131, negated_conjecture, (~v5_pre_topc(k9_tmap_1(esk4_0,esk5_0),esk4_0,k8_tmap_1(esk4_0,esk5_0))|~v1_tsep_1(esk5_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_125, c_0_126])]), c_0_127])])).
% 1.75/1.94  cnf(c_0_132, plain, (v5_pre_topc(k7_tmap_1(X1,u1_struct_0(X2)),X1,k6_tmap_1(X1,u1_struct_0(X2)))|v2_struct_0(X1)|~v3_pre_topc(u1_struct_0(X2),X1)|~v2_pre_topc(X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_128, c_0_20])).
% 1.75/1.94  cnf(c_0_133, negated_conjecture, (k8_tmap_1(esk4_0,esk5_0)=k8_tmap_1(esk4_0,esk4_0)|v3_pre_topc(u1_struct_0(esk5_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_129, c_0_130]), c_0_24])])).
% 1.75/1.94  cnf(c_0_134, negated_conjecture, (~v5_pre_topc(k9_tmap_1(esk4_0,esk5_0),esk4_0,k8_tmap_1(esk4_0,esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_131, c_0_130])])).
% 1.75/1.94  cnf(c_0_135, plain, (v3_pre_topc(u1_struct_0(X1),X2)|u1_struct_0(X1)!=u1_struct_0(X3)|~v1_tsep_1(X3,X2)|~m1_pre_topc(X3,X2)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(spm,[status(thm)],[c_0_120, c_0_20])).
% 1.75/1.94  cnf(c_0_136, negated_conjecture, (v1_tsep_1(esk5_0,esk4_0)|m1_subset_1(u1_struct_0(esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_92]), c_0_24]), c_0_26])])).
% 1.75/1.94  cnf(c_0_137, negated_conjecture, (k8_tmap_1(esk4_0,esk5_0)=k8_tmap_1(esk4_0,esk4_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_132, c_0_133]), c_0_67]), c_0_123]), c_0_81]), c_0_25]), c_0_24]), c_0_26])]), c_0_134]), c_0_27])).
% 1.75/1.94  cnf(c_0_138, negated_conjecture, (v3_pre_topc(u1_struct_0(X1),esk4_0)|m1_subset_1(u1_struct_0(esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0)))|u1_struct_0(X1)!=u1_struct_0(esk5_0)|~m1_pre_topc(X1,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_135, c_0_136]), c_0_24]), c_0_26])])).
% 1.75/1.94  cnf(c_0_139, negated_conjecture, (k7_tmap_1(esk4_0,u1_struct_0(esk5_0))=k9_tmap_1(esk4_0,esk5_0)), inference(rw,[status(thm)],[c_0_67, c_0_123])).
% 1.75/1.94  cnf(c_0_140, negated_conjecture, (~v5_pre_topc(k9_tmap_1(esk4_0,esk5_0),esk4_0,k8_tmap_1(esk4_0,esk4_0))), inference(rw,[status(thm)],[c_0_134, c_0_137])).
% 1.75/1.94  cnf(c_0_141, negated_conjecture, (v3_pre_topc(u1_struct_0(esk5_0),esk4_0)|m1_subset_1(u1_struct_0(esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(spm,[status(thm)],[c_0_138, c_0_24])).
% 1.75/1.94  cnf(c_0_142, negated_conjecture, (~v3_pre_topc(u1_struct_0(esk5_0),esk4_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_132, c_0_139]), c_0_81]), c_0_137]), c_0_25]), c_0_24]), c_0_26])]), c_0_140]), c_0_27])).
% 1.75/1.94  cnf(c_0_143, negated_conjecture, (m1_subset_1(u1_struct_0(esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(sr,[status(thm)],[c_0_141, c_0_142])).
% 1.75/1.94  cnf(c_0_144, negated_conjecture, (u1_struct_0(esk5_0)!=u1_struct_0(X1)|~v1_tsep_1(X1,esk4_0)|~m1_pre_topc(X1,esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120, c_0_143]), c_0_26])]), c_0_142])).
% 1.75/1.94  cnf(c_0_145, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_144, c_0_130]), c_0_24])]), ['proof']).
% 1.75/1.94  # SZS output end CNFRefutation
% 1.75/1.94  # Proof object total steps             : 146
% 1.75/1.94  # Proof object clause steps            : 113
% 1.75/1.94  # Proof object formula steps           : 33
% 1.75/1.94  # Proof object conjectures             : 75
% 1.75/1.94  # Proof object clause conjectures      : 72
% 1.75/1.94  # Proof object formula conjectures     : 3
% 1.75/1.94  # Proof object initial clauses used    : 34
% 1.75/1.94  # Proof object initial formulas used   : 16
% 1.75/1.94  # Proof object generating inferences   : 66
% 1.75/1.94  # Proof object simplifying inferences  : 231
% 1.75/1.94  # Training examples: 0 positive, 0 negative
% 1.75/1.94  # Parsed axioms                        : 17
% 1.75/1.94  # Removed by relevancy pruning/SinE    : 0
% 1.75/1.94  # Initial clauses                      : 51
% 1.75/1.94  # Removed in clause preprocessing      : 0
% 1.75/1.94  # Initial clauses in saturation        : 51
% 1.75/1.94  # Processed clauses                    : 5257
% 1.75/1.94  # ...of these trivial                  : 157
% 1.75/1.94  # ...subsumed                          : 3305
% 1.75/1.94  # ...remaining for further processing  : 1795
% 1.75/1.94  # Other redundant clauses eliminated   : 0
% 1.75/1.94  # Clauses deleted for lack of memory   : 0
% 1.75/1.94  # Backward-subsumed                    : 172
% 1.75/1.94  # Backward-rewritten                   : 843
% 1.75/1.94  # Generated clauses                    : 33962
% 1.75/1.94  # ...of the previous two non-trivial   : 29543
% 1.75/1.94  # Contextual simplify-reflections      : 857
% 1.75/1.94  # Paramodulations                      : 33936
% 1.75/1.94  # Factorizations                       : 4
% 1.75/1.94  # Equation resolutions                 : 20
% 1.75/1.94  # Propositional unsat checks           : 0
% 1.75/1.94  #    Propositional check models        : 0
% 1.75/1.94  #    Propositional check unsatisfiable : 0
% 1.75/1.94  #    Propositional clauses             : 0
% 1.75/1.94  #    Propositional clauses after purity: 0
% 1.75/1.94  #    Propositional unsat core size     : 0
% 1.75/1.94  #    Propositional preprocessing time  : 0.000
% 1.75/1.94  #    Propositional encoding time       : 0.000
% 1.75/1.94  #    Propositional solver time         : 0.000
% 1.75/1.94  #    Success case prop preproc time    : 0.000
% 1.75/1.94  #    Success case prop encoding time   : 0.000
% 1.75/1.94  #    Success case prop solver time     : 0.000
% 1.75/1.94  # Current number of processed clauses  : 778
% 1.75/1.94  #    Positive orientable unit clauses  : 27
% 1.75/1.94  #    Positive unorientable unit clauses: 0
% 1.75/1.94  #    Negative unit clauses             : 5
% 1.75/1.94  #    Non-unit-clauses                  : 746
% 1.75/1.94  # Current number of unprocessed clauses: 24003
% 1.75/1.94  # ...number of literals in the above   : 136093
% 1.75/1.94  # Current number of archived formulas  : 0
% 1.75/1.94  # Current number of archived clauses   : 1017
% 1.75/1.94  # Clause-clause subsumption calls (NU) : 612215
% 1.75/1.94  # Rec. Clause-clause subsumption calls : 100030
% 1.75/1.94  # Non-unit clause-clause subsumptions  : 4269
% 1.75/1.94  # Unit Clause-clause subsumption calls : 4652
% 1.75/1.94  # Rewrite failures with RHS unbound    : 0
% 1.75/1.94  # BW rewrite match attempts            : 60
% 1.75/1.94  # BW rewrite match successes           : 27
% 1.75/1.94  # Condensation attempts                : 0
% 1.75/1.94  # Condensation successes               : 0
% 1.75/1.94  # Termbank termtop insertions          : 1294072
% 1.75/1.95  
% 1.75/1.95  # -------------------------------------------------
% 1.75/1.95  # User time                : 1.577 s
% 1.75/1.95  # System time              : 0.037 s
% 1.75/1.95  # Total time               : 1.614 s
% 1.75/1.95  # Maximum resident set size: 1604 pages
%------------------------------------------------------------------------------
