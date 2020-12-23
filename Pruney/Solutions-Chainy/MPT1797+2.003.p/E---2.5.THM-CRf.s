%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:18:20 EST 2020

% Result     : Theorem 0.87s
% Output     : CNFRefutation 0.87s
% Verified   : 
% Statistics : Number of formulae       :  111 (41430 expanded)
%              Number of clauses        :   86 (13017 expanded)
%              Number of leaves         :   12 (10246 expanded)
%              Depth                    :   22
%              Number of atoms          :  562 (347875 expanded)
%              Number of equality atoms :   75 (8400 expanded)
%              Maximal formula depth    :   20 (   5 average)
%              Maximal clause size      :   68 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t113_tmap_1,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tops_2)).

fof(d10_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k7_tmap_1(X1,X2) = k6_partfun1(u1_struct_0(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_tmap_1)).

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

fof(t171_funct_2,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k8_relset_1(X1,X1,k6_partfun1(X1),X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t171_funct_2)).

fof(t105_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X1,X2))))
             => ( X3 = X2
               => v3_pre_topc(X3,k6_tmap_1(X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_tmap_1)).

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

fof(c_0_12,negated_conjecture,(
    ~ ! [X1] :
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
    inference(assume_negation,[status(cth)],[t113_tmap_1])).

fof(c_0_13,plain,(
    ! [X31,X32] :
      ( ( u1_struct_0(k6_tmap_1(X31,X32)) = u1_struct_0(X31)
        | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))
        | v2_struct_0(X31)
        | ~ v2_pre_topc(X31)
        | ~ l1_pre_topc(X31) )
      & ( u1_pre_topc(k6_tmap_1(X31,X32)) = k5_tmap_1(X31,X32)
        | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))
        | v2_struct_0(X31)
        | ~ v2_pre_topc(X31)
        | ~ l1_pre_topc(X31) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t104_tmap_1])])])])])).

fof(c_0_14,negated_conjecture,
    ( ~ v2_struct_0(esk3_0)
    & v2_pre_topc(esk3_0)
    & l1_pre_topc(esk3_0)
    & m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))
    & ( ~ v3_pre_topc(esk4_0,esk3_0)
      | ~ v1_funct_1(k7_tmap_1(esk3_0,esk4_0))
      | ~ v1_funct_2(k7_tmap_1(esk3_0,esk4_0),u1_struct_0(esk3_0),u1_struct_0(k6_tmap_1(esk3_0,esk4_0)))
      | ~ v5_pre_topc(k7_tmap_1(esk3_0,esk4_0),esk3_0,k6_tmap_1(esk3_0,esk4_0))
      | ~ m1_subset_1(k7_tmap_1(esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(k6_tmap_1(esk3_0,esk4_0))))) )
    & ( v1_funct_1(k7_tmap_1(esk3_0,esk4_0))
      | v3_pre_topc(esk4_0,esk3_0) )
    & ( v1_funct_2(k7_tmap_1(esk3_0,esk4_0),u1_struct_0(esk3_0),u1_struct_0(k6_tmap_1(esk3_0,esk4_0)))
      | v3_pre_topc(esk4_0,esk3_0) )
    & ( v5_pre_topc(k7_tmap_1(esk3_0,esk4_0),esk3_0,k6_tmap_1(esk3_0,esk4_0))
      | v3_pre_topc(esk4_0,esk3_0) )
    & ( m1_subset_1(k7_tmap_1(esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(k6_tmap_1(esk3_0,esk4_0)))))
      | v3_pre_topc(esk4_0,esk3_0) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_12])])])])])).

fof(c_0_15,plain,(
    ! [X24,X25] :
      ( ( v1_pre_topc(k6_tmap_1(X24,X25))
        | v2_struct_0(X24)
        | ~ v2_pre_topc(X24)
        | ~ l1_pre_topc(X24)
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24))) )
      & ( v2_pre_topc(k6_tmap_1(X24,X25))
        | v2_struct_0(X24)
        | ~ v2_pre_topc(X24)
        | ~ l1_pre_topc(X24)
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24))) )
      & ( l1_pre_topc(k6_tmap_1(X24,X25))
        | v2_struct_0(X24)
        | ~ v2_pre_topc(X24)
        | ~ l1_pre_topc(X24)
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_tmap_1])])])])).

fof(c_0_16,plain,(
    ! [X29,X30] :
      ( ( ~ r2_hidden(X30,u1_pre_topc(X29))
        | u1_pre_topc(X29) = k5_tmap_1(X29,X30)
        | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))
        | v2_struct_0(X29)
        | ~ v2_pre_topc(X29)
        | ~ l1_pre_topc(X29) )
      & ( u1_pre_topc(X29) != k5_tmap_1(X29,X30)
        | r2_hidden(X30,u1_pre_topc(X29))
        | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))
        | v2_struct_0(X29)
        | ~ v2_pre_topc(X29)
        | ~ l1_pre_topc(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t103_tmap_1])])])])])).

fof(c_0_17,plain,(
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

cnf(c_0_18,plain,
    ( u1_pre_topc(k6_tmap_1(X1,X2)) = k5_tmap_1(X1,X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,plain,
    ( l1_pre_topc(k6_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,plain,
    ( u1_struct_0(k6_tmap_1(X1,X2)) = u1_struct_0(X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_25,plain,
    ( u1_pre_topc(X2) = k5_tmap_1(X2,X1)
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,u1_pre_topc(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_26,plain,(
    ! [X17,X18,X19,X20] :
      ( ( ~ v5_pre_topc(X19,X17,X18)
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X18)))
        | ~ v3_pre_topc(X20,X18)
        | v3_pre_topc(k8_relset_1(u1_struct_0(X17),u1_struct_0(X18),X19,X20),X17)
        | k2_struct_0(X18) = k1_xboole_0
        | ~ v1_funct_1(X19)
        | ~ v1_funct_2(X19,u1_struct_0(X17),u1_struct_0(X18))
        | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X17),u1_struct_0(X18))))
        | ~ l1_pre_topc(X18)
        | ~ l1_pre_topc(X17) )
      & ( m1_subset_1(esk2_3(X17,X18,X19),k1_zfmisc_1(u1_struct_0(X18)))
        | v5_pre_topc(X19,X17,X18)
        | k2_struct_0(X18) = k1_xboole_0
        | ~ v1_funct_1(X19)
        | ~ v1_funct_2(X19,u1_struct_0(X17),u1_struct_0(X18))
        | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X17),u1_struct_0(X18))))
        | ~ l1_pre_topc(X18)
        | ~ l1_pre_topc(X17) )
      & ( v3_pre_topc(esk2_3(X17,X18,X19),X18)
        | v5_pre_topc(X19,X17,X18)
        | k2_struct_0(X18) = k1_xboole_0
        | ~ v1_funct_1(X19)
        | ~ v1_funct_2(X19,u1_struct_0(X17),u1_struct_0(X18))
        | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X17),u1_struct_0(X18))))
        | ~ l1_pre_topc(X18)
        | ~ l1_pre_topc(X17) )
      & ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X17),u1_struct_0(X18),X19,esk2_3(X17,X18,X19)),X17)
        | v5_pre_topc(X19,X17,X18)
        | k2_struct_0(X18) = k1_xboole_0
        | ~ v1_funct_1(X19)
        | ~ v1_funct_2(X19,u1_struct_0(X17),u1_struct_0(X18))
        | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X17),u1_struct_0(X18))))
        | ~ l1_pre_topc(X18)
        | ~ l1_pre_topc(X17) )
      & ( ~ v5_pre_topc(X19,X17,X18)
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X18)))
        | ~ v3_pre_topc(X20,X18)
        | v3_pre_topc(k8_relset_1(u1_struct_0(X17),u1_struct_0(X18),X19,X20),X17)
        | k2_struct_0(X17) != k1_xboole_0
        | ~ v1_funct_1(X19)
        | ~ v1_funct_2(X19,u1_struct_0(X17),u1_struct_0(X18))
        | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X17),u1_struct_0(X18))))
        | ~ l1_pre_topc(X18)
        | ~ l1_pre_topc(X17) )
      & ( m1_subset_1(esk2_3(X17,X18,X19),k1_zfmisc_1(u1_struct_0(X18)))
        | v5_pre_topc(X19,X17,X18)
        | k2_struct_0(X17) != k1_xboole_0
        | ~ v1_funct_1(X19)
        | ~ v1_funct_2(X19,u1_struct_0(X17),u1_struct_0(X18))
        | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X17),u1_struct_0(X18))))
        | ~ l1_pre_topc(X18)
        | ~ l1_pre_topc(X17) )
      & ( v3_pre_topc(esk2_3(X17,X18,X19),X18)
        | v5_pre_topc(X19,X17,X18)
        | k2_struct_0(X17) != k1_xboole_0
        | ~ v1_funct_1(X19)
        | ~ v1_funct_2(X19,u1_struct_0(X17),u1_struct_0(X18))
        | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X17),u1_struct_0(X18))))
        | ~ l1_pre_topc(X18)
        | ~ l1_pre_topc(X17) )
      & ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X17),u1_struct_0(X18),X19,esk2_3(X17,X18,X19)),X17)
        | v5_pre_topc(X19,X17,X18)
        | k2_struct_0(X17) != k1_xboole_0
        | ~ v1_funct_1(X19)
        | ~ v1_funct_2(X19,u1_struct_0(X17),u1_struct_0(X18))
        | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X17),u1_struct_0(X18))))
        | ~ l1_pre_topc(X18)
        | ~ l1_pre_topc(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_tops_2])])])])])).

fof(c_0_27,plain,(
    ! [X22,X23] :
      ( v2_struct_0(X22)
      | ~ v2_pre_topc(X22)
      | ~ l1_pre_topc(X22)
      | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))
      | k7_tmap_1(X22,X23) = k6_partfun1(u1_struct_0(X22)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d10_tmap_1])])])])).

fof(c_0_28,plain,(
    ! [X26,X27] :
      ( ( v1_funct_1(k7_tmap_1(X26,X27))
        | v2_struct_0(X26)
        | ~ v2_pre_topc(X26)
        | ~ l1_pre_topc(X26)
        | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26))) )
      & ( v1_funct_2(k7_tmap_1(X26,X27),u1_struct_0(X26),u1_struct_0(k6_tmap_1(X26,X27)))
        | v2_struct_0(X26)
        | ~ v2_pre_topc(X26)
        | ~ l1_pre_topc(X26)
        | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26))) )
      & ( m1_subset_1(k7_tmap_1(X26,X27),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X26),u1_struct_0(k6_tmap_1(X26,X27)))))
        | v2_struct_0(X26)
        | ~ v2_pre_topc(X26)
        | ~ l1_pre_topc(X26)
        | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k7_tmap_1])])])])).

cnf(c_0_29,plain,
    ( r2_hidden(X1,u1_pre_topc(X2))
    | ~ v3_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_30,negated_conjecture,
    ( u1_pre_topc(k6_tmap_1(esk3_0,esk4_0)) = k5_tmap_1(esk3_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20]),c_0_21])]),c_0_22])).

cnf(c_0_31,negated_conjecture,
    ( l1_pre_topc(k6_tmap_1(esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_19]),c_0_20]),c_0_21])]),c_0_22])).

cnf(c_0_32,negated_conjecture,
    ( u1_struct_0(k6_tmap_1(esk3_0,esk4_0)) = u1_struct_0(esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_19]),c_0_20]),c_0_21])]),c_0_22])).

cnf(c_0_33,negated_conjecture,
    ( k5_tmap_1(esk3_0,esk4_0) = u1_pre_topc(esk3_0)
    | ~ r2_hidden(esk4_0,u1_pre_topc(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_19]),c_0_20]),c_0_21])]),c_0_22])).

cnf(c_0_34,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_35,plain,(
    ! [X9,X10] :
      ( ~ m1_subset_1(X10,k1_zfmisc_1(X9))
      | k8_relset_1(X9,X9,k6_partfun1(X9),X10) = X10 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t171_funct_2])])).

cnf(c_0_36,plain,
    ( v2_struct_0(X1)
    | k7_tmap_1(X1,X2) = k6_partfun1(u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_37,plain,
    ( v1_funct_2(k7_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_38,plain,
    ( v1_funct_1(k7_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_39,plain,
    ( m1_subset_1(k7_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(X1,k5_tmap_1(esk3_0,esk4_0))
    | ~ v3_pre_topc(X1,k6_tmap_1(esk3_0,esk4_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31]),c_0_32])])).

cnf(c_0_41,negated_conjecture,
    ( k5_tmap_1(esk3_0,esk4_0) = u1_pre_topc(esk3_0)
    | ~ v3_pre_topc(esk4_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_29]),c_0_21]),c_0_19])])).

fof(c_0_42,plain,(
    ! [X33,X34,X35] :
      ( v2_struct_0(X33)
      | ~ v2_pre_topc(X33)
      | ~ l1_pre_topc(X33)
      | ~ m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33)))
      | ~ m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X33,X34))))
      | X35 != X34
      | v3_pre_topc(X35,k6_tmap_1(X33,X34)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t105_tmap_1])])])])).

cnf(c_0_43,negated_conjecture,
    ( k2_struct_0(k6_tmap_1(esk3_0,esk4_0)) = k1_xboole_0
    | v3_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(esk3_0),X2,X3),X1)
    | ~ v5_pre_topc(X2,X1,k6_tmap_1(esk3_0,esk4_0))
    | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(esk3_0))
    | ~ v1_funct_1(X2)
    | ~ v3_pre_topc(X3,k6_tmap_1(esk3_0,esk4_0))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk3_0))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_32]),c_0_31])])).

cnf(c_0_44,plain,
    ( k8_relset_1(X2,X2,k6_partfun1(X2),X1) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_45,negated_conjecture,
    ( k6_partfun1(u1_struct_0(esk3_0)) = k7_tmap_1(esk3_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_19]),c_0_20]),c_0_21])]),c_0_22])).

cnf(c_0_46,negated_conjecture,
    ( v1_funct_2(k7_tmap_1(esk3_0,esk4_0),u1_struct_0(esk3_0),u1_struct_0(esk3_0)) ),
    inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_19]),c_0_20]),c_0_21])]),c_0_22]),c_0_32])).

cnf(c_0_47,negated_conjecture,
    ( v1_funct_1(k7_tmap_1(esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_19]),c_0_20]),c_0_21])]),c_0_22])).

cnf(c_0_48,negated_conjecture,
    ( m1_subset_1(k7_tmap_1(esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk3_0)))) ),
    inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_19]),c_0_20]),c_0_21])]),c_0_22]),c_0_32])).

cnf(c_0_49,plain,
    ( v3_pre_topc(X1,X2)
    | ~ r2_hidden(X1,u1_pre_topc(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_50,negated_conjecture,
    ( r2_hidden(X1,u1_pre_topc(esk3_0))
    | ~ v3_pre_topc(X1,k6_tmap_1(esk3_0,esk4_0))
    | ~ v3_pre_topc(esk4_0,esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_51,plain,
    ( v2_struct_0(X1)
    | v3_pre_topc(X3,k6_tmap_1(X1,X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X1,X2))))
    | X3 != X2 ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_52,plain,
    ( v3_pre_topc(esk2_3(X1,X2,X3),X2)
    | v5_pre_topc(X3,X1,X2)
    | k2_struct_0(X2) = k1_xboole_0
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_53,negated_conjecture,
    ( k2_struct_0(k6_tmap_1(esk3_0,esk4_0)) = k1_xboole_0
    | v3_pre_topc(X1,esk3_0)
    | ~ v5_pre_topc(k7_tmap_1(esk3_0,esk4_0),esk3_0,k6_tmap_1(esk3_0,esk4_0))
    | ~ v3_pre_topc(X1,k6_tmap_1(esk3_0,esk4_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45]),c_0_45]),c_0_46]),c_0_45]),c_0_47]),c_0_21]),c_0_45]),c_0_48])])).

cnf(c_0_54,negated_conjecture,
    ( v5_pre_topc(k7_tmap_1(esk3_0,esk4_0),esk3_0,k6_tmap_1(esk3_0,esk4_0))
    | v3_pre_topc(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_55,negated_conjecture,
    ( v3_pre_topc(X1,esk3_0)
    | ~ v3_pre_topc(X1,k6_tmap_1(esk3_0,esk4_0))
    | ~ v3_pre_topc(esk4_0,esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_21])])).

cnf(c_0_56,plain,
    ( v2_struct_0(X1)
    | v3_pre_topc(X2,k6_tmap_1(X1,X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X1,X2))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(er,[status(thm)],[c_0_51])).

cnf(c_0_57,negated_conjecture,
    ( ~ v3_pre_topc(esk4_0,esk3_0)
    | ~ v1_funct_1(k7_tmap_1(esk3_0,esk4_0))
    | ~ v1_funct_2(k7_tmap_1(esk3_0,esk4_0),u1_struct_0(esk3_0),u1_struct_0(k6_tmap_1(esk3_0,esk4_0)))
    | ~ v5_pre_topc(k7_tmap_1(esk3_0,esk4_0),esk3_0,k6_tmap_1(esk3_0,esk4_0))
    | ~ m1_subset_1(k7_tmap_1(esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(k6_tmap_1(esk3_0,esk4_0))))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_58,negated_conjecture,
    ( k2_struct_0(k6_tmap_1(esk3_0,esk4_0)) = k1_xboole_0
    | v5_pre_topc(X1,X2,k6_tmap_1(esk3_0,esk4_0))
    | v3_pre_topc(esk2_3(X2,k6_tmap_1(esk3_0,esk4_0),X1),k6_tmap_1(esk3_0,esk4_0))
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(esk3_0))
    | ~ v1_funct_1(X1)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(esk3_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_32]),c_0_31])])).

cnf(c_0_59,negated_conjecture,
    ( k2_struct_0(k6_tmap_1(esk3_0,esk4_0)) = k1_xboole_0
    | v3_pre_topc(X1,esk3_0)
    | ~ v3_pre_topc(X1,k6_tmap_1(esk3_0,esk4_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_55])).

cnf(c_0_60,negated_conjecture,
    ( v3_pre_topc(esk4_0,k6_tmap_1(esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_32]),c_0_20]),c_0_21]),c_0_19])]),c_0_22])).

cnf(c_0_61,plain,
    ( m1_subset_1(esk2_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X2)))
    | v5_pre_topc(X3,X1,X2)
    | k2_struct_0(X2) = k1_xboole_0
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_62,negated_conjecture,
    ( ~ v5_pre_topc(k7_tmap_1(esk3_0,esk4_0),esk3_0,k6_tmap_1(esk3_0,esk4_0))
    | ~ v1_funct_2(k7_tmap_1(esk3_0,esk4_0),u1_struct_0(esk3_0),u1_struct_0(k6_tmap_1(esk3_0,esk4_0)))
    | ~ v3_pre_topc(esk4_0,esk3_0)
    | ~ m1_subset_1(k7_tmap_1(esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(k6_tmap_1(esk3_0,esk4_0))))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_57,c_0_47])])).

cnf(c_0_63,negated_conjecture,
    ( k2_struct_0(k6_tmap_1(esk3_0,esk4_0)) = k1_xboole_0
    | v5_pre_topc(k7_tmap_1(esk3_0,esk4_0),esk3_0,k6_tmap_1(esk3_0,esk4_0))
    | v3_pre_topc(esk2_3(esk3_0,k6_tmap_1(esk3_0,esk4_0),k7_tmap_1(esk3_0,esk4_0)),k6_tmap_1(esk3_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_48]),c_0_46]),c_0_47]),c_0_21])])).

cnf(c_0_64,negated_conjecture,
    ( k2_struct_0(k6_tmap_1(esk3_0,esk4_0)) = k1_xboole_0
    | v3_pre_topc(esk4_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_19])])).

cnf(c_0_65,negated_conjecture,
    ( k2_struct_0(k6_tmap_1(esk3_0,esk4_0)) = k1_xboole_0
    | v5_pre_topc(X1,X2,k6_tmap_1(esk3_0,esk4_0))
    | m1_subset_1(esk2_3(X2,k6_tmap_1(esk3_0,esk4_0),X1),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(esk3_0))
    | ~ v1_funct_1(X1)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(esk3_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_32]),c_0_31])])).

cnf(c_0_66,negated_conjecture,
    ( ~ v5_pre_topc(k7_tmap_1(esk3_0,esk4_0),esk3_0,k6_tmap_1(esk3_0,esk4_0))
    | ~ v3_pre_topc(esk4_0,esk3_0)
    | ~ m1_subset_1(k7_tmap_1(esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk3_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_62,c_0_32]),c_0_32]),c_0_46])])).

cnf(c_0_67,plain,
    ( v5_pre_topc(X3,X1,X2)
    | k2_struct_0(X2) = k1_xboole_0
    | ~ v3_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,esk2_3(X1,X2,X3)),X1)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_68,negated_conjecture,
    ( k2_struct_0(k6_tmap_1(esk3_0,esk4_0)) = k1_xboole_0
    | v5_pre_topc(k7_tmap_1(esk3_0,esk4_0),esk3_0,k6_tmap_1(esk3_0,esk4_0))
    | v3_pre_topc(esk2_3(esk3_0,k6_tmap_1(esk3_0,esk4_0),k7_tmap_1(esk3_0,esk4_0)),esk3_0)
    | ~ m1_subset_1(esk2_3(esk3_0,k6_tmap_1(esk3_0,esk4_0),k7_tmap_1(esk3_0,esk4_0)),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_63]),c_0_64])).

cnf(c_0_69,negated_conjecture,
    ( k2_struct_0(k6_tmap_1(esk3_0,esk4_0)) = k1_xboole_0
    | v5_pre_topc(k7_tmap_1(esk3_0,esk4_0),esk3_0,k6_tmap_1(esk3_0,esk4_0))
    | m1_subset_1(esk2_3(esk3_0,k6_tmap_1(esk3_0,esk4_0),k7_tmap_1(esk3_0,esk4_0)),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_48]),c_0_46]),c_0_47]),c_0_21])])).

cnf(c_0_70,plain,
    ( v3_pre_topc(k8_relset_1(u1_struct_0(X2),u1_struct_0(X3),X1,X4),X2)
    | ~ v5_pre_topc(X1,X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ v3_pre_topc(X4,X3)
    | k2_struct_0(X2) != k1_xboole_0
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_71,plain,(
    ! [X11] :
      ( ~ l1_struct_0(X11)
      | k2_struct_0(X11) = u1_struct_0(X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

fof(c_0_72,plain,(
    ! [X14] :
      ( ~ l1_pre_topc(X14)
      | l1_struct_0(X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_73,negated_conjecture,
    ( ~ v5_pre_topc(k7_tmap_1(esk3_0,esk4_0),esk3_0,k6_tmap_1(esk3_0,esk4_0))
    | ~ v3_pre_topc(esk4_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_66,c_0_48])])).

cnf(c_0_74,negated_conjecture,
    ( k7_tmap_1(esk3_0,X1) = k7_tmap_1(esk3_0,esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_45]),c_0_20]),c_0_21])]),c_0_22])).

cnf(c_0_75,negated_conjecture,
    ( k2_struct_0(k6_tmap_1(esk3_0,esk4_0)) = k1_xboole_0
    | v5_pre_topc(X1,X2,k6_tmap_1(esk3_0,esk4_0))
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(esk3_0))
    | ~ v1_funct_1(X1)
    | ~ v3_pre_topc(k8_relset_1(u1_struct_0(X2),u1_struct_0(esk3_0),X1,esk2_3(X2,k6_tmap_1(esk3_0,esk4_0),X1)),X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(esk3_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_32]),c_0_31])])).

cnf(c_0_76,negated_conjecture,
    ( k2_struct_0(k6_tmap_1(esk3_0,esk4_0)) = k1_xboole_0
    | v5_pre_topc(k7_tmap_1(esk3_0,esk4_0),esk3_0,k6_tmap_1(esk3_0,esk4_0))
    | v3_pre_topc(esk2_3(esk3_0,k6_tmap_1(esk3_0,esk4_0),k7_tmap_1(esk3_0,esk4_0)),esk3_0) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_77,negated_conjecture,
    ( v3_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(esk3_0),X2,X3),X1)
    | k2_struct_0(X1) != k1_xboole_0
    | ~ v5_pre_topc(X2,X1,k6_tmap_1(esk3_0,esk4_0))
    | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(esk3_0))
    | ~ v1_funct_1(X2)
    | ~ v3_pre_topc(X3,k6_tmap_1(esk3_0,esk4_0))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk3_0))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_32]),c_0_31])])).

cnf(c_0_78,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_79,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_80,negated_conjecture,
    ( ~ v5_pre_topc(k7_tmap_1(esk3_0,X1),esk3_0,k6_tmap_1(esk3_0,esk4_0))
    | ~ v3_pre_topc(esk4_0,esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_81,negated_conjecture,
    ( k2_struct_0(k6_tmap_1(esk3_0,esk4_0)) = k1_xboole_0
    | v5_pre_topc(k7_tmap_1(esk3_0,esk4_0),esk3_0,k6_tmap_1(esk3_0,esk4_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_44]),c_0_45]),c_0_45]),c_0_46]),c_0_45]),c_0_47]),c_0_45]),c_0_21]),c_0_45]),c_0_48]),c_0_45])]),c_0_69]),c_0_76])).

cnf(c_0_82,negated_conjecture,
    ( v3_pre_topc(X1,esk3_0)
    | k2_struct_0(esk3_0) != k1_xboole_0
    | ~ v5_pre_topc(k7_tmap_1(esk3_0,esk4_0),esk3_0,k6_tmap_1(esk3_0,esk4_0))
    | ~ v3_pre_topc(X1,k6_tmap_1(esk3_0,esk4_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_44]),c_0_45]),c_0_45]),c_0_46]),c_0_45]),c_0_47]),c_0_21]),c_0_45]),c_0_48])])).

cnf(c_0_83,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_78,c_0_79])).

cnf(c_0_84,negated_conjecture,
    ( k2_struct_0(k6_tmap_1(esk3_0,esk4_0)) = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_81]),c_0_19])]),c_0_64])).

cnf(c_0_85,negated_conjecture,
    ( v3_pre_topc(X1,esk3_0)
    | u1_struct_0(esk3_0) != k1_xboole_0
    | ~ v5_pre_topc(k7_tmap_1(esk3_0,esk4_0),esk3_0,k6_tmap_1(esk3_0,esk4_0))
    | ~ v3_pre_topc(X1,k6_tmap_1(esk3_0,esk4_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_21])])).

cnf(c_0_86,negated_conjecture,
    ( u1_struct_0(esk3_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_84]),c_0_32]),c_0_31])])).

cnf(c_0_87,plain,
    ( v3_pre_topc(esk2_3(X1,X2,X3),X2)
    | v5_pre_topc(X3,X1,X2)
    | k2_struct_0(X1) != k1_xboole_0
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_88,negated_conjecture,
    ( v3_pre_topc(X1,esk3_0)
    | ~ v5_pre_topc(k7_tmap_1(esk3_0,esk4_0),esk3_0,k6_tmap_1(esk3_0,esk4_0))
    | ~ v3_pre_topc(X1,k6_tmap_1(esk3_0,esk4_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_85,c_0_86]),c_0_86])])).

cnf(c_0_89,negated_conjecture,
    ( v3_pre_topc(X1,esk3_0)
    | ~ v3_pre_topc(X1,k6_tmap_1(esk3_0,esk4_0))
    | ~ v3_pre_topc(esk4_0,esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(rw,[status(thm)],[c_0_55,c_0_86])).

cnf(c_0_90,plain,
    ( m1_subset_1(esk2_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X2)))
    | v5_pre_topc(X3,X1,X2)
    | k2_struct_0(X1) != k1_xboole_0
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_91,negated_conjecture,
    ( v5_pre_topc(X1,X2,k6_tmap_1(esk3_0,esk4_0))
    | v3_pre_topc(esk2_3(X2,k6_tmap_1(esk3_0,esk4_0),X1),k6_tmap_1(esk3_0,esk4_0))
    | k2_struct_0(X2) != k1_xboole_0
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(esk3_0))
    | ~ v1_funct_1(X1)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(esk3_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_32]),c_0_31])])).

cnf(c_0_92,negated_conjecture,
    ( v3_pre_topc(X1,esk3_0)
    | ~ v3_pre_topc(X1,k6_tmap_1(esk3_0,esk4_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_54]),c_0_89])).

cnf(c_0_93,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(rw,[status(thm)],[c_0_19,c_0_86])).

cnf(c_0_94,negated_conjecture,
    ( v5_pre_topc(X1,X2,k6_tmap_1(esk3_0,esk4_0))
    | m1_subset_1(esk2_3(X2,k6_tmap_1(esk3_0,esk4_0),X1),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | k2_struct_0(X2) != k1_xboole_0
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(esk3_0))
    | ~ v1_funct_1(X1)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(esk3_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_32]),c_0_31])])).

cnf(c_0_95,plain,
    ( v5_pre_topc(X3,X1,X2)
    | ~ v3_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,esk2_3(X1,X2,X3)),X1)
    | k2_struct_0(X1) != k1_xboole_0
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_96,negated_conjecture,
    ( v5_pre_topc(k7_tmap_1(esk3_0,esk4_0),esk3_0,k6_tmap_1(esk3_0,esk4_0))
    | v3_pre_topc(esk2_3(esk3_0,k6_tmap_1(esk3_0,esk4_0),k7_tmap_1(esk3_0,esk4_0)),k6_tmap_1(esk3_0,esk4_0))
    | k2_struct_0(esk3_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_48]),c_0_46]),c_0_47]),c_0_21])])).

cnf(c_0_97,negated_conjecture,
    ( v3_pre_topc(esk4_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_60]),c_0_93])])).

cnf(c_0_98,negated_conjecture,
    ( v5_pre_topc(k7_tmap_1(esk3_0,esk4_0),esk3_0,k6_tmap_1(esk3_0,esk4_0))
    | m1_subset_1(esk2_3(esk3_0,k6_tmap_1(esk3_0,esk4_0),k7_tmap_1(esk3_0,esk4_0)),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | k2_struct_0(esk3_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_48]),c_0_46]),c_0_47]),c_0_21])])).

cnf(c_0_99,negated_conjecture,
    ( v5_pre_topc(X1,X2,k6_tmap_1(esk3_0,esk4_0))
    | k2_struct_0(X2) != k1_xboole_0
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(esk3_0))
    | ~ v1_funct_1(X1)
    | ~ v3_pre_topc(k8_relset_1(u1_struct_0(X2),u1_struct_0(esk3_0),X1,esk2_3(X2,k6_tmap_1(esk3_0,esk4_0),X1)),X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(esk3_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_32]),c_0_31])])).

cnf(c_0_100,negated_conjecture,
    ( v5_pre_topc(k7_tmap_1(esk3_0,esk4_0),esk3_0,k6_tmap_1(esk3_0,esk4_0))
    | v3_pre_topc(esk2_3(esk3_0,k6_tmap_1(esk3_0,esk4_0),k7_tmap_1(esk3_0,esk4_0)),k6_tmap_1(esk3_0,esk4_0))
    | u1_struct_0(esk3_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_83]),c_0_21])])).

cnf(c_0_101,negated_conjecture,
    ( ~ v5_pre_topc(k7_tmap_1(esk3_0,esk4_0),esk3_0,k6_tmap_1(esk3_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_73,c_0_97])])).

cnf(c_0_102,negated_conjecture,
    ( v5_pre_topc(k7_tmap_1(esk3_0,esk4_0),esk3_0,k6_tmap_1(esk3_0,esk4_0))
    | m1_subset_1(esk2_3(esk3_0,k6_tmap_1(esk3_0,esk4_0),k7_tmap_1(esk3_0,esk4_0)),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | u1_struct_0(esk3_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_83]),c_0_21])])).

cnf(c_0_103,negated_conjecture,
    ( v5_pre_topc(k7_tmap_1(esk3_0,esk4_0),esk3_0,k6_tmap_1(esk3_0,esk4_0))
    | k2_struct_0(esk3_0) != k1_xboole_0
    | ~ v3_pre_topc(esk2_3(esk3_0,k6_tmap_1(esk3_0,esk4_0),k7_tmap_1(esk3_0,esk4_0)),esk3_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_44]),c_0_45]),c_0_45]),c_0_46]),c_0_45]),c_0_47]),c_0_45]),c_0_21]),c_0_45]),c_0_48]),c_0_45])]),c_0_98])).

cnf(c_0_104,negated_conjecture,
    ( k7_tmap_1(esk3_0,X1) = k7_tmap_1(esk3_0,esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(rw,[status(thm)],[c_0_74,c_0_86])).

cnf(c_0_105,negated_conjecture,
    ( v3_pre_topc(esk2_3(esk3_0,k6_tmap_1(esk3_0,esk4_0),k7_tmap_1(esk3_0,esk4_0)),k6_tmap_1(esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_100,c_0_86])]),c_0_101])).

cnf(c_0_106,negated_conjecture,
    ( m1_subset_1(esk2_3(esk3_0,k6_tmap_1(esk3_0,esk4_0),k7_tmap_1(esk3_0,esk4_0)),k1_zfmisc_1(k1_xboole_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_102,c_0_86]),c_0_86])]),c_0_101])).

cnf(c_0_107,negated_conjecture,
    ( k2_struct_0(esk3_0) != k1_xboole_0
    | ~ v3_pre_topc(esk2_3(esk3_0,k6_tmap_1(esk3_0,esk4_0),k7_tmap_1(esk3_0,esk4_0)),esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_104]),c_0_93])]),c_0_101])).

cnf(c_0_108,negated_conjecture,
    ( v3_pre_topc(esk2_3(esk3_0,k6_tmap_1(esk3_0,esk4_0),k7_tmap_1(esk3_0,esk4_0)),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_105]),c_0_106])])).

cnf(c_0_109,negated_conjecture,
    ( k2_struct_0(esk3_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_107,c_0_108])])).

cnf(c_0_110,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_83]),c_0_86]),c_0_21])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 11:31:09 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.87/1.03  # AutoSched0-Mode selected heuristic G_E___302_C18_F1_URBAN_RG_S04BN
% 0.87/1.03  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.87/1.03  #
% 0.87/1.03  # Preprocessing time       : 0.038 s
% 0.87/1.03  
% 0.87/1.03  # Proof found!
% 0.87/1.03  # SZS status Theorem
% 0.87/1.03  # SZS output start CNFRefutation
% 0.87/1.03  fof(t113_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>(((v1_funct_1(k7_tmap_1(X1,X2))&v1_funct_2(k7_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2))))&v5_pre_topc(k7_tmap_1(X1,X2),X1,k6_tmap_1(X1,X2)))&m1_subset_1(k7_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_tmap_1)).
% 0.87/1.03  fof(t104_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(u1_struct_0(k6_tmap_1(X1,X2))=u1_struct_0(X1)&u1_pre_topc(k6_tmap_1(X1,X2))=k5_tmap_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t104_tmap_1)).
% 0.87/1.03  fof(dt_k6_tmap_1, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>((v1_pre_topc(k6_tmap_1(X1,X2))&v2_pre_topc(k6_tmap_1(X1,X2)))&l1_pre_topc(k6_tmap_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_tmap_1)).
% 0.87/1.03  fof(t103_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(r2_hidden(X2,u1_pre_topc(X1))<=>u1_pre_topc(X1)=k5_tmap_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t103_tmap_1)).
% 0.87/1.03  fof(d5_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>r2_hidden(X2,u1_pre_topc(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_pre_topc)).
% 0.87/1.03  fof(t55_tops_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(l1_pre_topc(X2)=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>((k2_struct_0(X2)=k1_xboole_0=>k2_struct_0(X1)=k1_xboole_0)=>(v5_pre_topc(X3,X1,X2)<=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))=>(v3_pre_topc(X4,X2)=>v3_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4),X1)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_tops_2)).
% 0.87/1.03  fof(d10_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k7_tmap_1(X1,X2)=k6_partfun1(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_tmap_1)).
% 0.87/1.03  fof(dt_k7_tmap_1, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>((v1_funct_1(k7_tmap_1(X1,X2))&v1_funct_2(k7_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2))))&m1_subset_1(k7_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_tmap_1)).
% 0.87/1.03  fof(t171_funct_2, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k8_relset_1(X1,X1,k6_partfun1(X1),X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t171_funct_2)).
% 0.87/1.03  fof(t105_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X1,X2))))=>(X3=X2=>v3_pre_topc(X3,k6_tmap_1(X1,X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t105_tmap_1)).
% 0.87/1.03  fof(d3_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>k2_struct_0(X1)=u1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 0.87/1.03  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.87/1.03  fof(c_0_12, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>(((v1_funct_1(k7_tmap_1(X1,X2))&v1_funct_2(k7_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2))))&v5_pre_topc(k7_tmap_1(X1,X2),X1,k6_tmap_1(X1,X2)))&m1_subset_1(k7_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))))))))), inference(assume_negation,[status(cth)],[t113_tmap_1])).
% 0.87/1.03  fof(c_0_13, plain, ![X31, X32]:((u1_struct_0(k6_tmap_1(X31,X32))=u1_struct_0(X31)|~m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))|(v2_struct_0(X31)|~v2_pre_topc(X31)|~l1_pre_topc(X31)))&(u1_pre_topc(k6_tmap_1(X31,X32))=k5_tmap_1(X31,X32)|~m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))|(v2_struct_0(X31)|~v2_pre_topc(X31)|~l1_pre_topc(X31)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t104_tmap_1])])])])])).
% 0.87/1.03  fof(c_0_14, negated_conjecture, (((~v2_struct_0(esk3_0)&v2_pre_topc(esk3_0))&l1_pre_topc(esk3_0))&(m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))&((~v3_pre_topc(esk4_0,esk3_0)|(~v1_funct_1(k7_tmap_1(esk3_0,esk4_0))|~v1_funct_2(k7_tmap_1(esk3_0,esk4_0),u1_struct_0(esk3_0),u1_struct_0(k6_tmap_1(esk3_0,esk4_0)))|~v5_pre_topc(k7_tmap_1(esk3_0,esk4_0),esk3_0,k6_tmap_1(esk3_0,esk4_0))|~m1_subset_1(k7_tmap_1(esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(k6_tmap_1(esk3_0,esk4_0)))))))&((((v1_funct_1(k7_tmap_1(esk3_0,esk4_0))|v3_pre_topc(esk4_0,esk3_0))&(v1_funct_2(k7_tmap_1(esk3_0,esk4_0),u1_struct_0(esk3_0),u1_struct_0(k6_tmap_1(esk3_0,esk4_0)))|v3_pre_topc(esk4_0,esk3_0)))&(v5_pre_topc(k7_tmap_1(esk3_0,esk4_0),esk3_0,k6_tmap_1(esk3_0,esk4_0))|v3_pre_topc(esk4_0,esk3_0)))&(m1_subset_1(k7_tmap_1(esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(k6_tmap_1(esk3_0,esk4_0)))))|v3_pre_topc(esk4_0,esk3_0)))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_12])])])])])).
% 0.87/1.03  fof(c_0_15, plain, ![X24, X25]:(((v1_pre_topc(k6_tmap_1(X24,X25))|(v2_struct_0(X24)|~v2_pre_topc(X24)|~l1_pre_topc(X24)|~m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))))&(v2_pre_topc(k6_tmap_1(X24,X25))|(v2_struct_0(X24)|~v2_pre_topc(X24)|~l1_pre_topc(X24)|~m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24))))))&(l1_pre_topc(k6_tmap_1(X24,X25))|(v2_struct_0(X24)|~v2_pre_topc(X24)|~l1_pre_topc(X24)|~m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_tmap_1])])])])).
% 0.87/1.03  fof(c_0_16, plain, ![X29, X30]:((~r2_hidden(X30,u1_pre_topc(X29))|u1_pre_topc(X29)=k5_tmap_1(X29,X30)|~m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))|(v2_struct_0(X29)|~v2_pre_topc(X29)|~l1_pre_topc(X29)))&(u1_pre_topc(X29)!=k5_tmap_1(X29,X30)|r2_hidden(X30,u1_pre_topc(X29))|~m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))|(v2_struct_0(X29)|~v2_pre_topc(X29)|~l1_pre_topc(X29)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t103_tmap_1])])])])])).
% 0.87/1.03  fof(c_0_17, plain, ![X12, X13]:((~v3_pre_topc(X13,X12)|r2_hidden(X13,u1_pre_topc(X12))|~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))|~l1_pre_topc(X12))&(~r2_hidden(X13,u1_pre_topc(X12))|v3_pre_topc(X13,X12)|~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))|~l1_pre_topc(X12))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_pre_topc])])])])).
% 0.87/1.03  cnf(c_0_18, plain, (u1_pre_topc(k6_tmap_1(X1,X2))=k5_tmap_1(X1,X2)|v2_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.87/1.03  cnf(c_0_19, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.87/1.03  cnf(c_0_20, negated_conjecture, (v2_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.87/1.03  cnf(c_0_21, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.87/1.03  cnf(c_0_22, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.87/1.03  cnf(c_0_23, plain, (l1_pre_topc(k6_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.87/1.03  cnf(c_0_24, plain, (u1_struct_0(k6_tmap_1(X1,X2))=u1_struct_0(X1)|v2_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.87/1.03  cnf(c_0_25, plain, (u1_pre_topc(X2)=k5_tmap_1(X2,X1)|v2_struct_0(X2)|~r2_hidden(X1,u1_pre_topc(X2))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.87/1.03  fof(c_0_26, plain, ![X17, X18, X19, X20]:(((~v5_pre_topc(X19,X17,X18)|(~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X18)))|(~v3_pre_topc(X20,X18)|v3_pre_topc(k8_relset_1(u1_struct_0(X17),u1_struct_0(X18),X19,X20),X17)))|k2_struct_0(X18)=k1_xboole_0|(~v1_funct_1(X19)|~v1_funct_2(X19,u1_struct_0(X17),u1_struct_0(X18))|~m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X17),u1_struct_0(X18)))))|~l1_pre_topc(X18)|~l1_pre_topc(X17))&((m1_subset_1(esk2_3(X17,X18,X19),k1_zfmisc_1(u1_struct_0(X18)))|v5_pre_topc(X19,X17,X18)|k2_struct_0(X18)=k1_xboole_0|(~v1_funct_1(X19)|~v1_funct_2(X19,u1_struct_0(X17),u1_struct_0(X18))|~m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X17),u1_struct_0(X18)))))|~l1_pre_topc(X18)|~l1_pre_topc(X17))&((v3_pre_topc(esk2_3(X17,X18,X19),X18)|v5_pre_topc(X19,X17,X18)|k2_struct_0(X18)=k1_xboole_0|(~v1_funct_1(X19)|~v1_funct_2(X19,u1_struct_0(X17),u1_struct_0(X18))|~m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X17),u1_struct_0(X18)))))|~l1_pre_topc(X18)|~l1_pre_topc(X17))&(~v3_pre_topc(k8_relset_1(u1_struct_0(X17),u1_struct_0(X18),X19,esk2_3(X17,X18,X19)),X17)|v5_pre_topc(X19,X17,X18)|k2_struct_0(X18)=k1_xboole_0|(~v1_funct_1(X19)|~v1_funct_2(X19,u1_struct_0(X17),u1_struct_0(X18))|~m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X17),u1_struct_0(X18)))))|~l1_pre_topc(X18)|~l1_pre_topc(X17)))))&((~v5_pre_topc(X19,X17,X18)|(~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X18)))|(~v3_pre_topc(X20,X18)|v3_pre_topc(k8_relset_1(u1_struct_0(X17),u1_struct_0(X18),X19,X20),X17)))|k2_struct_0(X17)!=k1_xboole_0|(~v1_funct_1(X19)|~v1_funct_2(X19,u1_struct_0(X17),u1_struct_0(X18))|~m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X17),u1_struct_0(X18)))))|~l1_pre_topc(X18)|~l1_pre_topc(X17))&((m1_subset_1(esk2_3(X17,X18,X19),k1_zfmisc_1(u1_struct_0(X18)))|v5_pre_topc(X19,X17,X18)|k2_struct_0(X17)!=k1_xboole_0|(~v1_funct_1(X19)|~v1_funct_2(X19,u1_struct_0(X17),u1_struct_0(X18))|~m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X17),u1_struct_0(X18)))))|~l1_pre_topc(X18)|~l1_pre_topc(X17))&((v3_pre_topc(esk2_3(X17,X18,X19),X18)|v5_pre_topc(X19,X17,X18)|k2_struct_0(X17)!=k1_xboole_0|(~v1_funct_1(X19)|~v1_funct_2(X19,u1_struct_0(X17),u1_struct_0(X18))|~m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X17),u1_struct_0(X18)))))|~l1_pre_topc(X18)|~l1_pre_topc(X17))&(~v3_pre_topc(k8_relset_1(u1_struct_0(X17),u1_struct_0(X18),X19,esk2_3(X17,X18,X19)),X17)|v5_pre_topc(X19,X17,X18)|k2_struct_0(X17)!=k1_xboole_0|(~v1_funct_1(X19)|~v1_funct_2(X19,u1_struct_0(X17),u1_struct_0(X18))|~m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X17),u1_struct_0(X18)))))|~l1_pre_topc(X18)|~l1_pre_topc(X17)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_tops_2])])])])])).
% 0.87/1.03  fof(c_0_27, plain, ![X22, X23]:(v2_struct_0(X22)|~v2_pre_topc(X22)|~l1_pre_topc(X22)|(~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))|k7_tmap_1(X22,X23)=k6_partfun1(u1_struct_0(X22)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d10_tmap_1])])])])).
% 0.87/1.03  fof(c_0_28, plain, ![X26, X27]:(((v1_funct_1(k7_tmap_1(X26,X27))|(v2_struct_0(X26)|~v2_pre_topc(X26)|~l1_pre_topc(X26)|~m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))))&(v1_funct_2(k7_tmap_1(X26,X27),u1_struct_0(X26),u1_struct_0(k6_tmap_1(X26,X27)))|(v2_struct_0(X26)|~v2_pre_topc(X26)|~l1_pre_topc(X26)|~m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26))))))&(m1_subset_1(k7_tmap_1(X26,X27),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X26),u1_struct_0(k6_tmap_1(X26,X27)))))|(v2_struct_0(X26)|~v2_pre_topc(X26)|~l1_pre_topc(X26)|~m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k7_tmap_1])])])])).
% 0.87/1.03  cnf(c_0_29, plain, (r2_hidden(X1,u1_pre_topc(X2))|~v3_pre_topc(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.87/1.03  cnf(c_0_30, negated_conjecture, (u1_pre_topc(k6_tmap_1(esk3_0,esk4_0))=k5_tmap_1(esk3_0,esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_20]), c_0_21])]), c_0_22])).
% 0.87/1.03  cnf(c_0_31, negated_conjecture, (l1_pre_topc(k6_tmap_1(esk3_0,esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_19]), c_0_20]), c_0_21])]), c_0_22])).
% 0.87/1.03  cnf(c_0_32, negated_conjecture, (u1_struct_0(k6_tmap_1(esk3_0,esk4_0))=u1_struct_0(esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_19]), c_0_20]), c_0_21])]), c_0_22])).
% 0.87/1.03  cnf(c_0_33, negated_conjecture, (k5_tmap_1(esk3_0,esk4_0)=u1_pre_topc(esk3_0)|~r2_hidden(esk4_0,u1_pre_topc(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_19]), c_0_20]), c_0_21])]), c_0_22])).
% 0.87/1.03  cnf(c_0_34, plain, (v3_pre_topc(k8_relset_1(u1_struct_0(X2),u1_struct_0(X3),X1,X4),X2)|k2_struct_0(X3)=k1_xboole_0|~v5_pre_topc(X1,X2,X3)|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))|~v3_pre_topc(X4,X3)|~v1_funct_1(X1)|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))|~l1_pre_topc(X3)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.87/1.03  fof(c_0_35, plain, ![X9, X10]:(~m1_subset_1(X10,k1_zfmisc_1(X9))|k8_relset_1(X9,X9,k6_partfun1(X9),X10)=X10), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t171_funct_2])])).
% 0.87/1.03  cnf(c_0_36, plain, (v2_struct_0(X1)|k7_tmap_1(X1,X2)=k6_partfun1(u1_struct_0(X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.87/1.03  cnf(c_0_37, plain, (v1_funct_2(k7_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.87/1.03  cnf(c_0_38, plain, (v1_funct_1(k7_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.87/1.03  cnf(c_0_39, plain, (m1_subset_1(k7_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.87/1.03  cnf(c_0_40, negated_conjecture, (r2_hidden(X1,k5_tmap_1(esk3_0,esk4_0))|~v3_pre_topc(X1,k6_tmap_1(esk3_0,esk4_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_31]), c_0_32])])).
% 0.87/1.03  cnf(c_0_41, negated_conjecture, (k5_tmap_1(esk3_0,esk4_0)=u1_pre_topc(esk3_0)|~v3_pre_topc(esk4_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_29]), c_0_21]), c_0_19])])).
% 0.87/1.03  fof(c_0_42, plain, ![X33, X34, X35]:(v2_struct_0(X33)|~v2_pre_topc(X33)|~l1_pre_topc(X33)|(~m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33)))|(~m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X33,X34))))|(X35!=X34|v3_pre_topc(X35,k6_tmap_1(X33,X34)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t105_tmap_1])])])])).
% 0.87/1.03  cnf(c_0_43, negated_conjecture, (k2_struct_0(k6_tmap_1(esk3_0,esk4_0))=k1_xboole_0|v3_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(esk3_0),X2,X3),X1)|~v5_pre_topc(X2,X1,k6_tmap_1(esk3_0,esk4_0))|~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(esk3_0))|~v1_funct_1(X2)|~v3_pre_topc(X3,k6_tmap_1(esk3_0,esk4_0))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk3_0))))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_32]), c_0_31])])).
% 0.87/1.03  cnf(c_0_44, plain, (k8_relset_1(X2,X2,k6_partfun1(X2),X1)=X1|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.87/1.03  cnf(c_0_45, negated_conjecture, (k6_partfun1(u1_struct_0(esk3_0))=k7_tmap_1(esk3_0,esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_19]), c_0_20]), c_0_21])]), c_0_22])).
% 0.87/1.03  cnf(c_0_46, negated_conjecture, (v1_funct_2(k7_tmap_1(esk3_0,esk4_0),u1_struct_0(esk3_0),u1_struct_0(esk3_0))), inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_19]), c_0_20]), c_0_21])]), c_0_22]), c_0_32])).
% 0.87/1.03  cnf(c_0_47, negated_conjecture, (v1_funct_1(k7_tmap_1(esk3_0,esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_19]), c_0_20]), c_0_21])]), c_0_22])).
% 0.87/1.03  cnf(c_0_48, negated_conjecture, (m1_subset_1(k7_tmap_1(esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk3_0))))), inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_19]), c_0_20]), c_0_21])]), c_0_22]), c_0_32])).
% 0.87/1.03  cnf(c_0_49, plain, (v3_pre_topc(X1,X2)|~r2_hidden(X1,u1_pre_topc(X2))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.87/1.03  cnf(c_0_50, negated_conjecture, (r2_hidden(X1,u1_pre_topc(esk3_0))|~v3_pre_topc(X1,k6_tmap_1(esk3_0,esk4_0))|~v3_pre_topc(esk4_0,esk3_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.87/1.03  cnf(c_0_51, plain, (v2_struct_0(X1)|v3_pre_topc(X3,k6_tmap_1(X1,X2))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X1,X2))))|X3!=X2), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.87/1.03  cnf(c_0_52, plain, (v3_pre_topc(esk2_3(X1,X2,X3),X2)|v5_pre_topc(X3,X1,X2)|k2_struct_0(X2)=k1_xboole_0|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.87/1.03  cnf(c_0_53, negated_conjecture, (k2_struct_0(k6_tmap_1(esk3_0,esk4_0))=k1_xboole_0|v3_pre_topc(X1,esk3_0)|~v5_pre_topc(k7_tmap_1(esk3_0,esk4_0),esk3_0,k6_tmap_1(esk3_0,esk4_0))|~v3_pre_topc(X1,k6_tmap_1(esk3_0,esk4_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_45]), c_0_45]), c_0_46]), c_0_45]), c_0_47]), c_0_21]), c_0_45]), c_0_48])])).
% 0.87/1.03  cnf(c_0_54, negated_conjecture, (v5_pre_topc(k7_tmap_1(esk3_0,esk4_0),esk3_0,k6_tmap_1(esk3_0,esk4_0))|v3_pre_topc(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.87/1.03  cnf(c_0_55, negated_conjecture, (v3_pre_topc(X1,esk3_0)|~v3_pre_topc(X1,k6_tmap_1(esk3_0,esk4_0))|~v3_pre_topc(esk4_0,esk3_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_21])])).
% 0.87/1.03  cnf(c_0_56, plain, (v2_struct_0(X1)|v3_pre_topc(X2,k6_tmap_1(X1,X2))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X1,X2))))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(er,[status(thm)],[c_0_51])).
% 0.87/1.03  cnf(c_0_57, negated_conjecture, (~v3_pre_topc(esk4_0,esk3_0)|~v1_funct_1(k7_tmap_1(esk3_0,esk4_0))|~v1_funct_2(k7_tmap_1(esk3_0,esk4_0),u1_struct_0(esk3_0),u1_struct_0(k6_tmap_1(esk3_0,esk4_0)))|~v5_pre_topc(k7_tmap_1(esk3_0,esk4_0),esk3_0,k6_tmap_1(esk3_0,esk4_0))|~m1_subset_1(k7_tmap_1(esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(k6_tmap_1(esk3_0,esk4_0)))))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.87/1.03  cnf(c_0_58, negated_conjecture, (k2_struct_0(k6_tmap_1(esk3_0,esk4_0))=k1_xboole_0|v5_pre_topc(X1,X2,k6_tmap_1(esk3_0,esk4_0))|v3_pre_topc(esk2_3(X2,k6_tmap_1(esk3_0,esk4_0),X1),k6_tmap_1(esk3_0,esk4_0))|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(esk3_0))|~v1_funct_1(X1)|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(esk3_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_32]), c_0_31])])).
% 0.87/1.03  cnf(c_0_59, negated_conjecture, (k2_struct_0(k6_tmap_1(esk3_0,esk4_0))=k1_xboole_0|v3_pre_topc(X1,esk3_0)|~v3_pre_topc(X1,k6_tmap_1(esk3_0,esk4_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_55])).
% 0.87/1.03  cnf(c_0_60, negated_conjecture, (v3_pre_topc(esk4_0,k6_tmap_1(esk3_0,esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_32]), c_0_20]), c_0_21]), c_0_19])]), c_0_22])).
% 0.87/1.03  cnf(c_0_61, plain, (m1_subset_1(esk2_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X2)))|v5_pre_topc(X3,X1,X2)|k2_struct_0(X2)=k1_xboole_0|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.87/1.03  cnf(c_0_62, negated_conjecture, (~v5_pre_topc(k7_tmap_1(esk3_0,esk4_0),esk3_0,k6_tmap_1(esk3_0,esk4_0))|~v1_funct_2(k7_tmap_1(esk3_0,esk4_0),u1_struct_0(esk3_0),u1_struct_0(k6_tmap_1(esk3_0,esk4_0)))|~v3_pre_topc(esk4_0,esk3_0)|~m1_subset_1(k7_tmap_1(esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(k6_tmap_1(esk3_0,esk4_0)))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_57, c_0_47])])).
% 0.87/1.03  cnf(c_0_63, negated_conjecture, (k2_struct_0(k6_tmap_1(esk3_0,esk4_0))=k1_xboole_0|v5_pre_topc(k7_tmap_1(esk3_0,esk4_0),esk3_0,k6_tmap_1(esk3_0,esk4_0))|v3_pre_topc(esk2_3(esk3_0,k6_tmap_1(esk3_0,esk4_0),k7_tmap_1(esk3_0,esk4_0)),k6_tmap_1(esk3_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_48]), c_0_46]), c_0_47]), c_0_21])])).
% 0.87/1.03  cnf(c_0_64, negated_conjecture, (k2_struct_0(k6_tmap_1(esk3_0,esk4_0))=k1_xboole_0|v3_pre_topc(esk4_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_19])])).
% 0.87/1.03  cnf(c_0_65, negated_conjecture, (k2_struct_0(k6_tmap_1(esk3_0,esk4_0))=k1_xboole_0|v5_pre_topc(X1,X2,k6_tmap_1(esk3_0,esk4_0))|m1_subset_1(esk2_3(X2,k6_tmap_1(esk3_0,esk4_0),X1),k1_zfmisc_1(u1_struct_0(esk3_0)))|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(esk3_0))|~v1_funct_1(X1)|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(esk3_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_32]), c_0_31])])).
% 0.87/1.03  cnf(c_0_66, negated_conjecture, (~v5_pre_topc(k7_tmap_1(esk3_0,esk4_0),esk3_0,k6_tmap_1(esk3_0,esk4_0))|~v3_pre_topc(esk4_0,esk3_0)|~m1_subset_1(k7_tmap_1(esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk3_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_62, c_0_32]), c_0_32]), c_0_46])])).
% 0.87/1.03  cnf(c_0_67, plain, (v5_pre_topc(X3,X1,X2)|k2_struct_0(X2)=k1_xboole_0|~v3_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,esk2_3(X1,X2,X3)),X1)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.87/1.03  cnf(c_0_68, negated_conjecture, (k2_struct_0(k6_tmap_1(esk3_0,esk4_0))=k1_xboole_0|v5_pre_topc(k7_tmap_1(esk3_0,esk4_0),esk3_0,k6_tmap_1(esk3_0,esk4_0))|v3_pre_topc(esk2_3(esk3_0,k6_tmap_1(esk3_0,esk4_0),k7_tmap_1(esk3_0,esk4_0)),esk3_0)|~m1_subset_1(esk2_3(esk3_0,k6_tmap_1(esk3_0,esk4_0),k7_tmap_1(esk3_0,esk4_0)),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_63]), c_0_64])).
% 0.87/1.03  cnf(c_0_69, negated_conjecture, (k2_struct_0(k6_tmap_1(esk3_0,esk4_0))=k1_xboole_0|v5_pre_topc(k7_tmap_1(esk3_0,esk4_0),esk3_0,k6_tmap_1(esk3_0,esk4_0))|m1_subset_1(esk2_3(esk3_0,k6_tmap_1(esk3_0,esk4_0),k7_tmap_1(esk3_0,esk4_0)),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_48]), c_0_46]), c_0_47]), c_0_21])])).
% 0.87/1.03  cnf(c_0_70, plain, (v3_pre_topc(k8_relset_1(u1_struct_0(X2),u1_struct_0(X3),X1,X4),X2)|~v5_pre_topc(X1,X2,X3)|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))|~v3_pre_topc(X4,X3)|k2_struct_0(X2)!=k1_xboole_0|~v1_funct_1(X1)|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))|~l1_pre_topc(X3)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.87/1.03  fof(c_0_71, plain, ![X11]:(~l1_struct_0(X11)|k2_struct_0(X11)=u1_struct_0(X11)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).
% 0.87/1.03  fof(c_0_72, plain, ![X14]:(~l1_pre_topc(X14)|l1_struct_0(X14)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.87/1.03  cnf(c_0_73, negated_conjecture, (~v5_pre_topc(k7_tmap_1(esk3_0,esk4_0),esk3_0,k6_tmap_1(esk3_0,esk4_0))|~v3_pre_topc(esk4_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_66, c_0_48])])).
% 0.87/1.03  cnf(c_0_74, negated_conjecture, (k7_tmap_1(esk3_0,X1)=k7_tmap_1(esk3_0,esk4_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_45]), c_0_20]), c_0_21])]), c_0_22])).
% 0.87/1.03  cnf(c_0_75, negated_conjecture, (k2_struct_0(k6_tmap_1(esk3_0,esk4_0))=k1_xboole_0|v5_pre_topc(X1,X2,k6_tmap_1(esk3_0,esk4_0))|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(esk3_0))|~v1_funct_1(X1)|~v3_pre_topc(k8_relset_1(u1_struct_0(X2),u1_struct_0(esk3_0),X1,esk2_3(X2,k6_tmap_1(esk3_0,esk4_0),X1)),X2)|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(esk3_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_32]), c_0_31])])).
% 0.87/1.03  cnf(c_0_76, negated_conjecture, (k2_struct_0(k6_tmap_1(esk3_0,esk4_0))=k1_xboole_0|v5_pre_topc(k7_tmap_1(esk3_0,esk4_0),esk3_0,k6_tmap_1(esk3_0,esk4_0))|v3_pre_topc(esk2_3(esk3_0,k6_tmap_1(esk3_0,esk4_0),k7_tmap_1(esk3_0,esk4_0)),esk3_0)), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 0.87/1.03  cnf(c_0_77, negated_conjecture, (v3_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(esk3_0),X2,X3),X1)|k2_struct_0(X1)!=k1_xboole_0|~v5_pre_topc(X2,X1,k6_tmap_1(esk3_0,esk4_0))|~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(esk3_0))|~v1_funct_1(X2)|~v3_pre_topc(X3,k6_tmap_1(esk3_0,esk4_0))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk3_0))))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_32]), c_0_31])])).
% 0.87/1.04  cnf(c_0_78, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_71])).
% 0.87/1.04  cnf(c_0_79, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_72])).
% 0.87/1.04  cnf(c_0_80, negated_conjecture, (~v5_pre_topc(k7_tmap_1(esk3_0,X1),esk3_0,k6_tmap_1(esk3_0,esk4_0))|~v3_pre_topc(esk4_0,esk3_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(spm,[status(thm)],[c_0_73, c_0_74])).
% 0.87/1.04  cnf(c_0_81, negated_conjecture, (k2_struct_0(k6_tmap_1(esk3_0,esk4_0))=k1_xboole_0|v5_pre_topc(k7_tmap_1(esk3_0,esk4_0),esk3_0,k6_tmap_1(esk3_0,esk4_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_44]), c_0_45]), c_0_45]), c_0_46]), c_0_45]), c_0_47]), c_0_45]), c_0_21]), c_0_45]), c_0_48]), c_0_45])]), c_0_69]), c_0_76])).
% 0.87/1.04  cnf(c_0_82, negated_conjecture, (v3_pre_topc(X1,esk3_0)|k2_struct_0(esk3_0)!=k1_xboole_0|~v5_pre_topc(k7_tmap_1(esk3_0,esk4_0),esk3_0,k6_tmap_1(esk3_0,esk4_0))|~v3_pre_topc(X1,k6_tmap_1(esk3_0,esk4_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_44]), c_0_45]), c_0_45]), c_0_46]), c_0_45]), c_0_47]), c_0_21]), c_0_45]), c_0_48])])).
% 0.87/1.04  cnf(c_0_83, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_78, c_0_79])).
% 0.87/1.04  cnf(c_0_84, negated_conjecture, (k2_struct_0(k6_tmap_1(esk3_0,esk4_0))=k1_xboole_0), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_81]), c_0_19])]), c_0_64])).
% 0.87/1.04  cnf(c_0_85, negated_conjecture, (v3_pre_topc(X1,esk3_0)|u1_struct_0(esk3_0)!=k1_xboole_0|~v5_pre_topc(k7_tmap_1(esk3_0,esk4_0),esk3_0,k6_tmap_1(esk3_0,esk4_0))|~v3_pre_topc(X1,k6_tmap_1(esk3_0,esk4_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_83]), c_0_21])])).
% 0.87/1.04  cnf(c_0_86, negated_conjecture, (u1_struct_0(esk3_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_84]), c_0_32]), c_0_31])])).
% 0.87/1.04  cnf(c_0_87, plain, (v3_pre_topc(esk2_3(X1,X2,X3),X2)|v5_pre_topc(X3,X1,X2)|k2_struct_0(X1)!=k1_xboole_0|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.87/1.04  cnf(c_0_88, negated_conjecture, (v3_pre_topc(X1,esk3_0)|~v5_pre_topc(k7_tmap_1(esk3_0,esk4_0),esk3_0,k6_tmap_1(esk3_0,esk4_0))|~v3_pre_topc(X1,k6_tmap_1(esk3_0,esk4_0))|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_85, c_0_86]), c_0_86])])).
% 0.87/1.04  cnf(c_0_89, negated_conjecture, (v3_pre_topc(X1,esk3_0)|~v3_pre_topc(X1,k6_tmap_1(esk3_0,esk4_0))|~v3_pre_topc(esk4_0,esk3_0)|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(rw,[status(thm)],[c_0_55, c_0_86])).
% 0.87/1.04  cnf(c_0_90, plain, (m1_subset_1(esk2_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X2)))|v5_pre_topc(X3,X1,X2)|k2_struct_0(X1)!=k1_xboole_0|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.87/1.04  cnf(c_0_91, negated_conjecture, (v5_pre_topc(X1,X2,k6_tmap_1(esk3_0,esk4_0))|v3_pre_topc(esk2_3(X2,k6_tmap_1(esk3_0,esk4_0),X1),k6_tmap_1(esk3_0,esk4_0))|k2_struct_0(X2)!=k1_xboole_0|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(esk3_0))|~v1_funct_1(X1)|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(esk3_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_32]), c_0_31])])).
% 0.87/1.04  cnf(c_0_92, negated_conjecture, (v3_pre_topc(X1,esk3_0)|~v3_pre_topc(X1,k6_tmap_1(esk3_0,esk4_0))|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_54]), c_0_89])).
% 0.87/1.04  cnf(c_0_93, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k1_xboole_0))), inference(rw,[status(thm)],[c_0_19, c_0_86])).
% 0.87/1.04  cnf(c_0_94, negated_conjecture, (v5_pre_topc(X1,X2,k6_tmap_1(esk3_0,esk4_0))|m1_subset_1(esk2_3(X2,k6_tmap_1(esk3_0,esk4_0),X1),k1_zfmisc_1(u1_struct_0(esk3_0)))|k2_struct_0(X2)!=k1_xboole_0|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(esk3_0))|~v1_funct_1(X1)|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(esk3_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_32]), c_0_31])])).
% 0.87/1.04  cnf(c_0_95, plain, (v5_pre_topc(X3,X1,X2)|~v3_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,esk2_3(X1,X2,X3)),X1)|k2_struct_0(X1)!=k1_xboole_0|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.87/1.04  cnf(c_0_96, negated_conjecture, (v5_pre_topc(k7_tmap_1(esk3_0,esk4_0),esk3_0,k6_tmap_1(esk3_0,esk4_0))|v3_pre_topc(esk2_3(esk3_0,k6_tmap_1(esk3_0,esk4_0),k7_tmap_1(esk3_0,esk4_0)),k6_tmap_1(esk3_0,esk4_0))|k2_struct_0(esk3_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_48]), c_0_46]), c_0_47]), c_0_21])])).
% 0.87/1.04  cnf(c_0_97, negated_conjecture, (v3_pre_topc(esk4_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_60]), c_0_93])])).
% 0.87/1.04  cnf(c_0_98, negated_conjecture, (v5_pre_topc(k7_tmap_1(esk3_0,esk4_0),esk3_0,k6_tmap_1(esk3_0,esk4_0))|m1_subset_1(esk2_3(esk3_0,k6_tmap_1(esk3_0,esk4_0),k7_tmap_1(esk3_0,esk4_0)),k1_zfmisc_1(u1_struct_0(esk3_0)))|k2_struct_0(esk3_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_48]), c_0_46]), c_0_47]), c_0_21])])).
% 0.87/1.04  cnf(c_0_99, negated_conjecture, (v5_pre_topc(X1,X2,k6_tmap_1(esk3_0,esk4_0))|k2_struct_0(X2)!=k1_xboole_0|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(esk3_0))|~v1_funct_1(X1)|~v3_pre_topc(k8_relset_1(u1_struct_0(X2),u1_struct_0(esk3_0),X1,esk2_3(X2,k6_tmap_1(esk3_0,esk4_0),X1)),X2)|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(esk3_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_32]), c_0_31])])).
% 0.87/1.04  cnf(c_0_100, negated_conjecture, (v5_pre_topc(k7_tmap_1(esk3_0,esk4_0),esk3_0,k6_tmap_1(esk3_0,esk4_0))|v3_pre_topc(esk2_3(esk3_0,k6_tmap_1(esk3_0,esk4_0),k7_tmap_1(esk3_0,esk4_0)),k6_tmap_1(esk3_0,esk4_0))|u1_struct_0(esk3_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_83]), c_0_21])])).
% 0.87/1.04  cnf(c_0_101, negated_conjecture, (~v5_pre_topc(k7_tmap_1(esk3_0,esk4_0),esk3_0,k6_tmap_1(esk3_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_73, c_0_97])])).
% 0.87/1.04  cnf(c_0_102, negated_conjecture, (v5_pre_topc(k7_tmap_1(esk3_0,esk4_0),esk3_0,k6_tmap_1(esk3_0,esk4_0))|m1_subset_1(esk2_3(esk3_0,k6_tmap_1(esk3_0,esk4_0),k7_tmap_1(esk3_0,esk4_0)),k1_zfmisc_1(u1_struct_0(esk3_0)))|u1_struct_0(esk3_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_83]), c_0_21])])).
% 0.87/1.04  cnf(c_0_103, negated_conjecture, (v5_pre_topc(k7_tmap_1(esk3_0,esk4_0),esk3_0,k6_tmap_1(esk3_0,esk4_0))|k2_struct_0(esk3_0)!=k1_xboole_0|~v3_pre_topc(esk2_3(esk3_0,k6_tmap_1(esk3_0,esk4_0),k7_tmap_1(esk3_0,esk4_0)),esk3_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_44]), c_0_45]), c_0_45]), c_0_46]), c_0_45]), c_0_47]), c_0_45]), c_0_21]), c_0_45]), c_0_48]), c_0_45])]), c_0_98])).
% 0.87/1.04  cnf(c_0_104, negated_conjecture, (k7_tmap_1(esk3_0,X1)=k7_tmap_1(esk3_0,esk4_0)|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(rw,[status(thm)],[c_0_74, c_0_86])).
% 0.87/1.04  cnf(c_0_105, negated_conjecture, (v3_pre_topc(esk2_3(esk3_0,k6_tmap_1(esk3_0,esk4_0),k7_tmap_1(esk3_0,esk4_0)),k6_tmap_1(esk3_0,esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_100, c_0_86])]), c_0_101])).
% 0.87/1.04  cnf(c_0_106, negated_conjecture, (m1_subset_1(esk2_3(esk3_0,k6_tmap_1(esk3_0,esk4_0),k7_tmap_1(esk3_0,esk4_0)),k1_zfmisc_1(k1_xboole_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_102, c_0_86]), c_0_86])]), c_0_101])).
% 0.87/1.04  cnf(c_0_107, negated_conjecture, (k2_struct_0(esk3_0)!=k1_xboole_0|~v3_pre_topc(esk2_3(esk3_0,k6_tmap_1(esk3_0,esk4_0),k7_tmap_1(esk3_0,esk4_0)),esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103, c_0_104]), c_0_93])]), c_0_101])).
% 0.87/1.04  cnf(c_0_108, negated_conjecture, (v3_pre_topc(esk2_3(esk3_0,k6_tmap_1(esk3_0,esk4_0),k7_tmap_1(esk3_0,esk4_0)),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_105]), c_0_106])])).
% 0.87/1.04  cnf(c_0_109, negated_conjecture, (k2_struct_0(esk3_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_107, c_0_108])])).
% 0.87/1.04  cnf(c_0_110, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109, c_0_83]), c_0_86]), c_0_21])]), ['proof']).
% 0.87/1.04  # SZS output end CNFRefutation
% 0.87/1.04  # Proof object total steps             : 111
% 0.87/1.04  # Proof object clause steps            : 86
% 0.87/1.04  # Proof object formula steps           : 25
% 0.87/1.04  # Proof object conjectures             : 65
% 0.87/1.04  # Proof object clause conjectures      : 62
% 0.87/1.04  # Proof object formula conjectures     : 3
% 0.87/1.04  # Proof object initial clauses used    : 28
% 0.87/1.04  # Proof object initial formulas used   : 12
% 0.87/1.04  # Proof object generating inferences   : 46
% 0.87/1.04  # Proof object simplifying inferences  : 179
% 0.87/1.04  # Training examples: 0 positive, 0 negative
% 0.87/1.04  # Parsed axioms                        : 15
% 0.87/1.04  # Removed by relevancy pruning/SinE    : 0
% 0.87/1.04  # Initial clauses                      : 41
% 0.87/1.04  # Removed in clause preprocessing      : 0
% 0.87/1.04  # Initial clauses in saturation        : 41
% 0.87/1.04  # Processed clauses                    : 2827
% 0.87/1.04  # ...of these trivial                  : 74
% 0.87/1.04  # ...subsumed                          : 1088
% 0.87/1.04  # ...remaining for further processing  : 1665
% 0.87/1.04  # Other redundant clauses eliminated   : 1
% 0.87/1.04  # Clauses deleted for lack of memory   : 0
% 0.87/1.04  # Backward-subsumed                    : 77
% 0.87/1.04  # Backward-rewritten                   : 628
% 0.87/1.04  # Generated clauses                    : 14984
% 0.87/1.04  # ...of the previous two non-trivial   : 14766
% 0.87/1.04  # Contextual simplify-reflections      : 559
% 0.87/1.04  # Paramodulations                      : 14976
% 0.87/1.04  # Factorizations                       : 0
% 0.87/1.04  # Equation resolutions                 : 1
% 0.87/1.04  # Propositional unsat checks           : 0
% 0.87/1.04  #    Propositional check models        : 0
% 0.87/1.04  #    Propositional check unsatisfiable : 0
% 0.87/1.04  #    Propositional clauses             : 0
% 0.87/1.04  #    Propositional clauses after purity: 0
% 0.87/1.04  #    Propositional unsat core size     : 0
% 0.87/1.04  #    Propositional preprocessing time  : 0.000
% 0.87/1.04  #    Propositional encoding time       : 0.000
% 0.87/1.04  #    Propositional solver time         : 0.000
% 0.87/1.04  #    Success case prop preproc time    : 0.000
% 0.87/1.04  #    Success case prop encoding time   : 0.000
% 0.87/1.04  #    Success case prop solver time     : 0.000
% 0.87/1.04  # Current number of processed clauses  : 952
% 0.87/1.04  #    Positive orientable unit clauses  : 108
% 0.87/1.04  #    Positive unorientable unit clauses: 0
% 0.87/1.04  #    Negative unit clauses             : 3
% 0.87/1.04  #    Non-unit-clauses                  : 841
% 0.87/1.04  # Current number of unprocessed clauses: 8973
% 0.87/1.04  # ...number of literals in the above   : 70180
% 0.87/1.04  # Current number of archived formulas  : 0
% 0.87/1.04  # Current number of archived clauses   : 712
% 0.87/1.04  # Clause-clause subsumption calls (NU) : 389122
% 0.87/1.04  # Rec. Clause-clause subsumption calls : 70602
% 0.87/1.04  # Non-unit clause-clause subsumptions  : 1701
% 0.87/1.04  # Unit Clause-clause subsumption calls : 9226
% 0.87/1.04  # Rewrite failures with RHS unbound    : 0
% 0.87/1.04  # BW rewrite match attempts            : 427
% 0.87/1.04  # BW rewrite match successes           : 33
% 0.87/1.04  # Condensation attempts                : 0
% 0.87/1.04  # Condensation successes               : 0
% 0.87/1.04  # Termbank termtop insertions          : 1011893
% 0.87/1.04  
% 0.87/1.04  # -------------------------------------------------
% 0.87/1.04  # User time                : 0.686 s
% 0.87/1.04  # System time              : 0.016 s
% 0.87/1.04  # Total time               : 0.702 s
% 0.87/1.04  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------
