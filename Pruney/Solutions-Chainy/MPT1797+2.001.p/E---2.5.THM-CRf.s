%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:18:20 EST 2020

% Result     : Theorem 1.39s
% Output     : CNFRefutation 1.39s
% Verified   : 
% Statistics : Number of formulae       :  158 (206317 expanded)
%              Number of clauses        :  125 (65384 expanded)
%              Number of leaves         :   16 (50840 expanded)
%              Depth                    :   23
%              Number of atoms          :  720 (1726651 expanded)
%              Number of equality atoms :   93 (41269 expanded)
%              Maximal formula depth    :   20 (   5 average)
%              Maximal clause size      :   68 (   3 average)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_tmap_1)).

fof(t104_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( u1_struct_0(k6_tmap_1(X1,X2)) = u1_struct_0(X1)
            & u1_pre_topc(k6_tmap_1(X1,X2)) = k5_tmap_1(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t104_tmap_1)).

fof(dt_k6_tmap_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( v1_pre_topc(k6_tmap_1(X1,X2))
        & v2_pre_topc(k6_tmap_1(X1,X2))
        & l1_pre_topc(k6_tmap_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_tmap_1)).

fof(t103_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( r2_hidden(X2,u1_pre_topc(X1))
          <=> u1_pre_topc(X1) = k5_tmap_1(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_tmap_1)).

fof(dt_k7_tmap_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( v1_funct_1(k7_tmap_1(X1,X2))
        & v1_funct_2(k7_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))
        & m1_subset_1(k7_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2))))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_tmap_1)).

fof(d5_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_pre_topc(X2,X1)
          <=> r2_hidden(X2,u1_pre_topc(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_pre_topc)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_tops_2)).

fof(d10_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k7_tmap_1(X1,X2) = k6_partfun1(u1_struct_0(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_tmap_1)).

fof(t171_funct_2,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k8_relset_1(X1,X1,k6_partfun1(X1),X2) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_funct_2)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_tmap_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(d3_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => k2_struct_0(X1) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(t106_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_pre_topc(X2,X1)
          <=> g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k6_tmap_1(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_tmap_1)).

fof(fc4_tmap_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ~ v2_struct_0(k6_tmap_1(X1,X2))
        & v1_pre_topc(k6_tmap_1(X1,X2))
        & v2_pre_topc(k6_tmap_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_tmap_1)).

fof(c_0_16,negated_conjecture,(
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

fof(c_0_17,plain,(
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

fof(c_0_18,negated_conjecture,
    ( ~ v2_struct_0(esk2_0)
    & v2_pre_topc(esk2_0)
    & l1_pre_topc(esk2_0)
    & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
    & ( ~ v3_pre_topc(esk3_0,esk2_0)
      | ~ v1_funct_1(k7_tmap_1(esk2_0,esk3_0))
      | ~ v1_funct_2(k7_tmap_1(esk2_0,esk3_0),u1_struct_0(esk2_0),u1_struct_0(k6_tmap_1(esk2_0,esk3_0)))
      | ~ v5_pre_topc(k7_tmap_1(esk2_0,esk3_0),esk2_0,k6_tmap_1(esk2_0,esk3_0))
      | ~ m1_subset_1(k7_tmap_1(esk2_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(k6_tmap_1(esk2_0,esk3_0))))) )
    & ( v1_funct_1(k7_tmap_1(esk2_0,esk3_0))
      | v3_pre_topc(esk3_0,esk2_0) )
    & ( v1_funct_2(k7_tmap_1(esk2_0,esk3_0),u1_struct_0(esk2_0),u1_struct_0(k6_tmap_1(esk2_0,esk3_0)))
      | v3_pre_topc(esk3_0,esk2_0) )
    & ( v5_pre_topc(k7_tmap_1(esk2_0,esk3_0),esk2_0,k6_tmap_1(esk2_0,esk3_0))
      | v3_pre_topc(esk3_0,esk2_0) )
    & ( m1_subset_1(k7_tmap_1(esk2_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(k6_tmap_1(esk2_0,esk3_0)))))
      | v3_pre_topc(esk3_0,esk2_0) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_16])])])])])).

fof(c_0_19,plain,(
    ! [X22,X23] :
      ( ( v1_pre_topc(k6_tmap_1(X22,X23))
        | v2_struct_0(X22)
        | ~ v2_pre_topc(X22)
        | ~ l1_pre_topc(X22)
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22))) )
      & ( v2_pre_topc(k6_tmap_1(X22,X23))
        | v2_struct_0(X22)
        | ~ v2_pre_topc(X22)
        | ~ l1_pre_topc(X22)
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22))) )
      & ( l1_pre_topc(k6_tmap_1(X22,X23))
        | v2_struct_0(X22)
        | ~ v2_pre_topc(X22)
        | ~ l1_pre_topc(X22)
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_tmap_1])])])])).

fof(c_0_20,plain,(
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

fof(c_0_21,plain,(
    ! [X24,X25] :
      ( ( v1_funct_1(k7_tmap_1(X24,X25))
        | v2_struct_0(X24)
        | ~ v2_pre_topc(X24)
        | ~ l1_pre_topc(X24)
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24))) )
      & ( v1_funct_2(k7_tmap_1(X24,X25),u1_struct_0(X24),u1_struct_0(k6_tmap_1(X24,X25)))
        | v2_struct_0(X24)
        | ~ v2_pre_topc(X24)
        | ~ l1_pre_topc(X24)
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24))) )
      & ( m1_subset_1(k7_tmap_1(X24,X25),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X24),u1_struct_0(k6_tmap_1(X24,X25)))))
        | v2_struct_0(X24)
        | ~ v2_pre_topc(X24)
        | ~ l1_pre_topc(X24)
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k7_tmap_1])])])])).

fof(c_0_22,plain,(
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

cnf(c_0_23,plain,
    ( u1_pre_topc(k6_tmap_1(X1,X2)) = k5_tmap_1(X1,X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_28,plain,
    ( l1_pre_topc(k6_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_29,plain,
    ( u1_struct_0(k6_tmap_1(X1,X2)) = u1_struct_0(X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_30,plain,
    ( u1_pre_topc(X2) = k5_tmap_1(X2,X1)
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,u1_pre_topc(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_31,plain,
    ( v1_funct_1(k7_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_32,plain,(
    ! [X15,X16,X17,X18] :
      ( ( ~ v5_pre_topc(X17,X15,X16)
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X16)))
        | ~ v3_pre_topc(X18,X16)
        | v3_pre_topc(k8_relset_1(u1_struct_0(X15),u1_struct_0(X16),X17,X18),X15)
        | k2_struct_0(X16) = k1_xboole_0
        | ~ v1_funct_1(X17)
        | ~ v1_funct_2(X17,u1_struct_0(X15),u1_struct_0(X16))
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),u1_struct_0(X16))))
        | ~ l1_pre_topc(X16)
        | ~ l1_pre_topc(X15) )
      & ( m1_subset_1(esk1_3(X15,X16,X17),k1_zfmisc_1(u1_struct_0(X16)))
        | v5_pre_topc(X17,X15,X16)
        | k2_struct_0(X16) = k1_xboole_0
        | ~ v1_funct_1(X17)
        | ~ v1_funct_2(X17,u1_struct_0(X15),u1_struct_0(X16))
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),u1_struct_0(X16))))
        | ~ l1_pre_topc(X16)
        | ~ l1_pre_topc(X15) )
      & ( v3_pre_topc(esk1_3(X15,X16,X17),X16)
        | v5_pre_topc(X17,X15,X16)
        | k2_struct_0(X16) = k1_xboole_0
        | ~ v1_funct_1(X17)
        | ~ v1_funct_2(X17,u1_struct_0(X15),u1_struct_0(X16))
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),u1_struct_0(X16))))
        | ~ l1_pre_topc(X16)
        | ~ l1_pre_topc(X15) )
      & ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X15),u1_struct_0(X16),X17,esk1_3(X15,X16,X17)),X15)
        | v5_pre_topc(X17,X15,X16)
        | k2_struct_0(X16) = k1_xboole_0
        | ~ v1_funct_1(X17)
        | ~ v1_funct_2(X17,u1_struct_0(X15),u1_struct_0(X16))
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),u1_struct_0(X16))))
        | ~ l1_pre_topc(X16)
        | ~ l1_pre_topc(X15) )
      & ( ~ v5_pre_topc(X17,X15,X16)
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X16)))
        | ~ v3_pre_topc(X18,X16)
        | v3_pre_topc(k8_relset_1(u1_struct_0(X15),u1_struct_0(X16),X17,X18),X15)
        | k2_struct_0(X15) != k1_xboole_0
        | ~ v1_funct_1(X17)
        | ~ v1_funct_2(X17,u1_struct_0(X15),u1_struct_0(X16))
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),u1_struct_0(X16))))
        | ~ l1_pre_topc(X16)
        | ~ l1_pre_topc(X15) )
      & ( m1_subset_1(esk1_3(X15,X16,X17),k1_zfmisc_1(u1_struct_0(X16)))
        | v5_pre_topc(X17,X15,X16)
        | k2_struct_0(X15) != k1_xboole_0
        | ~ v1_funct_1(X17)
        | ~ v1_funct_2(X17,u1_struct_0(X15),u1_struct_0(X16))
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),u1_struct_0(X16))))
        | ~ l1_pre_topc(X16)
        | ~ l1_pre_topc(X15) )
      & ( v3_pre_topc(esk1_3(X15,X16,X17),X16)
        | v5_pre_topc(X17,X15,X16)
        | k2_struct_0(X15) != k1_xboole_0
        | ~ v1_funct_1(X17)
        | ~ v1_funct_2(X17,u1_struct_0(X15),u1_struct_0(X16))
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),u1_struct_0(X16))))
        | ~ l1_pre_topc(X16)
        | ~ l1_pre_topc(X15) )
      & ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X15),u1_struct_0(X16),X17,esk1_3(X15,X16,X17)),X15)
        | v5_pre_topc(X17,X15,X16)
        | k2_struct_0(X15) != k1_xboole_0
        | ~ v1_funct_1(X17)
        | ~ v1_funct_2(X17,u1_struct_0(X15),u1_struct_0(X16))
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),u1_struct_0(X16))))
        | ~ l1_pre_topc(X16)
        | ~ l1_pre_topc(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_tops_2])])])])])).

fof(c_0_33,plain,(
    ! [X20,X21] :
      ( v2_struct_0(X20)
      | ~ v2_pre_topc(X20)
      | ~ l1_pre_topc(X20)
      | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))
      | k7_tmap_1(X20,X21) = k6_partfun1(u1_struct_0(X20)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d10_tmap_1])])])])).

cnf(c_0_34,plain,
    ( v1_funct_2(k7_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_35,plain,
    ( r2_hidden(X1,u1_pre_topc(X2))
    | ~ v3_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_36,negated_conjecture,
    ( u1_pre_topc(k6_tmap_1(esk2_0,esk3_0)) = k5_tmap_1(esk2_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25]),c_0_26])]),c_0_27])).

cnf(c_0_37,negated_conjecture,
    ( l1_pre_topc(k6_tmap_1(esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_24]),c_0_25]),c_0_26])]),c_0_27])).

cnf(c_0_38,negated_conjecture,
    ( u1_struct_0(k6_tmap_1(esk2_0,esk3_0)) = u1_struct_0(esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_24]),c_0_25]),c_0_26])]),c_0_27])).

cnf(c_0_39,negated_conjecture,
    ( k5_tmap_1(esk2_0,esk3_0) = u1_pre_topc(esk2_0)
    | ~ r2_hidden(esk3_0,u1_pre_topc(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_24]),c_0_25]),c_0_26])]),c_0_27])).

cnf(c_0_40,negated_conjecture,
    ( ~ v3_pre_topc(esk3_0,esk2_0)
    | ~ v1_funct_1(k7_tmap_1(esk2_0,esk3_0))
    | ~ v1_funct_2(k7_tmap_1(esk2_0,esk3_0),u1_struct_0(esk2_0),u1_struct_0(k6_tmap_1(esk2_0,esk3_0)))
    | ~ v5_pre_topc(k7_tmap_1(esk2_0,esk3_0),esk2_0,k6_tmap_1(esk2_0,esk3_0))
    | ~ m1_subset_1(k7_tmap_1(esk2_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(k6_tmap_1(esk2_0,esk3_0))))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_41,negated_conjecture,
    ( v1_funct_1(k7_tmap_1(esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_24]),c_0_25]),c_0_26])]),c_0_27])).

cnf(c_0_42,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_43,plain,(
    ! [X9,X10] :
      ( ~ m1_subset_1(X10,k1_zfmisc_1(X9))
      | k8_relset_1(X9,X9,k6_partfun1(X9),X10) = X10 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t171_funct_2])])).

cnf(c_0_44,plain,
    ( v2_struct_0(X1)
    | k7_tmap_1(X1,X2) = k6_partfun1(u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_45,negated_conjecture,
    ( v1_funct_2(k7_tmap_1(esk2_0,esk3_0),u1_struct_0(esk2_0),u1_struct_0(k6_tmap_1(esk2_0,esk3_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_24]),c_0_25]),c_0_26])]),c_0_27])).

cnf(c_0_46,plain,
    ( m1_subset_1(k7_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(X1,k5_tmap_1(esk2_0,esk3_0))
    | ~ v3_pre_topc(X1,k6_tmap_1(esk2_0,esk3_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37]),c_0_38])])).

cnf(c_0_48,negated_conjecture,
    ( k5_tmap_1(esk2_0,esk3_0) = u1_pre_topc(esk2_0)
    | ~ v3_pre_topc(esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_35]),c_0_26]),c_0_24])])).

fof(c_0_49,plain,(
    ! [X33,X34,X35] :
      ( v2_struct_0(X33)
      | ~ v2_pre_topc(X33)
      | ~ l1_pre_topc(X33)
      | ~ m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33)))
      | ~ m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X33,X34))))
      | X35 != X34
      | v3_pre_topc(X35,k6_tmap_1(X33,X34)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t105_tmap_1])])])])).

cnf(c_0_50,negated_conjecture,
    ( ~ v5_pre_topc(k7_tmap_1(esk2_0,esk3_0),esk2_0,k6_tmap_1(esk2_0,esk3_0))
    | ~ v1_funct_2(k7_tmap_1(esk2_0,esk3_0),u1_struct_0(esk2_0),u1_struct_0(k6_tmap_1(esk2_0,esk3_0)))
    | ~ v3_pre_topc(esk3_0,esk2_0)
    | ~ m1_subset_1(k7_tmap_1(esk2_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(k6_tmap_1(esk2_0,esk3_0))))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_41])])).

cnf(c_0_51,negated_conjecture,
    ( k2_struct_0(k6_tmap_1(esk2_0,esk3_0)) = k1_xboole_0
    | v3_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(esk2_0),X2,X3),X1)
    | ~ v5_pre_topc(X2,X1,k6_tmap_1(esk2_0,esk3_0))
    | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(esk2_0))
    | ~ v1_funct_1(X2)
    | ~ v3_pre_topc(X3,k6_tmap_1(esk2_0,esk3_0))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk2_0))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_38]),c_0_37])])).

cnf(c_0_52,plain,
    ( k8_relset_1(X2,X2,k6_partfun1(X2),X1) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_53,negated_conjecture,
    ( k6_partfun1(u1_struct_0(esk2_0)) = k7_tmap_1(esk2_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_24]),c_0_25]),c_0_26])]),c_0_27])).

cnf(c_0_54,negated_conjecture,
    ( v1_funct_2(k7_tmap_1(esk2_0,esk3_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0)) ),
    inference(rw,[status(thm)],[c_0_45,c_0_38])).

cnf(c_0_55,negated_conjecture,
    ( m1_subset_1(k7_tmap_1(esk2_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk2_0)))) ),
    inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_24]),c_0_25]),c_0_26])]),c_0_27]),c_0_38])).

cnf(c_0_56,plain,
    ( v3_pre_topc(X1,X2)
    | ~ r2_hidden(X1,u1_pre_topc(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_57,negated_conjecture,
    ( r2_hidden(X1,u1_pre_topc(esk2_0))
    | ~ v3_pre_topc(X1,k6_tmap_1(esk2_0,esk3_0))
    | ~ v3_pre_topc(esk3_0,esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_58,plain,
    ( v2_struct_0(X1)
    | v3_pre_topc(X3,k6_tmap_1(X1,X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X1,X2))))
    | X3 != X2 ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_59,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X2)))
    | v5_pre_topc(X3,X1,X2)
    | k2_struct_0(X2) = k1_xboole_0
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_60,negated_conjecture,
    ( ~ v5_pre_topc(k7_tmap_1(esk2_0,esk3_0),esk2_0,k6_tmap_1(esk2_0,esk3_0))
    | ~ v3_pre_topc(esk3_0,esk2_0)
    | ~ m1_subset_1(k7_tmap_1(esk2_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(k6_tmap_1(esk2_0,esk3_0))))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_50,c_0_45])])).

cnf(c_0_61,plain,
    ( v3_pre_topc(esk1_3(X1,X2,X3),X2)
    | v5_pre_topc(X3,X1,X2)
    | k2_struct_0(X2) = k1_xboole_0
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_62,negated_conjecture,
    ( k2_struct_0(k6_tmap_1(esk2_0,esk3_0)) = k1_xboole_0
    | v3_pre_topc(X1,esk2_0)
    | ~ v5_pre_topc(k7_tmap_1(esk2_0,esk3_0),esk2_0,k6_tmap_1(esk2_0,esk3_0))
    | ~ v3_pre_topc(X1,k6_tmap_1(esk2_0,esk3_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_53]),c_0_53]),c_0_54]),c_0_53]),c_0_41]),c_0_26]),c_0_53]),c_0_55])])).

cnf(c_0_63,negated_conjecture,
    ( v5_pre_topc(k7_tmap_1(esk2_0,esk3_0),esk2_0,k6_tmap_1(esk2_0,esk3_0))
    | v3_pre_topc(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_64,negated_conjecture,
    ( v3_pre_topc(X1,esk2_0)
    | ~ v3_pre_topc(X1,k6_tmap_1(esk2_0,esk3_0))
    | ~ v3_pre_topc(esk3_0,esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_26])])).

cnf(c_0_65,plain,
    ( v2_struct_0(X1)
    | v3_pre_topc(X2,k6_tmap_1(X1,X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X1,X2))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(er,[status(thm)],[c_0_58])).

cnf(c_0_66,plain,
    ( v5_pre_topc(X3,X1,X2)
    | k2_struct_0(X2) = k1_xboole_0
    | ~ v3_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,esk1_3(X1,X2,X3)),X1)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_67,negated_conjecture,
    ( k2_struct_0(k6_tmap_1(esk2_0,esk3_0)) = k1_xboole_0
    | v5_pre_topc(X1,X2,k6_tmap_1(esk2_0,esk3_0))
    | m1_subset_1(esk1_3(X2,k6_tmap_1(esk2_0,esk3_0),X1),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(esk2_0))
    | ~ v1_funct_1(X1)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_38]),c_0_37])])).

cnf(c_0_68,negated_conjecture,
    ( ~ v5_pre_topc(k7_tmap_1(esk2_0,esk3_0),esk2_0,k6_tmap_1(esk2_0,esk3_0))
    | ~ v3_pre_topc(esk3_0,esk2_0)
    | ~ m1_subset_1(k7_tmap_1(esk2_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk2_0)))) ),
    inference(rw,[status(thm)],[c_0_60,c_0_38])).

cnf(c_0_69,negated_conjecture,
    ( k2_struct_0(k6_tmap_1(esk2_0,esk3_0)) = k1_xboole_0
    | v5_pre_topc(X1,X2,k6_tmap_1(esk2_0,esk3_0))
    | v3_pre_topc(esk1_3(X2,k6_tmap_1(esk2_0,esk3_0),X1),k6_tmap_1(esk2_0,esk3_0))
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(esk2_0))
    | ~ v1_funct_1(X1)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_38]),c_0_37])])).

cnf(c_0_70,negated_conjecture,
    ( k2_struct_0(k6_tmap_1(esk2_0,esk3_0)) = k1_xboole_0
    | v3_pre_topc(X1,esk2_0)
    | ~ v3_pre_topc(X1,k6_tmap_1(esk2_0,esk3_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_64])).

cnf(c_0_71,negated_conjecture,
    ( v3_pre_topc(esk3_0,k6_tmap_1(esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_38]),c_0_25]),c_0_26]),c_0_24])]),c_0_27])).

cnf(c_0_72,negated_conjecture,
    ( k2_struct_0(k6_tmap_1(esk2_0,esk3_0)) = k1_xboole_0
    | v5_pre_topc(X1,X2,k6_tmap_1(esk2_0,esk3_0))
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(esk2_0))
    | ~ v1_funct_1(X1)
    | ~ v3_pre_topc(k8_relset_1(u1_struct_0(X2),u1_struct_0(esk2_0),X1,esk1_3(X2,k6_tmap_1(esk2_0,esk3_0),X1)),X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_38]),c_0_37])])).

cnf(c_0_73,negated_conjecture,
    ( k2_struct_0(k6_tmap_1(esk2_0,esk3_0)) = k1_xboole_0
    | v5_pre_topc(k7_tmap_1(esk2_0,esk3_0),esk2_0,k6_tmap_1(esk2_0,esk3_0))
    | m1_subset_1(esk1_3(esk2_0,k6_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,esk3_0)),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_55]),c_0_54]),c_0_41]),c_0_26])])).

fof(c_0_74,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | X5 != X6 )
      & ( r1_tarski(X6,X5)
        | X5 != X6 )
      & ( ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X5)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_75,plain,(
    ! [X11] :
      ( ~ l1_struct_0(X11)
      | k2_struct_0(X11) = u1_struct_0(X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

fof(c_0_76,plain,(
    ! [X14] :
      ( ~ l1_pre_topc(X14)
      | l1_struct_0(X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_77,negated_conjecture,
    ( ~ v5_pre_topc(k7_tmap_1(esk2_0,esk3_0),esk2_0,k6_tmap_1(esk2_0,esk3_0))
    | ~ v3_pre_topc(esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_68,c_0_55])])).

cnf(c_0_78,negated_conjecture,
    ( k7_tmap_1(esk2_0,X1) = k7_tmap_1(esk2_0,esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_53]),c_0_25]),c_0_26])]),c_0_27])).

cnf(c_0_79,negated_conjecture,
    ( k2_struct_0(k6_tmap_1(esk2_0,esk3_0)) = k1_xboole_0
    | v5_pre_topc(k7_tmap_1(esk2_0,esk3_0),esk2_0,k6_tmap_1(esk2_0,esk3_0))
    | v3_pre_topc(esk1_3(esk2_0,k6_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,esk3_0)),k6_tmap_1(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_55]),c_0_54]),c_0_41]),c_0_26])])).

cnf(c_0_80,negated_conjecture,
    ( k2_struct_0(k6_tmap_1(esk2_0,esk3_0)) = k1_xboole_0
    | v3_pre_topc(esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_24])])).

cnf(c_0_81,negated_conjecture,
    ( k2_struct_0(k6_tmap_1(esk2_0,esk3_0)) = k1_xboole_0
    | v5_pre_topc(k7_tmap_1(esk2_0,esk3_0),esk2_0,k6_tmap_1(esk2_0,esk3_0))
    | ~ v3_pre_topc(esk1_3(esk2_0,k6_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,esk3_0)),esk2_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_52]),c_0_53]),c_0_53]),c_0_54]),c_0_53]),c_0_41]),c_0_53]),c_0_26]),c_0_53]),c_0_55]),c_0_53])]),c_0_73])).

fof(c_0_82,plain,(
    ! [X7,X8] :
      ( ( ~ m1_subset_1(X7,k1_zfmisc_1(X8))
        | r1_tarski(X7,X8) )
      & ( ~ r1_tarski(X7,X8)
        | m1_subset_1(X7,k1_zfmisc_1(X8)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_83,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

cnf(c_0_84,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_85,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_76])).

cnf(c_0_86,negated_conjecture,
    ( ~ v5_pre_topc(k7_tmap_1(esk2_0,X1),esk2_0,k6_tmap_1(esk2_0,esk3_0))
    | ~ v3_pre_topc(esk3_0,esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_77,c_0_78])).

cnf(c_0_87,negated_conjecture,
    ( k2_struct_0(k6_tmap_1(esk2_0,esk3_0)) = k1_xboole_0
    | v5_pre_topc(k7_tmap_1(esk2_0,esk3_0),esk2_0,k6_tmap_1(esk2_0,esk3_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_79]),c_0_73]),c_0_80]),c_0_81])).

cnf(c_0_88,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_89,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_82])).

cnf(c_0_90,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_83])).

cnf(c_0_91,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_84,c_0_85])).

cnf(c_0_92,negated_conjecture,
    ( k2_struct_0(k6_tmap_1(esk2_0,esk3_0)) = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_87]),c_0_24])]),c_0_80])).

cnf(c_0_93,plain,
    ( v2_pre_topc(k6_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_94,negated_conjecture,
    ( v3_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(esk2_0),X2,X3),X1)
    | k2_struct_0(X1) != k1_xboole_0
    | ~ v5_pre_topc(X2,X1,k6_tmap_1(esk2_0,esk3_0))
    | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(esk2_0))
    | ~ v1_funct_1(X2)
    | ~ v3_pre_topc(X3,k6_tmap_1(esk2_0,esk3_0))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk2_0))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_38]),c_0_37])])).

cnf(c_0_95,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_89,c_0_90])).

cnf(c_0_96,negated_conjecture,
    ( u1_struct_0(esk2_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_92]),c_0_38]),c_0_37])])).

cnf(c_0_97,negated_conjecture,
    ( v2_pre_topc(k6_tmap_1(esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_24]),c_0_25]),c_0_26])]),c_0_27])).

fof(c_0_98,plain,(
    ! [X36,X37] :
      ( ( ~ v3_pre_topc(X37,X36)
        | g1_pre_topc(u1_struct_0(X36),u1_pre_topc(X36)) = k6_tmap_1(X36,X37)
        | ~ m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X36)))
        | v2_struct_0(X36)
        | ~ v2_pre_topc(X36)
        | ~ l1_pre_topc(X36) )
      & ( g1_pre_topc(u1_struct_0(X36),u1_pre_topc(X36)) != k6_tmap_1(X36,X37)
        | v3_pre_topc(X37,X36)
        | ~ m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X36)))
        | v2_struct_0(X36)
        | ~ v2_pre_topc(X36)
        | ~ l1_pre_topc(X36) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t106_tmap_1])])])])])).

cnf(c_0_99,negated_conjecture,
    ( v3_pre_topc(X1,esk2_0)
    | k2_struct_0(esk2_0) != k1_xboole_0
    | ~ v5_pre_topc(k7_tmap_1(esk2_0,esk3_0),esk2_0,k6_tmap_1(esk2_0,esk3_0))
    | ~ v3_pre_topc(X1,k6_tmap_1(esk2_0,esk3_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_52]),c_0_53]),c_0_53]),c_0_54]),c_0_53]),c_0_41]),c_0_26]),c_0_53]),c_0_55])])).

cnf(c_0_100,plain,
    ( k7_tmap_1(X1,u1_struct_0(X1)) = k6_partfun1(u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_95])).

cnf(c_0_101,negated_conjecture,
    ( k6_partfun1(k1_xboole_0) = k7_tmap_1(esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_53,c_0_96])).

cnf(c_0_102,negated_conjecture,
    ( v5_pre_topc(k7_tmap_1(esk2_0,X1),esk2_0,k6_tmap_1(esk2_0,esk3_0))
    | v3_pre_topc(esk3_0,esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_63,c_0_78])).

cnf(c_0_103,negated_conjecture,
    ( u1_struct_0(k6_tmap_1(k6_tmap_1(esk2_0,esk3_0),X1)) = u1_struct_0(esk2_0)
    | v2_struct_0(k6_tmap_1(esk2_0,esk3_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_38]),c_0_97]),c_0_37])])).

cnf(c_0_104,negated_conjecture,
    ( v2_struct_0(k6_tmap_1(esk2_0,esk3_0))
    | l1_pre_topc(k6_tmap_1(k6_tmap_1(esk2_0,esk3_0),X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_38]),c_0_97]),c_0_37])])).

cnf(c_0_105,plain,
    ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = k6_tmap_1(X2,X1)
    | v2_struct_0(X2)
    | ~ v3_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_98])).

cnf(c_0_106,negated_conjecture,
    ( v3_pre_topc(X1,esk2_0)
    | u1_struct_0(esk2_0) != k1_xboole_0
    | ~ v5_pre_topc(k7_tmap_1(esk2_0,esk3_0),esk2_0,k6_tmap_1(esk2_0,esk3_0))
    | ~ v3_pre_topc(X1,k6_tmap_1(esk2_0,esk3_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_91]),c_0_26])])).

cnf(c_0_107,negated_conjecture,
    ( k7_tmap_1(esk2_0,esk3_0) = k7_tmap_1(esk2_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_96]),c_0_25]),c_0_26])]),c_0_27]),c_0_101])).

cnf(c_0_108,negated_conjecture,
    ( v5_pre_topc(k7_tmap_1(esk2_0,X1),esk2_0,k6_tmap_1(esk2_0,esk3_0))
    | v3_pre_topc(esk3_0,esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(rw,[status(thm)],[c_0_102,c_0_96])).

cnf(c_0_109,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(rw,[status(thm)],[c_0_24,c_0_96])).

cnf(c_0_110,plain,
    ( v5_pre_topc(X3,X1,X2)
    | ~ v3_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,esk1_3(X1,X2,X3)),X1)
    | k2_struct_0(X1) != k1_xboole_0
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_111,negated_conjecture,
    ( u1_struct_0(k6_tmap_1(k6_tmap_1(esk2_0,esk3_0),esk3_0)) = u1_struct_0(esk2_0)
    | v2_struct_0(k6_tmap_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_103,c_0_24])).

cnf(c_0_112,negated_conjecture,
    ( v2_struct_0(k6_tmap_1(esk2_0,esk3_0))
    | l1_pre_topc(k6_tmap_1(k6_tmap_1(esk2_0,esk3_0),esk3_0)) ),
    inference(spm,[status(thm)],[c_0_104,c_0_24])).

cnf(c_0_113,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk2_0),k5_tmap_1(esk2_0,esk3_0)) = k6_tmap_1(k6_tmap_1(esk2_0,esk3_0),X1)
    | v2_struct_0(k6_tmap_1(esk2_0,esk3_0))
    | ~ v3_pre_topc(X1,k6_tmap_1(esk2_0,esk3_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_38]),c_0_97]),c_0_37])]),c_0_36])).

cnf(c_0_114,negated_conjecture,
    ( v3_pre_topc(X1,esk2_0)
    | ~ v5_pre_topc(k7_tmap_1(esk2_0,k1_xboole_0),esk2_0,k6_tmap_1(esk2_0,esk3_0))
    | ~ v3_pre_topc(X1,k6_tmap_1(esk2_0,esk3_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_106,c_0_96]),c_0_96])]),c_0_107])).

cnf(c_0_115,negated_conjecture,
    ( v5_pre_topc(k7_tmap_1(esk2_0,k1_xboole_0),esk2_0,k6_tmap_1(esk2_0,esk3_0))
    | v3_pre_topc(esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_107]),c_0_109])])).

cnf(c_0_116,negated_conjecture,
    ( v3_pre_topc(X1,esk2_0)
    | ~ v3_pre_topc(X1,k6_tmap_1(esk2_0,esk3_0))
    | ~ v3_pre_topc(esk3_0,esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(rw,[status(thm)],[c_0_64,c_0_96])).

cnf(c_0_117,plain,
    ( v3_pre_topc(esk1_3(X1,X2,X3),X2)
    | v5_pre_topc(X3,X1,X2)
    | k2_struct_0(X1) != k1_xboole_0
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_118,negated_conjecture,
    ( v2_struct_0(k6_tmap_1(esk2_0,esk3_0))
    | v5_pre_topc(X1,X2,k6_tmap_1(k6_tmap_1(esk2_0,esk3_0),esk3_0))
    | k2_struct_0(X2) != k1_xboole_0
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(esk2_0))
    | ~ v1_funct_1(X1)
    | ~ v3_pre_topc(k8_relset_1(u1_struct_0(X2),u1_struct_0(esk2_0),X1,esk1_3(X2,k6_tmap_1(k6_tmap_1(esk2_0,esk3_0),esk3_0),X1)),X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(esk2_0)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_110,c_0_111]),c_0_112])).

cnf(c_0_119,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk2_0),k5_tmap_1(esk2_0,esk3_0)) = k6_tmap_1(k6_tmap_1(esk2_0,esk3_0),esk3_0)
    | v2_struct_0(k6_tmap_1(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113,c_0_71]),c_0_24])])).

cnf(c_0_120,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)) = k6_tmap_1(esk2_0,esk3_0)
    | ~ v3_pre_topc(esk3_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_24]),c_0_25]),c_0_26])]),c_0_27])).

cnf(c_0_121,negated_conjecture,
    ( v3_pre_topc(X1,esk2_0)
    | ~ v3_pre_topc(X1,k6_tmap_1(esk2_0,esk3_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_114,c_0_115]),c_0_116])).

cnf(c_0_122,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X2)))
    | v5_pre_topc(X3,X1,X2)
    | k2_struct_0(X1) != k1_xboole_0
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_123,negated_conjecture,
    ( m1_subset_1(k7_tmap_1(esk2_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(k6_tmap_1(esk2_0,X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_78]),c_0_25]),c_0_26])]),c_0_27])).

cnf(c_0_124,negated_conjecture,
    ( v1_funct_2(k7_tmap_1(esk2_0,esk3_0),u1_struct_0(esk2_0),u1_struct_0(k6_tmap_1(esk2_0,X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_78]),c_0_25]),c_0_26])]),c_0_27])).

cnf(c_0_125,negated_conjecture,
    ( v5_pre_topc(X1,X2,k6_tmap_1(esk2_0,esk3_0))
    | v3_pre_topc(esk1_3(X2,k6_tmap_1(esk2_0,esk3_0),X1),k6_tmap_1(esk2_0,esk3_0))
    | k2_struct_0(X2) != k1_xboole_0
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(esk2_0))
    | ~ v1_funct_1(X1)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117,c_0_38]),c_0_37])])).

cnf(c_0_126,negated_conjecture,
    ( m1_subset_1(k7_tmap_1(esk2_0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk2_0))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_78]),c_0_38]),c_0_25]),c_0_26]),c_0_24])]),c_0_27])).

cnf(c_0_127,negated_conjecture,
    ( v1_funct_1(k7_tmap_1(esk2_0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_78]),c_0_25]),c_0_26]),c_0_24])]),c_0_27])).

cnf(c_0_128,negated_conjecture,
    ( v1_funct_2(k7_tmap_1(esk2_0,X1),u1_struct_0(esk2_0),u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_78]),c_0_38]),c_0_25]),c_0_26]),c_0_24])]),c_0_27])).

cnf(c_0_129,negated_conjecture,
    ( v2_struct_0(k6_tmap_1(esk2_0,esk3_0))
    | v5_pre_topc(k7_tmap_1(esk2_0,esk3_0),esk2_0,k6_tmap_1(k6_tmap_1(esk2_0,esk3_0),esk3_0))
    | k2_struct_0(esk2_0) != k1_xboole_0
    | ~ v3_pre_topc(esk1_3(esk2_0,k6_tmap_1(k6_tmap_1(esk2_0,esk3_0),esk3_0),k7_tmap_1(esk2_0,esk3_0)),esk2_0)
    | ~ m1_subset_1(esk1_3(esk2_0,k6_tmap_1(k6_tmap_1(esk2_0,esk3_0),esk3_0),k7_tmap_1(esk2_0,esk3_0)),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_118,c_0_52]),c_0_53]),c_0_53]),c_0_54]),c_0_53]),c_0_41]),c_0_53]),c_0_26]),c_0_53]),c_0_55]),c_0_53])])).

cnf(c_0_130,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)) = k6_tmap_1(k6_tmap_1(esk2_0,esk3_0),esk3_0)
    | v2_struct_0(k6_tmap_1(esk2_0,esk3_0))
    | ~ v3_pre_topc(esk3_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_119,c_0_48])).

cnf(c_0_131,negated_conjecture,
    ( g1_pre_topc(k1_xboole_0,u1_pre_topc(esk2_0)) = k6_tmap_1(esk2_0,esk3_0)
    | ~ v3_pre_topc(esk3_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_120,c_0_96])).

cnf(c_0_132,negated_conjecture,
    ( v3_pre_topc(esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_121,c_0_71]),c_0_109])])).

cnf(c_0_133,negated_conjecture,
    ( v5_pre_topc(k7_tmap_1(esk2_0,esk3_0),esk2_0,k6_tmap_1(esk2_0,X1))
    | m1_subset_1(esk1_3(esk2_0,k6_tmap_1(esk2_0,X1),k7_tmap_1(esk2_0,esk3_0)),k1_zfmisc_1(u1_struct_0(k6_tmap_1(esk2_0,X1))))
    | k2_struct_0(esk2_0) != k1_xboole_0
    | ~ l1_pre_topc(k6_tmap_1(esk2_0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_122,c_0_123]),c_0_41]),c_0_26])]),c_0_124])).

cnf(c_0_134,negated_conjecture,
    ( v5_pre_topc(k7_tmap_1(esk2_0,X1),esk2_0,k6_tmap_1(esk2_0,esk3_0))
    | v3_pre_topc(esk1_3(esk2_0,k6_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,X1)),k6_tmap_1(esk2_0,esk3_0))
    | k2_struct_0(esk2_0) != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_125,c_0_126]),c_0_26])]),c_0_127]),c_0_128])).

cnf(c_0_135,negated_conjecture,
    ( ~ v5_pre_topc(k7_tmap_1(esk2_0,X1),esk2_0,k6_tmap_1(esk2_0,esk3_0))
    | ~ v3_pre_topc(esk3_0,esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(rw,[status(thm)],[c_0_86,c_0_96])).

cnf(c_0_136,negated_conjecture,
    ( v2_struct_0(k6_tmap_1(esk2_0,esk3_0))
    | v5_pre_topc(k7_tmap_1(esk2_0,esk3_0),esk2_0,k6_tmap_1(k6_tmap_1(esk2_0,esk3_0),esk3_0))
    | u1_struct_0(esk2_0) != k1_xboole_0
    | ~ v3_pre_topc(esk1_3(esk2_0,k6_tmap_1(k6_tmap_1(esk2_0,esk3_0),esk3_0),k7_tmap_1(esk2_0,esk3_0)),esk2_0)
    | ~ m1_subset_1(esk1_3(esk2_0,k6_tmap_1(k6_tmap_1(esk2_0,esk3_0),esk3_0),k7_tmap_1(esk2_0,esk3_0)),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_129,c_0_91]),c_0_26])])).

cnf(c_0_137,negated_conjecture,
    ( g1_pre_topc(k1_xboole_0,u1_pre_topc(esk2_0)) = k6_tmap_1(k6_tmap_1(esk2_0,esk3_0),esk3_0)
    | v2_struct_0(k6_tmap_1(esk2_0,esk3_0))
    | ~ v3_pre_topc(esk3_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_130,c_0_96])).

cnf(c_0_138,negated_conjecture,
    ( g1_pre_topc(k1_xboole_0,u1_pre_topc(esk2_0)) = k6_tmap_1(esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_131,c_0_132])])).

cnf(c_0_139,negated_conjecture,
    ( ~ v5_pre_topc(k7_tmap_1(esk2_0,k1_xboole_0),esk2_0,k6_tmap_1(esk2_0,esk3_0))
    | ~ v3_pre_topc(esk3_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_77,c_0_107])).

cnf(c_0_140,negated_conjecture,
    ( v5_pre_topc(k7_tmap_1(esk2_0,esk3_0),esk2_0,k6_tmap_1(esk2_0,X1))
    | m1_subset_1(esk1_3(esk2_0,k6_tmap_1(esk2_0,X1),k7_tmap_1(esk2_0,esk3_0)),k1_zfmisc_1(u1_struct_0(k6_tmap_1(esk2_0,X1))))
    | u1_struct_0(esk2_0) != k1_xboole_0
    | ~ l1_pre_topc(k6_tmap_1(esk2_0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_133,c_0_91]),c_0_26])])).

cnf(c_0_141,negated_conjecture,
    ( l1_pre_topc(k6_tmap_1(esk2_0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_96]),c_0_25]),c_0_26])]),c_0_27])).

cnf(c_0_142,negated_conjecture,
    ( v5_pre_topc(k7_tmap_1(esk2_0,X1),esk2_0,k6_tmap_1(esk2_0,esk3_0))
    | v3_pre_topc(esk1_3(esk2_0,k6_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,X1)),k6_tmap_1(esk2_0,esk3_0))
    | u1_struct_0(esk2_0) != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_134,c_0_91]),c_0_26])])).

cnf(c_0_143,negated_conjecture,
    ( ~ v5_pre_topc(k7_tmap_1(esk2_0,X1),esk2_0,k6_tmap_1(esk2_0,esk3_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_135,c_0_132])])).

cnf(c_0_144,negated_conjecture,
    ( v2_struct_0(k6_tmap_1(esk2_0,esk3_0))
    | v5_pre_topc(k7_tmap_1(esk2_0,k1_xboole_0),esk2_0,k6_tmap_1(k6_tmap_1(esk2_0,esk3_0),esk3_0))
    | ~ v3_pre_topc(esk1_3(esk2_0,k6_tmap_1(k6_tmap_1(esk2_0,esk3_0),esk3_0),k7_tmap_1(esk2_0,k1_xboole_0)),esk2_0)
    | ~ m1_subset_1(esk1_3(esk2_0,k6_tmap_1(k6_tmap_1(esk2_0,esk3_0),esk3_0),k7_tmap_1(esk2_0,k1_xboole_0)),k1_zfmisc_1(k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_136,c_0_96]),c_0_96])]),c_0_107]),c_0_107]),c_0_107])).

cnf(c_0_145,negated_conjecture,
    ( k6_tmap_1(k6_tmap_1(esk2_0,esk3_0),esk3_0) = k6_tmap_1(esk2_0,esk3_0)
    | v2_struct_0(k6_tmap_1(esk2_0,esk3_0)) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_137,c_0_132])]),c_0_138])).

cnf(c_0_146,negated_conjecture,
    ( ~ v5_pre_topc(k7_tmap_1(esk2_0,k1_xboole_0),esk2_0,k6_tmap_1(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_139,c_0_132])])).

cnf(c_0_147,negated_conjecture,
    ( v5_pre_topc(k7_tmap_1(esk2_0,k1_xboole_0),esk2_0,k6_tmap_1(esk2_0,X1))
    | m1_subset_1(esk1_3(esk2_0,k6_tmap_1(esk2_0,X1),k7_tmap_1(esk2_0,k1_xboole_0)),k1_zfmisc_1(u1_struct_0(k6_tmap_1(esk2_0,X1))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(csr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_140,c_0_96]),c_0_96])]),c_0_107]),c_0_107]),c_0_141])).

cnf(c_0_148,negated_conjecture,
    ( v3_pre_topc(esk1_3(esk2_0,k6_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,X1)),k6_tmap_1(esk2_0,esk3_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_142,c_0_96]),c_0_96])]),c_0_143])).

cnf(c_0_149,negated_conjecture,
    ( v2_struct_0(k6_tmap_1(esk2_0,esk3_0))
    | ~ v3_pre_topc(esk1_3(esk2_0,k6_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,k1_xboole_0)),esk2_0)
    | ~ m1_subset_1(esk1_3(esk2_0,k6_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,k1_xboole_0)),k1_zfmisc_1(k1_xboole_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_144,c_0_145]),c_0_146])).

cnf(c_0_150,negated_conjecture,
    ( m1_subset_1(esk1_3(esk2_0,k6_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,k1_xboole_0)),k1_zfmisc_1(k1_xboole_0)) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_147,c_0_109]),c_0_38]),c_0_96]),c_0_146])).

cnf(c_0_151,negated_conjecture,
    ( v3_pre_topc(esk1_3(esk2_0,k6_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,k1_xboole_0)),k6_tmap_1(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_148,c_0_107]),c_0_109])])).

fof(c_0_152,plain,(
    ! [X27,X28] :
      ( ( ~ v2_struct_0(k6_tmap_1(X27,X28))
        | v2_struct_0(X27)
        | ~ v2_pre_topc(X27)
        | ~ l1_pre_topc(X27)
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27))) )
      & ( v1_pre_topc(k6_tmap_1(X27,X28))
        | v2_struct_0(X27)
        | ~ v2_pre_topc(X27)
        | ~ l1_pre_topc(X27)
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27))) )
      & ( v2_pre_topc(k6_tmap_1(X27,X28))
        | v2_struct_0(X27)
        | ~ v2_pre_topc(X27)
        | ~ l1_pre_topc(X27)
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc4_tmap_1])])])])).

cnf(c_0_153,negated_conjecture,
    ( v2_struct_0(k6_tmap_1(esk2_0,esk3_0))
    | ~ v3_pre_topc(esk1_3(esk2_0,k6_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,k1_xboole_0)),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_149,c_0_150])])).

cnf(c_0_154,negated_conjecture,
    ( v3_pre_topc(esk1_3(esk2_0,k6_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,k1_xboole_0)),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_121,c_0_151]),c_0_150])])).

cnf(c_0_155,plain,
    ( v2_struct_0(X1)
    | ~ v2_struct_0(k6_tmap_1(X1,X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_152])).

cnf(c_0_156,negated_conjecture,
    ( v2_struct_0(k6_tmap_1(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_153,c_0_154])])).

cnf(c_0_157,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_155,c_0_156]),c_0_25]),c_0_26]),c_0_96]),c_0_109])]),c_0_27]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.15/0.35  % Computer   : n025.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 19:04:51 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  # Version: 2.5pre002
% 0.15/0.35  # No SInE strategy applied
% 0.15/0.35  # Trying AutoSched0 for 299 seconds
% 1.39/1.57  # AutoSched0-Mode selected heuristic G_E___302_C18_F1_URBAN_RG_S04BN
% 1.39/1.57  # and selection function PSelectComplexExceptUniqMaxHorn.
% 1.39/1.57  #
% 1.39/1.57  # Preprocessing time       : 0.038 s
% 1.39/1.57  
% 1.39/1.57  # Proof found!
% 1.39/1.57  # SZS status Theorem
% 1.39/1.57  # SZS output start CNFRefutation
% 1.39/1.57  fof(t113_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>(((v1_funct_1(k7_tmap_1(X1,X2))&v1_funct_2(k7_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2))))&v5_pre_topc(k7_tmap_1(X1,X2),X1,k6_tmap_1(X1,X2)))&m1_subset_1(k7_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_tmap_1)).
% 1.39/1.57  fof(t104_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(u1_struct_0(k6_tmap_1(X1,X2))=u1_struct_0(X1)&u1_pre_topc(k6_tmap_1(X1,X2))=k5_tmap_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t104_tmap_1)).
% 1.39/1.57  fof(dt_k6_tmap_1, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>((v1_pre_topc(k6_tmap_1(X1,X2))&v2_pre_topc(k6_tmap_1(X1,X2)))&l1_pre_topc(k6_tmap_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_tmap_1)).
% 1.39/1.57  fof(t103_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(r2_hidden(X2,u1_pre_topc(X1))<=>u1_pre_topc(X1)=k5_tmap_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t103_tmap_1)).
% 1.39/1.57  fof(dt_k7_tmap_1, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>((v1_funct_1(k7_tmap_1(X1,X2))&v1_funct_2(k7_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2))))&m1_subset_1(k7_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_tmap_1)).
% 1.39/1.57  fof(d5_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>r2_hidden(X2,u1_pre_topc(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_pre_topc)).
% 1.39/1.57  fof(t55_tops_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(l1_pre_topc(X2)=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>((k2_struct_0(X2)=k1_xboole_0=>k2_struct_0(X1)=k1_xboole_0)=>(v5_pre_topc(X3,X1,X2)<=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))=>(v3_pre_topc(X4,X2)=>v3_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4),X1)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_tops_2)).
% 1.39/1.57  fof(d10_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k7_tmap_1(X1,X2)=k6_partfun1(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_tmap_1)).
% 1.39/1.57  fof(t171_funct_2, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k8_relset_1(X1,X1,k6_partfun1(X1),X2)=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t171_funct_2)).
% 1.39/1.57  fof(t105_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X1,X2))))=>(X3=X2=>v3_pre_topc(X3,k6_tmap_1(X1,X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t105_tmap_1)).
% 1.39/1.57  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.39/1.57  fof(d3_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>k2_struct_0(X1)=u1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 1.39/1.57  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 1.39/1.57  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 1.39/1.57  fof(t106_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))=k6_tmap_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_tmap_1)).
% 1.39/1.57  fof(fc4_tmap_1, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>((~(v2_struct_0(k6_tmap_1(X1,X2)))&v1_pre_topc(k6_tmap_1(X1,X2)))&v2_pre_topc(k6_tmap_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_tmap_1)).
% 1.39/1.57  fof(c_0_16, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>(((v1_funct_1(k7_tmap_1(X1,X2))&v1_funct_2(k7_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2))))&v5_pre_topc(k7_tmap_1(X1,X2),X1,k6_tmap_1(X1,X2)))&m1_subset_1(k7_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))))))))), inference(assume_negation,[status(cth)],[t113_tmap_1])).
% 1.39/1.57  fof(c_0_17, plain, ![X31, X32]:((u1_struct_0(k6_tmap_1(X31,X32))=u1_struct_0(X31)|~m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))|(v2_struct_0(X31)|~v2_pre_topc(X31)|~l1_pre_topc(X31)))&(u1_pre_topc(k6_tmap_1(X31,X32))=k5_tmap_1(X31,X32)|~m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))|(v2_struct_0(X31)|~v2_pre_topc(X31)|~l1_pre_topc(X31)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t104_tmap_1])])])])])).
% 1.39/1.57  fof(c_0_18, negated_conjecture, (((~v2_struct_0(esk2_0)&v2_pre_topc(esk2_0))&l1_pre_topc(esk2_0))&(m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))&((~v3_pre_topc(esk3_0,esk2_0)|(~v1_funct_1(k7_tmap_1(esk2_0,esk3_0))|~v1_funct_2(k7_tmap_1(esk2_0,esk3_0),u1_struct_0(esk2_0),u1_struct_0(k6_tmap_1(esk2_0,esk3_0)))|~v5_pre_topc(k7_tmap_1(esk2_0,esk3_0),esk2_0,k6_tmap_1(esk2_0,esk3_0))|~m1_subset_1(k7_tmap_1(esk2_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(k6_tmap_1(esk2_0,esk3_0)))))))&((((v1_funct_1(k7_tmap_1(esk2_0,esk3_0))|v3_pre_topc(esk3_0,esk2_0))&(v1_funct_2(k7_tmap_1(esk2_0,esk3_0),u1_struct_0(esk2_0),u1_struct_0(k6_tmap_1(esk2_0,esk3_0)))|v3_pre_topc(esk3_0,esk2_0)))&(v5_pre_topc(k7_tmap_1(esk2_0,esk3_0),esk2_0,k6_tmap_1(esk2_0,esk3_0))|v3_pre_topc(esk3_0,esk2_0)))&(m1_subset_1(k7_tmap_1(esk2_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(k6_tmap_1(esk2_0,esk3_0)))))|v3_pre_topc(esk3_0,esk2_0)))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_16])])])])])).
% 1.39/1.57  fof(c_0_19, plain, ![X22, X23]:(((v1_pre_topc(k6_tmap_1(X22,X23))|(v2_struct_0(X22)|~v2_pre_topc(X22)|~l1_pre_topc(X22)|~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))))&(v2_pre_topc(k6_tmap_1(X22,X23))|(v2_struct_0(X22)|~v2_pre_topc(X22)|~l1_pre_topc(X22)|~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22))))))&(l1_pre_topc(k6_tmap_1(X22,X23))|(v2_struct_0(X22)|~v2_pre_topc(X22)|~l1_pre_topc(X22)|~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_tmap_1])])])])).
% 1.39/1.57  fof(c_0_20, plain, ![X29, X30]:((~r2_hidden(X30,u1_pre_topc(X29))|u1_pre_topc(X29)=k5_tmap_1(X29,X30)|~m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))|(v2_struct_0(X29)|~v2_pre_topc(X29)|~l1_pre_topc(X29)))&(u1_pre_topc(X29)!=k5_tmap_1(X29,X30)|r2_hidden(X30,u1_pre_topc(X29))|~m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))|(v2_struct_0(X29)|~v2_pre_topc(X29)|~l1_pre_topc(X29)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t103_tmap_1])])])])])).
% 1.39/1.57  fof(c_0_21, plain, ![X24, X25]:(((v1_funct_1(k7_tmap_1(X24,X25))|(v2_struct_0(X24)|~v2_pre_topc(X24)|~l1_pre_topc(X24)|~m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))))&(v1_funct_2(k7_tmap_1(X24,X25),u1_struct_0(X24),u1_struct_0(k6_tmap_1(X24,X25)))|(v2_struct_0(X24)|~v2_pre_topc(X24)|~l1_pre_topc(X24)|~m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24))))))&(m1_subset_1(k7_tmap_1(X24,X25),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X24),u1_struct_0(k6_tmap_1(X24,X25)))))|(v2_struct_0(X24)|~v2_pre_topc(X24)|~l1_pre_topc(X24)|~m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k7_tmap_1])])])])).
% 1.39/1.57  fof(c_0_22, plain, ![X12, X13]:((~v3_pre_topc(X13,X12)|r2_hidden(X13,u1_pre_topc(X12))|~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))|~l1_pre_topc(X12))&(~r2_hidden(X13,u1_pre_topc(X12))|v3_pre_topc(X13,X12)|~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))|~l1_pre_topc(X12))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_pre_topc])])])])).
% 1.39/1.57  cnf(c_0_23, plain, (u1_pre_topc(k6_tmap_1(X1,X2))=k5_tmap_1(X1,X2)|v2_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 1.39/1.57  cnf(c_0_24, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 1.39/1.57  cnf(c_0_25, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 1.39/1.57  cnf(c_0_26, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 1.39/1.57  cnf(c_0_27, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 1.39/1.57  cnf(c_0_28, plain, (l1_pre_topc(k6_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 1.39/1.57  cnf(c_0_29, plain, (u1_struct_0(k6_tmap_1(X1,X2))=u1_struct_0(X1)|v2_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 1.39/1.57  cnf(c_0_30, plain, (u1_pre_topc(X2)=k5_tmap_1(X2,X1)|v2_struct_0(X2)|~r2_hidden(X1,u1_pre_topc(X2))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 1.39/1.57  cnf(c_0_31, plain, (v1_funct_1(k7_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 1.39/1.57  fof(c_0_32, plain, ![X15, X16, X17, X18]:(((~v5_pre_topc(X17,X15,X16)|(~m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X16)))|(~v3_pre_topc(X18,X16)|v3_pre_topc(k8_relset_1(u1_struct_0(X15),u1_struct_0(X16),X17,X18),X15)))|k2_struct_0(X16)=k1_xboole_0|(~v1_funct_1(X17)|~v1_funct_2(X17,u1_struct_0(X15),u1_struct_0(X16))|~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),u1_struct_0(X16)))))|~l1_pre_topc(X16)|~l1_pre_topc(X15))&((m1_subset_1(esk1_3(X15,X16,X17),k1_zfmisc_1(u1_struct_0(X16)))|v5_pre_topc(X17,X15,X16)|k2_struct_0(X16)=k1_xboole_0|(~v1_funct_1(X17)|~v1_funct_2(X17,u1_struct_0(X15),u1_struct_0(X16))|~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),u1_struct_0(X16)))))|~l1_pre_topc(X16)|~l1_pre_topc(X15))&((v3_pre_topc(esk1_3(X15,X16,X17),X16)|v5_pre_topc(X17,X15,X16)|k2_struct_0(X16)=k1_xboole_0|(~v1_funct_1(X17)|~v1_funct_2(X17,u1_struct_0(X15),u1_struct_0(X16))|~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),u1_struct_0(X16)))))|~l1_pre_topc(X16)|~l1_pre_topc(X15))&(~v3_pre_topc(k8_relset_1(u1_struct_0(X15),u1_struct_0(X16),X17,esk1_3(X15,X16,X17)),X15)|v5_pre_topc(X17,X15,X16)|k2_struct_0(X16)=k1_xboole_0|(~v1_funct_1(X17)|~v1_funct_2(X17,u1_struct_0(X15),u1_struct_0(X16))|~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),u1_struct_0(X16)))))|~l1_pre_topc(X16)|~l1_pre_topc(X15)))))&((~v5_pre_topc(X17,X15,X16)|(~m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X16)))|(~v3_pre_topc(X18,X16)|v3_pre_topc(k8_relset_1(u1_struct_0(X15),u1_struct_0(X16),X17,X18),X15)))|k2_struct_0(X15)!=k1_xboole_0|(~v1_funct_1(X17)|~v1_funct_2(X17,u1_struct_0(X15),u1_struct_0(X16))|~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),u1_struct_0(X16)))))|~l1_pre_topc(X16)|~l1_pre_topc(X15))&((m1_subset_1(esk1_3(X15,X16,X17),k1_zfmisc_1(u1_struct_0(X16)))|v5_pre_topc(X17,X15,X16)|k2_struct_0(X15)!=k1_xboole_0|(~v1_funct_1(X17)|~v1_funct_2(X17,u1_struct_0(X15),u1_struct_0(X16))|~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),u1_struct_0(X16)))))|~l1_pre_topc(X16)|~l1_pre_topc(X15))&((v3_pre_topc(esk1_3(X15,X16,X17),X16)|v5_pre_topc(X17,X15,X16)|k2_struct_0(X15)!=k1_xboole_0|(~v1_funct_1(X17)|~v1_funct_2(X17,u1_struct_0(X15),u1_struct_0(X16))|~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),u1_struct_0(X16)))))|~l1_pre_topc(X16)|~l1_pre_topc(X15))&(~v3_pre_topc(k8_relset_1(u1_struct_0(X15),u1_struct_0(X16),X17,esk1_3(X15,X16,X17)),X15)|v5_pre_topc(X17,X15,X16)|k2_struct_0(X15)!=k1_xboole_0|(~v1_funct_1(X17)|~v1_funct_2(X17,u1_struct_0(X15),u1_struct_0(X16))|~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),u1_struct_0(X16)))))|~l1_pre_topc(X16)|~l1_pre_topc(X15)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_tops_2])])])])])).
% 1.39/1.57  fof(c_0_33, plain, ![X20, X21]:(v2_struct_0(X20)|~v2_pre_topc(X20)|~l1_pre_topc(X20)|(~m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))|k7_tmap_1(X20,X21)=k6_partfun1(u1_struct_0(X20)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d10_tmap_1])])])])).
% 1.39/1.57  cnf(c_0_34, plain, (v1_funct_2(k7_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 1.39/1.57  cnf(c_0_35, plain, (r2_hidden(X1,u1_pre_topc(X2))|~v3_pre_topc(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 1.39/1.57  cnf(c_0_36, negated_conjecture, (u1_pre_topc(k6_tmap_1(esk2_0,esk3_0))=k5_tmap_1(esk2_0,esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_25]), c_0_26])]), c_0_27])).
% 1.39/1.57  cnf(c_0_37, negated_conjecture, (l1_pre_topc(k6_tmap_1(esk2_0,esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_24]), c_0_25]), c_0_26])]), c_0_27])).
% 1.39/1.57  cnf(c_0_38, negated_conjecture, (u1_struct_0(k6_tmap_1(esk2_0,esk3_0))=u1_struct_0(esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_24]), c_0_25]), c_0_26])]), c_0_27])).
% 1.39/1.57  cnf(c_0_39, negated_conjecture, (k5_tmap_1(esk2_0,esk3_0)=u1_pre_topc(esk2_0)|~r2_hidden(esk3_0,u1_pre_topc(esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_24]), c_0_25]), c_0_26])]), c_0_27])).
% 1.39/1.57  cnf(c_0_40, negated_conjecture, (~v3_pre_topc(esk3_0,esk2_0)|~v1_funct_1(k7_tmap_1(esk2_0,esk3_0))|~v1_funct_2(k7_tmap_1(esk2_0,esk3_0),u1_struct_0(esk2_0),u1_struct_0(k6_tmap_1(esk2_0,esk3_0)))|~v5_pre_topc(k7_tmap_1(esk2_0,esk3_0),esk2_0,k6_tmap_1(esk2_0,esk3_0))|~m1_subset_1(k7_tmap_1(esk2_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(k6_tmap_1(esk2_0,esk3_0)))))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 1.39/1.57  cnf(c_0_41, negated_conjecture, (v1_funct_1(k7_tmap_1(esk2_0,esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_24]), c_0_25]), c_0_26])]), c_0_27])).
% 1.39/1.57  cnf(c_0_42, plain, (v3_pre_topc(k8_relset_1(u1_struct_0(X2),u1_struct_0(X3),X1,X4),X2)|k2_struct_0(X3)=k1_xboole_0|~v5_pre_topc(X1,X2,X3)|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))|~v3_pre_topc(X4,X3)|~v1_funct_1(X1)|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))|~l1_pre_topc(X3)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 1.39/1.57  fof(c_0_43, plain, ![X9, X10]:(~m1_subset_1(X10,k1_zfmisc_1(X9))|k8_relset_1(X9,X9,k6_partfun1(X9),X10)=X10), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t171_funct_2])])).
% 1.39/1.57  cnf(c_0_44, plain, (v2_struct_0(X1)|k7_tmap_1(X1,X2)=k6_partfun1(u1_struct_0(X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 1.39/1.57  cnf(c_0_45, negated_conjecture, (v1_funct_2(k7_tmap_1(esk2_0,esk3_0),u1_struct_0(esk2_0),u1_struct_0(k6_tmap_1(esk2_0,esk3_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_24]), c_0_25]), c_0_26])]), c_0_27])).
% 1.39/1.57  cnf(c_0_46, plain, (m1_subset_1(k7_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 1.39/1.57  cnf(c_0_47, negated_conjecture, (r2_hidden(X1,k5_tmap_1(esk2_0,esk3_0))|~v3_pre_topc(X1,k6_tmap_1(esk2_0,esk3_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_37]), c_0_38])])).
% 1.39/1.57  cnf(c_0_48, negated_conjecture, (k5_tmap_1(esk2_0,esk3_0)=u1_pre_topc(esk2_0)|~v3_pre_topc(esk3_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_35]), c_0_26]), c_0_24])])).
% 1.39/1.57  fof(c_0_49, plain, ![X33, X34, X35]:(v2_struct_0(X33)|~v2_pre_topc(X33)|~l1_pre_topc(X33)|(~m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33)))|(~m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X33,X34))))|(X35!=X34|v3_pre_topc(X35,k6_tmap_1(X33,X34)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t105_tmap_1])])])])).
% 1.39/1.57  cnf(c_0_50, negated_conjecture, (~v5_pre_topc(k7_tmap_1(esk2_0,esk3_0),esk2_0,k6_tmap_1(esk2_0,esk3_0))|~v1_funct_2(k7_tmap_1(esk2_0,esk3_0),u1_struct_0(esk2_0),u1_struct_0(k6_tmap_1(esk2_0,esk3_0)))|~v3_pre_topc(esk3_0,esk2_0)|~m1_subset_1(k7_tmap_1(esk2_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(k6_tmap_1(esk2_0,esk3_0)))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_41])])).
% 1.39/1.57  cnf(c_0_51, negated_conjecture, (k2_struct_0(k6_tmap_1(esk2_0,esk3_0))=k1_xboole_0|v3_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(esk2_0),X2,X3),X1)|~v5_pre_topc(X2,X1,k6_tmap_1(esk2_0,esk3_0))|~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(esk2_0))|~v1_funct_1(X2)|~v3_pre_topc(X3,k6_tmap_1(esk2_0,esk3_0))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk2_0))))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_38]), c_0_37])])).
% 1.39/1.57  cnf(c_0_52, plain, (k8_relset_1(X2,X2,k6_partfun1(X2),X1)=X1|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 1.39/1.57  cnf(c_0_53, negated_conjecture, (k6_partfun1(u1_struct_0(esk2_0))=k7_tmap_1(esk2_0,esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_24]), c_0_25]), c_0_26])]), c_0_27])).
% 1.39/1.57  cnf(c_0_54, negated_conjecture, (v1_funct_2(k7_tmap_1(esk2_0,esk3_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0))), inference(rw,[status(thm)],[c_0_45, c_0_38])).
% 1.39/1.57  cnf(c_0_55, negated_conjecture, (m1_subset_1(k7_tmap_1(esk2_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk2_0))))), inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_24]), c_0_25]), c_0_26])]), c_0_27]), c_0_38])).
% 1.39/1.57  cnf(c_0_56, plain, (v3_pre_topc(X1,X2)|~r2_hidden(X1,u1_pre_topc(X2))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 1.39/1.57  cnf(c_0_57, negated_conjecture, (r2_hidden(X1,u1_pre_topc(esk2_0))|~v3_pre_topc(X1,k6_tmap_1(esk2_0,esk3_0))|~v3_pre_topc(esk3_0,esk2_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 1.39/1.57  cnf(c_0_58, plain, (v2_struct_0(X1)|v3_pre_topc(X3,k6_tmap_1(X1,X2))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X1,X2))))|X3!=X2), inference(split_conjunct,[status(thm)],[c_0_49])).
% 1.39/1.57  cnf(c_0_59, plain, (m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X2)))|v5_pre_topc(X3,X1,X2)|k2_struct_0(X2)=k1_xboole_0|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 1.39/1.57  cnf(c_0_60, negated_conjecture, (~v5_pre_topc(k7_tmap_1(esk2_0,esk3_0),esk2_0,k6_tmap_1(esk2_0,esk3_0))|~v3_pre_topc(esk3_0,esk2_0)|~m1_subset_1(k7_tmap_1(esk2_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(k6_tmap_1(esk2_0,esk3_0)))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_50, c_0_45])])).
% 1.39/1.57  cnf(c_0_61, plain, (v3_pre_topc(esk1_3(X1,X2,X3),X2)|v5_pre_topc(X3,X1,X2)|k2_struct_0(X2)=k1_xboole_0|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 1.39/1.57  cnf(c_0_62, negated_conjecture, (k2_struct_0(k6_tmap_1(esk2_0,esk3_0))=k1_xboole_0|v3_pre_topc(X1,esk2_0)|~v5_pre_topc(k7_tmap_1(esk2_0,esk3_0),esk2_0,k6_tmap_1(esk2_0,esk3_0))|~v3_pre_topc(X1,k6_tmap_1(esk2_0,esk3_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_53]), c_0_53]), c_0_54]), c_0_53]), c_0_41]), c_0_26]), c_0_53]), c_0_55])])).
% 1.39/1.57  cnf(c_0_63, negated_conjecture, (v5_pre_topc(k7_tmap_1(esk2_0,esk3_0),esk2_0,k6_tmap_1(esk2_0,esk3_0))|v3_pre_topc(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 1.39/1.57  cnf(c_0_64, negated_conjecture, (v3_pre_topc(X1,esk2_0)|~v3_pre_topc(X1,k6_tmap_1(esk2_0,esk3_0))|~v3_pre_topc(esk3_0,esk2_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_26])])).
% 1.39/1.57  cnf(c_0_65, plain, (v2_struct_0(X1)|v3_pre_topc(X2,k6_tmap_1(X1,X2))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X1,X2))))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(er,[status(thm)],[c_0_58])).
% 1.39/1.57  cnf(c_0_66, plain, (v5_pre_topc(X3,X1,X2)|k2_struct_0(X2)=k1_xboole_0|~v3_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,esk1_3(X1,X2,X3)),X1)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 1.39/1.57  cnf(c_0_67, negated_conjecture, (k2_struct_0(k6_tmap_1(esk2_0,esk3_0))=k1_xboole_0|v5_pre_topc(X1,X2,k6_tmap_1(esk2_0,esk3_0))|m1_subset_1(esk1_3(X2,k6_tmap_1(esk2_0,esk3_0),X1),k1_zfmisc_1(u1_struct_0(esk2_0)))|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(esk2_0))|~v1_funct_1(X1)|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_38]), c_0_37])])).
% 1.39/1.57  cnf(c_0_68, negated_conjecture, (~v5_pre_topc(k7_tmap_1(esk2_0,esk3_0),esk2_0,k6_tmap_1(esk2_0,esk3_0))|~v3_pre_topc(esk3_0,esk2_0)|~m1_subset_1(k7_tmap_1(esk2_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk2_0))))), inference(rw,[status(thm)],[c_0_60, c_0_38])).
% 1.39/1.57  cnf(c_0_69, negated_conjecture, (k2_struct_0(k6_tmap_1(esk2_0,esk3_0))=k1_xboole_0|v5_pre_topc(X1,X2,k6_tmap_1(esk2_0,esk3_0))|v3_pre_topc(esk1_3(X2,k6_tmap_1(esk2_0,esk3_0),X1),k6_tmap_1(esk2_0,esk3_0))|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(esk2_0))|~v1_funct_1(X1)|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_38]), c_0_37])])).
% 1.39/1.57  cnf(c_0_70, negated_conjecture, (k2_struct_0(k6_tmap_1(esk2_0,esk3_0))=k1_xboole_0|v3_pre_topc(X1,esk2_0)|~v3_pre_topc(X1,k6_tmap_1(esk2_0,esk3_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_64])).
% 1.39/1.57  cnf(c_0_71, negated_conjecture, (v3_pre_topc(esk3_0,k6_tmap_1(esk2_0,esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_38]), c_0_25]), c_0_26]), c_0_24])]), c_0_27])).
% 1.39/1.57  cnf(c_0_72, negated_conjecture, (k2_struct_0(k6_tmap_1(esk2_0,esk3_0))=k1_xboole_0|v5_pre_topc(X1,X2,k6_tmap_1(esk2_0,esk3_0))|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(esk2_0))|~v1_funct_1(X1)|~v3_pre_topc(k8_relset_1(u1_struct_0(X2),u1_struct_0(esk2_0),X1,esk1_3(X2,k6_tmap_1(esk2_0,esk3_0),X1)),X2)|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_38]), c_0_37])])).
% 1.39/1.57  cnf(c_0_73, negated_conjecture, (k2_struct_0(k6_tmap_1(esk2_0,esk3_0))=k1_xboole_0|v5_pre_topc(k7_tmap_1(esk2_0,esk3_0),esk2_0,k6_tmap_1(esk2_0,esk3_0))|m1_subset_1(esk1_3(esk2_0,k6_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,esk3_0)),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_55]), c_0_54]), c_0_41]), c_0_26])])).
% 1.39/1.57  fof(c_0_74, plain, ![X5, X6]:(((r1_tarski(X5,X6)|X5!=X6)&(r1_tarski(X6,X5)|X5!=X6))&(~r1_tarski(X5,X6)|~r1_tarski(X6,X5)|X5=X6)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 1.39/1.57  fof(c_0_75, plain, ![X11]:(~l1_struct_0(X11)|k2_struct_0(X11)=u1_struct_0(X11)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).
% 1.39/1.57  fof(c_0_76, plain, ![X14]:(~l1_pre_topc(X14)|l1_struct_0(X14)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 1.39/1.57  cnf(c_0_77, negated_conjecture, (~v5_pre_topc(k7_tmap_1(esk2_0,esk3_0),esk2_0,k6_tmap_1(esk2_0,esk3_0))|~v3_pre_topc(esk3_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_68, c_0_55])])).
% 1.39/1.57  cnf(c_0_78, negated_conjecture, (k7_tmap_1(esk2_0,X1)=k7_tmap_1(esk2_0,esk3_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_53]), c_0_25]), c_0_26])]), c_0_27])).
% 1.39/1.57  cnf(c_0_79, negated_conjecture, (k2_struct_0(k6_tmap_1(esk2_0,esk3_0))=k1_xboole_0|v5_pre_topc(k7_tmap_1(esk2_0,esk3_0),esk2_0,k6_tmap_1(esk2_0,esk3_0))|v3_pre_topc(esk1_3(esk2_0,k6_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,esk3_0)),k6_tmap_1(esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_55]), c_0_54]), c_0_41]), c_0_26])])).
% 1.39/1.57  cnf(c_0_80, negated_conjecture, (k2_struct_0(k6_tmap_1(esk2_0,esk3_0))=k1_xboole_0|v3_pre_topc(esk3_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_71]), c_0_24])])).
% 1.39/1.57  cnf(c_0_81, negated_conjecture, (k2_struct_0(k6_tmap_1(esk2_0,esk3_0))=k1_xboole_0|v5_pre_topc(k7_tmap_1(esk2_0,esk3_0),esk2_0,k6_tmap_1(esk2_0,esk3_0))|~v3_pre_topc(esk1_3(esk2_0,k6_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,esk3_0)),esk2_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_52]), c_0_53]), c_0_53]), c_0_54]), c_0_53]), c_0_41]), c_0_53]), c_0_26]), c_0_53]), c_0_55]), c_0_53])]), c_0_73])).
% 1.39/1.57  fof(c_0_82, plain, ![X7, X8]:((~m1_subset_1(X7,k1_zfmisc_1(X8))|r1_tarski(X7,X8))&(~r1_tarski(X7,X8)|m1_subset_1(X7,k1_zfmisc_1(X8)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 1.39/1.57  cnf(c_0_83, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_74])).
% 1.39/1.57  cnf(c_0_84, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_75])).
% 1.39/1.57  cnf(c_0_85, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_76])).
% 1.39/1.57  cnf(c_0_86, negated_conjecture, (~v5_pre_topc(k7_tmap_1(esk2_0,X1),esk2_0,k6_tmap_1(esk2_0,esk3_0))|~v3_pre_topc(esk3_0,esk2_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(spm,[status(thm)],[c_0_77, c_0_78])).
% 1.39/1.57  cnf(c_0_87, negated_conjecture, (k2_struct_0(k6_tmap_1(esk2_0,esk3_0))=k1_xboole_0|v5_pre_topc(k7_tmap_1(esk2_0,esk3_0),esk2_0,k6_tmap_1(esk2_0,esk3_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_79]), c_0_73]), c_0_80]), c_0_81])).
% 1.39/1.57  cnf(c_0_88, plain, (v3_pre_topc(k8_relset_1(u1_struct_0(X2),u1_struct_0(X3),X1,X4),X2)|~v5_pre_topc(X1,X2,X3)|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))|~v3_pre_topc(X4,X3)|k2_struct_0(X2)!=k1_xboole_0|~v1_funct_1(X1)|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))|~l1_pre_topc(X3)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 1.39/1.57  cnf(c_0_89, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_82])).
% 1.39/1.57  cnf(c_0_90, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_83])).
% 1.39/1.57  cnf(c_0_91, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_84, c_0_85])).
% 1.39/1.57  cnf(c_0_92, negated_conjecture, (k2_struct_0(k6_tmap_1(esk2_0,esk3_0))=k1_xboole_0), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_87]), c_0_24])]), c_0_80])).
% 1.39/1.57  cnf(c_0_93, plain, (v2_pre_topc(k6_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 1.39/1.57  cnf(c_0_94, negated_conjecture, (v3_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(esk2_0),X2,X3),X1)|k2_struct_0(X1)!=k1_xboole_0|~v5_pre_topc(X2,X1,k6_tmap_1(esk2_0,esk3_0))|~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(esk2_0))|~v1_funct_1(X2)|~v3_pre_topc(X3,k6_tmap_1(esk2_0,esk3_0))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk2_0))))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_38]), c_0_37])])).
% 1.39/1.57  cnf(c_0_95, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_89, c_0_90])).
% 1.39/1.57  cnf(c_0_96, negated_conjecture, (u1_struct_0(esk2_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_92]), c_0_38]), c_0_37])])).
% 1.39/1.57  cnf(c_0_97, negated_conjecture, (v2_pre_topc(k6_tmap_1(esk2_0,esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_24]), c_0_25]), c_0_26])]), c_0_27])).
% 1.39/1.57  fof(c_0_98, plain, ![X36, X37]:((~v3_pre_topc(X37,X36)|g1_pre_topc(u1_struct_0(X36),u1_pre_topc(X36))=k6_tmap_1(X36,X37)|~m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X36)))|(v2_struct_0(X36)|~v2_pre_topc(X36)|~l1_pre_topc(X36)))&(g1_pre_topc(u1_struct_0(X36),u1_pre_topc(X36))!=k6_tmap_1(X36,X37)|v3_pre_topc(X37,X36)|~m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X36)))|(v2_struct_0(X36)|~v2_pre_topc(X36)|~l1_pre_topc(X36)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t106_tmap_1])])])])])).
% 1.39/1.57  cnf(c_0_99, negated_conjecture, (v3_pre_topc(X1,esk2_0)|k2_struct_0(esk2_0)!=k1_xboole_0|~v5_pre_topc(k7_tmap_1(esk2_0,esk3_0),esk2_0,k6_tmap_1(esk2_0,esk3_0))|~v3_pre_topc(X1,k6_tmap_1(esk2_0,esk3_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_52]), c_0_53]), c_0_53]), c_0_54]), c_0_53]), c_0_41]), c_0_26]), c_0_53]), c_0_55])])).
% 1.39/1.57  cnf(c_0_100, plain, (k7_tmap_1(X1,u1_struct_0(X1))=k6_partfun1(u1_struct_0(X1))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_44, c_0_95])).
% 1.39/1.57  cnf(c_0_101, negated_conjecture, (k6_partfun1(k1_xboole_0)=k7_tmap_1(esk2_0,esk3_0)), inference(rw,[status(thm)],[c_0_53, c_0_96])).
% 1.39/1.57  cnf(c_0_102, negated_conjecture, (v5_pre_topc(k7_tmap_1(esk2_0,X1),esk2_0,k6_tmap_1(esk2_0,esk3_0))|v3_pre_topc(esk3_0,esk2_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(spm,[status(thm)],[c_0_63, c_0_78])).
% 1.39/1.57  cnf(c_0_103, negated_conjecture, (u1_struct_0(k6_tmap_1(k6_tmap_1(esk2_0,esk3_0),X1))=u1_struct_0(esk2_0)|v2_struct_0(k6_tmap_1(esk2_0,esk3_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_38]), c_0_97]), c_0_37])])).
% 1.39/1.57  cnf(c_0_104, negated_conjecture, (v2_struct_0(k6_tmap_1(esk2_0,esk3_0))|l1_pre_topc(k6_tmap_1(k6_tmap_1(esk2_0,esk3_0),X1))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_38]), c_0_97]), c_0_37])])).
% 1.39/1.57  cnf(c_0_105, plain, (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))=k6_tmap_1(X2,X1)|v2_struct_0(X2)|~v3_pre_topc(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_98])).
% 1.39/1.57  cnf(c_0_106, negated_conjecture, (v3_pre_topc(X1,esk2_0)|u1_struct_0(esk2_0)!=k1_xboole_0|~v5_pre_topc(k7_tmap_1(esk2_0,esk3_0),esk2_0,k6_tmap_1(esk2_0,esk3_0))|~v3_pre_topc(X1,k6_tmap_1(esk2_0,esk3_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_91]), c_0_26])])).
% 1.39/1.57  cnf(c_0_107, negated_conjecture, (k7_tmap_1(esk2_0,esk3_0)=k7_tmap_1(esk2_0,k1_xboole_0)), inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_96]), c_0_25]), c_0_26])]), c_0_27]), c_0_101])).
% 1.39/1.57  cnf(c_0_108, negated_conjecture, (v5_pre_topc(k7_tmap_1(esk2_0,X1),esk2_0,k6_tmap_1(esk2_0,esk3_0))|v3_pre_topc(esk3_0,esk2_0)|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(rw,[status(thm)],[c_0_102, c_0_96])).
% 1.39/1.57  cnf(c_0_109, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k1_xboole_0))), inference(rw,[status(thm)],[c_0_24, c_0_96])).
% 1.39/1.57  cnf(c_0_110, plain, (v5_pre_topc(X3,X1,X2)|~v3_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,esk1_3(X1,X2,X3)),X1)|k2_struct_0(X1)!=k1_xboole_0|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 1.39/1.57  cnf(c_0_111, negated_conjecture, (u1_struct_0(k6_tmap_1(k6_tmap_1(esk2_0,esk3_0),esk3_0))=u1_struct_0(esk2_0)|v2_struct_0(k6_tmap_1(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_103, c_0_24])).
% 1.39/1.57  cnf(c_0_112, negated_conjecture, (v2_struct_0(k6_tmap_1(esk2_0,esk3_0))|l1_pre_topc(k6_tmap_1(k6_tmap_1(esk2_0,esk3_0),esk3_0))), inference(spm,[status(thm)],[c_0_104, c_0_24])).
% 1.39/1.57  cnf(c_0_113, negated_conjecture, (g1_pre_topc(u1_struct_0(esk2_0),k5_tmap_1(esk2_0,esk3_0))=k6_tmap_1(k6_tmap_1(esk2_0,esk3_0),X1)|v2_struct_0(k6_tmap_1(esk2_0,esk3_0))|~v3_pre_topc(X1,k6_tmap_1(esk2_0,esk3_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105, c_0_38]), c_0_97]), c_0_37])]), c_0_36])).
% 1.39/1.57  cnf(c_0_114, negated_conjecture, (v3_pre_topc(X1,esk2_0)|~v5_pre_topc(k7_tmap_1(esk2_0,k1_xboole_0),esk2_0,k6_tmap_1(esk2_0,esk3_0))|~v3_pre_topc(X1,k6_tmap_1(esk2_0,esk3_0))|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_106, c_0_96]), c_0_96])]), c_0_107])).
% 1.39/1.57  cnf(c_0_115, negated_conjecture, (v5_pre_topc(k7_tmap_1(esk2_0,k1_xboole_0),esk2_0,k6_tmap_1(esk2_0,esk3_0))|v3_pre_topc(esk3_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108, c_0_107]), c_0_109])])).
% 1.39/1.57  cnf(c_0_116, negated_conjecture, (v3_pre_topc(X1,esk2_0)|~v3_pre_topc(X1,k6_tmap_1(esk2_0,esk3_0))|~v3_pre_topc(esk3_0,esk2_0)|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(rw,[status(thm)],[c_0_64, c_0_96])).
% 1.39/1.57  cnf(c_0_117, plain, (v3_pre_topc(esk1_3(X1,X2,X3),X2)|v5_pre_topc(X3,X1,X2)|k2_struct_0(X1)!=k1_xboole_0|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 1.39/1.57  cnf(c_0_118, negated_conjecture, (v2_struct_0(k6_tmap_1(esk2_0,esk3_0))|v5_pre_topc(X1,X2,k6_tmap_1(k6_tmap_1(esk2_0,esk3_0),esk3_0))|k2_struct_0(X2)!=k1_xboole_0|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(esk2_0))|~v1_funct_1(X1)|~v3_pre_topc(k8_relset_1(u1_struct_0(X2),u1_struct_0(esk2_0),X1,esk1_3(X2,k6_tmap_1(k6_tmap_1(esk2_0,esk3_0),esk3_0),X1)),X2)|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(esk2_0))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_110, c_0_111]), c_0_112])).
% 1.39/1.57  cnf(c_0_119, negated_conjecture, (g1_pre_topc(u1_struct_0(esk2_0),k5_tmap_1(esk2_0,esk3_0))=k6_tmap_1(k6_tmap_1(esk2_0,esk3_0),esk3_0)|v2_struct_0(k6_tmap_1(esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113, c_0_71]), c_0_24])])).
% 1.39/1.57  cnf(c_0_120, negated_conjecture, (g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))=k6_tmap_1(esk2_0,esk3_0)|~v3_pre_topc(esk3_0,esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105, c_0_24]), c_0_25]), c_0_26])]), c_0_27])).
% 1.39/1.57  cnf(c_0_121, negated_conjecture, (v3_pre_topc(X1,esk2_0)|~v3_pre_topc(X1,k6_tmap_1(esk2_0,esk3_0))|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_114, c_0_115]), c_0_116])).
% 1.39/1.57  cnf(c_0_122, plain, (m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X2)))|v5_pre_topc(X3,X1,X2)|k2_struct_0(X1)!=k1_xboole_0|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 1.39/1.57  cnf(c_0_123, negated_conjecture, (m1_subset_1(k7_tmap_1(esk2_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(k6_tmap_1(esk2_0,X1)))))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_78]), c_0_25]), c_0_26])]), c_0_27])).
% 1.39/1.57  cnf(c_0_124, negated_conjecture, (v1_funct_2(k7_tmap_1(esk2_0,esk3_0),u1_struct_0(esk2_0),u1_struct_0(k6_tmap_1(esk2_0,X1)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_78]), c_0_25]), c_0_26])]), c_0_27])).
% 1.39/1.57  cnf(c_0_125, negated_conjecture, (v5_pre_topc(X1,X2,k6_tmap_1(esk2_0,esk3_0))|v3_pre_topc(esk1_3(X2,k6_tmap_1(esk2_0,esk3_0),X1),k6_tmap_1(esk2_0,esk3_0))|k2_struct_0(X2)!=k1_xboole_0|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(esk2_0))|~v1_funct_1(X1)|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117, c_0_38]), c_0_37])])).
% 1.39/1.57  cnf(c_0_126, negated_conjecture, (m1_subset_1(k7_tmap_1(esk2_0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk2_0))))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_78]), c_0_38]), c_0_25]), c_0_26]), c_0_24])]), c_0_27])).
% 1.39/1.57  cnf(c_0_127, negated_conjecture, (v1_funct_1(k7_tmap_1(esk2_0,X1))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_78]), c_0_25]), c_0_26]), c_0_24])]), c_0_27])).
% 1.39/1.57  cnf(c_0_128, negated_conjecture, (v1_funct_2(k7_tmap_1(esk2_0,X1),u1_struct_0(esk2_0),u1_struct_0(esk2_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_78]), c_0_38]), c_0_25]), c_0_26]), c_0_24])]), c_0_27])).
% 1.39/1.57  cnf(c_0_129, negated_conjecture, (v2_struct_0(k6_tmap_1(esk2_0,esk3_0))|v5_pre_topc(k7_tmap_1(esk2_0,esk3_0),esk2_0,k6_tmap_1(k6_tmap_1(esk2_0,esk3_0),esk3_0))|k2_struct_0(esk2_0)!=k1_xboole_0|~v3_pre_topc(esk1_3(esk2_0,k6_tmap_1(k6_tmap_1(esk2_0,esk3_0),esk3_0),k7_tmap_1(esk2_0,esk3_0)),esk2_0)|~m1_subset_1(esk1_3(esk2_0,k6_tmap_1(k6_tmap_1(esk2_0,esk3_0),esk3_0),k7_tmap_1(esk2_0,esk3_0)),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_118, c_0_52]), c_0_53]), c_0_53]), c_0_54]), c_0_53]), c_0_41]), c_0_53]), c_0_26]), c_0_53]), c_0_55]), c_0_53])])).
% 1.39/1.57  cnf(c_0_130, negated_conjecture, (g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))=k6_tmap_1(k6_tmap_1(esk2_0,esk3_0),esk3_0)|v2_struct_0(k6_tmap_1(esk2_0,esk3_0))|~v3_pre_topc(esk3_0,esk2_0)), inference(spm,[status(thm)],[c_0_119, c_0_48])).
% 1.39/1.57  cnf(c_0_131, negated_conjecture, (g1_pre_topc(k1_xboole_0,u1_pre_topc(esk2_0))=k6_tmap_1(esk2_0,esk3_0)|~v3_pre_topc(esk3_0,esk2_0)), inference(rw,[status(thm)],[c_0_120, c_0_96])).
% 1.39/1.57  cnf(c_0_132, negated_conjecture, (v3_pre_topc(esk3_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_121, c_0_71]), c_0_109])])).
% 1.39/1.57  cnf(c_0_133, negated_conjecture, (v5_pre_topc(k7_tmap_1(esk2_0,esk3_0),esk2_0,k6_tmap_1(esk2_0,X1))|m1_subset_1(esk1_3(esk2_0,k6_tmap_1(esk2_0,X1),k7_tmap_1(esk2_0,esk3_0)),k1_zfmisc_1(u1_struct_0(k6_tmap_1(esk2_0,X1))))|k2_struct_0(esk2_0)!=k1_xboole_0|~l1_pre_topc(k6_tmap_1(esk2_0,X1))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_122, c_0_123]), c_0_41]), c_0_26])]), c_0_124])).
% 1.39/1.57  cnf(c_0_134, negated_conjecture, (v5_pre_topc(k7_tmap_1(esk2_0,X1),esk2_0,k6_tmap_1(esk2_0,esk3_0))|v3_pre_topc(esk1_3(esk2_0,k6_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,X1)),k6_tmap_1(esk2_0,esk3_0))|k2_struct_0(esk2_0)!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_125, c_0_126]), c_0_26])]), c_0_127]), c_0_128])).
% 1.39/1.57  cnf(c_0_135, negated_conjecture, (~v5_pre_topc(k7_tmap_1(esk2_0,X1),esk2_0,k6_tmap_1(esk2_0,esk3_0))|~v3_pre_topc(esk3_0,esk2_0)|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(rw,[status(thm)],[c_0_86, c_0_96])).
% 1.39/1.57  cnf(c_0_136, negated_conjecture, (v2_struct_0(k6_tmap_1(esk2_0,esk3_0))|v5_pre_topc(k7_tmap_1(esk2_0,esk3_0),esk2_0,k6_tmap_1(k6_tmap_1(esk2_0,esk3_0),esk3_0))|u1_struct_0(esk2_0)!=k1_xboole_0|~v3_pre_topc(esk1_3(esk2_0,k6_tmap_1(k6_tmap_1(esk2_0,esk3_0),esk3_0),k7_tmap_1(esk2_0,esk3_0)),esk2_0)|~m1_subset_1(esk1_3(esk2_0,k6_tmap_1(k6_tmap_1(esk2_0,esk3_0),esk3_0),k7_tmap_1(esk2_0,esk3_0)),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_129, c_0_91]), c_0_26])])).
% 1.39/1.57  cnf(c_0_137, negated_conjecture, (g1_pre_topc(k1_xboole_0,u1_pre_topc(esk2_0))=k6_tmap_1(k6_tmap_1(esk2_0,esk3_0),esk3_0)|v2_struct_0(k6_tmap_1(esk2_0,esk3_0))|~v3_pre_topc(esk3_0,esk2_0)), inference(rw,[status(thm)],[c_0_130, c_0_96])).
% 1.39/1.57  cnf(c_0_138, negated_conjecture, (g1_pre_topc(k1_xboole_0,u1_pre_topc(esk2_0))=k6_tmap_1(esk2_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_131, c_0_132])])).
% 1.39/1.57  cnf(c_0_139, negated_conjecture, (~v5_pre_topc(k7_tmap_1(esk2_0,k1_xboole_0),esk2_0,k6_tmap_1(esk2_0,esk3_0))|~v3_pre_topc(esk3_0,esk2_0)), inference(rw,[status(thm)],[c_0_77, c_0_107])).
% 1.39/1.57  cnf(c_0_140, negated_conjecture, (v5_pre_topc(k7_tmap_1(esk2_0,esk3_0),esk2_0,k6_tmap_1(esk2_0,X1))|m1_subset_1(esk1_3(esk2_0,k6_tmap_1(esk2_0,X1),k7_tmap_1(esk2_0,esk3_0)),k1_zfmisc_1(u1_struct_0(k6_tmap_1(esk2_0,X1))))|u1_struct_0(esk2_0)!=k1_xboole_0|~l1_pre_topc(k6_tmap_1(esk2_0,X1))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_133, c_0_91]), c_0_26])])).
% 1.39/1.57  cnf(c_0_141, negated_conjecture, (l1_pre_topc(k6_tmap_1(esk2_0,X1))|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_96]), c_0_25]), c_0_26])]), c_0_27])).
% 1.39/1.57  cnf(c_0_142, negated_conjecture, (v5_pre_topc(k7_tmap_1(esk2_0,X1),esk2_0,k6_tmap_1(esk2_0,esk3_0))|v3_pre_topc(esk1_3(esk2_0,k6_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,X1)),k6_tmap_1(esk2_0,esk3_0))|u1_struct_0(esk2_0)!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_134, c_0_91]), c_0_26])])).
% 1.39/1.57  cnf(c_0_143, negated_conjecture, (~v5_pre_topc(k7_tmap_1(esk2_0,X1),esk2_0,k6_tmap_1(esk2_0,esk3_0))|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_135, c_0_132])])).
% 1.39/1.57  cnf(c_0_144, negated_conjecture, (v2_struct_0(k6_tmap_1(esk2_0,esk3_0))|v5_pre_topc(k7_tmap_1(esk2_0,k1_xboole_0),esk2_0,k6_tmap_1(k6_tmap_1(esk2_0,esk3_0),esk3_0))|~v3_pre_topc(esk1_3(esk2_0,k6_tmap_1(k6_tmap_1(esk2_0,esk3_0),esk3_0),k7_tmap_1(esk2_0,k1_xboole_0)),esk2_0)|~m1_subset_1(esk1_3(esk2_0,k6_tmap_1(k6_tmap_1(esk2_0,esk3_0),esk3_0),k7_tmap_1(esk2_0,k1_xboole_0)),k1_zfmisc_1(k1_xboole_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_136, c_0_96]), c_0_96])]), c_0_107]), c_0_107]), c_0_107])).
% 1.39/1.57  cnf(c_0_145, negated_conjecture, (k6_tmap_1(k6_tmap_1(esk2_0,esk3_0),esk3_0)=k6_tmap_1(esk2_0,esk3_0)|v2_struct_0(k6_tmap_1(esk2_0,esk3_0))), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_137, c_0_132])]), c_0_138])).
% 1.39/1.57  cnf(c_0_146, negated_conjecture, (~v5_pre_topc(k7_tmap_1(esk2_0,k1_xboole_0),esk2_0,k6_tmap_1(esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_139, c_0_132])])).
% 1.39/1.57  cnf(c_0_147, negated_conjecture, (v5_pre_topc(k7_tmap_1(esk2_0,k1_xboole_0),esk2_0,k6_tmap_1(esk2_0,X1))|m1_subset_1(esk1_3(esk2_0,k6_tmap_1(esk2_0,X1),k7_tmap_1(esk2_0,k1_xboole_0)),k1_zfmisc_1(u1_struct_0(k6_tmap_1(esk2_0,X1))))|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(csr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_140, c_0_96]), c_0_96])]), c_0_107]), c_0_107]), c_0_141])).
% 1.39/1.57  cnf(c_0_148, negated_conjecture, (v3_pre_topc(esk1_3(esk2_0,k6_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,X1)),k6_tmap_1(esk2_0,esk3_0))|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_142, c_0_96]), c_0_96])]), c_0_143])).
% 1.39/1.57  cnf(c_0_149, negated_conjecture, (v2_struct_0(k6_tmap_1(esk2_0,esk3_0))|~v3_pre_topc(esk1_3(esk2_0,k6_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,k1_xboole_0)),esk2_0)|~m1_subset_1(esk1_3(esk2_0,k6_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,k1_xboole_0)),k1_zfmisc_1(k1_xboole_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_144, c_0_145]), c_0_146])).
% 1.39/1.57  cnf(c_0_150, negated_conjecture, (m1_subset_1(esk1_3(esk2_0,k6_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,k1_xboole_0)),k1_zfmisc_1(k1_xboole_0))), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_147, c_0_109]), c_0_38]), c_0_96]), c_0_146])).
% 1.39/1.57  cnf(c_0_151, negated_conjecture, (v3_pre_topc(esk1_3(esk2_0,k6_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,k1_xboole_0)),k6_tmap_1(esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_148, c_0_107]), c_0_109])])).
% 1.39/1.57  fof(c_0_152, plain, ![X27, X28]:(((~v2_struct_0(k6_tmap_1(X27,X28))|(v2_struct_0(X27)|~v2_pre_topc(X27)|~l1_pre_topc(X27)|~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))))&(v1_pre_topc(k6_tmap_1(X27,X28))|(v2_struct_0(X27)|~v2_pre_topc(X27)|~l1_pre_topc(X27)|~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27))))))&(v2_pre_topc(k6_tmap_1(X27,X28))|(v2_struct_0(X27)|~v2_pre_topc(X27)|~l1_pre_topc(X27)|~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc4_tmap_1])])])])).
% 1.39/1.57  cnf(c_0_153, negated_conjecture, (v2_struct_0(k6_tmap_1(esk2_0,esk3_0))|~v3_pre_topc(esk1_3(esk2_0,k6_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,k1_xboole_0)),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_149, c_0_150])])).
% 1.39/1.57  cnf(c_0_154, negated_conjecture, (v3_pre_topc(esk1_3(esk2_0,k6_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,k1_xboole_0)),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_121, c_0_151]), c_0_150])])).
% 1.39/1.57  cnf(c_0_155, plain, (v2_struct_0(X1)|~v2_struct_0(k6_tmap_1(X1,X2))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_152])).
% 1.39/1.57  cnf(c_0_156, negated_conjecture, (v2_struct_0(k6_tmap_1(esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_153, c_0_154])])).
% 1.39/1.57  cnf(c_0_157, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_155, c_0_156]), c_0_25]), c_0_26]), c_0_96]), c_0_109])]), c_0_27]), ['proof']).
% 1.39/1.57  # SZS output end CNFRefutation
% 1.39/1.57  # Proof object total steps             : 158
% 1.39/1.57  # Proof object clause steps            : 125
% 1.39/1.57  # Proof object formula steps           : 33
% 1.39/1.57  # Proof object conjectures             : 96
% 1.39/1.57  # Proof object clause conjectures      : 93
% 1.39/1.57  # Proof object formula conjectures     : 3
% 1.39/1.57  # Proof object initial clauses used    : 33
% 1.39/1.57  # Proof object initial formulas used   : 16
% 1.39/1.57  # Proof object generating inferences   : 67
% 1.39/1.57  # Proof object simplifying inferences  : 264
% 1.39/1.57  # Training examples: 0 positive, 0 negative
% 1.39/1.57  # Parsed axioms                        : 17
% 1.39/1.57  # Removed by relevancy pruning/SinE    : 0
% 1.39/1.57  # Initial clauses                      : 47
% 1.39/1.57  # Removed in clause preprocessing      : 0
% 1.39/1.57  # Initial clauses in saturation        : 47
% 1.39/1.57  # Processed clauses                    : 3381
% 1.39/1.57  # ...of these trivial                  : 51
% 1.39/1.57  # ...subsumed                          : 1666
% 1.39/1.57  # ...remaining for further processing  : 1664
% 1.39/1.57  # Other redundant clauses eliminated   : 3
% 1.39/1.57  # Clauses deleted for lack of memory   : 0
% 1.39/1.57  # Backward-subsumed                    : 68
% 1.39/1.57  # Backward-rewritten                   : 1279
% 1.39/1.57  # Generated clauses                    : 12258
% 1.39/1.57  # ...of the previous two non-trivial   : 12610
% 1.39/1.57  # Contextual simplify-reflections      : 505
% 1.39/1.57  # Paramodulations                      : 12255
% 1.39/1.57  # Factorizations                       : 0
% 1.39/1.57  # Equation resolutions                 : 3
% 1.39/1.57  # Propositional unsat checks           : 0
% 1.39/1.57  #    Propositional check models        : 0
% 1.39/1.57  #    Propositional check unsatisfiable : 0
% 1.39/1.57  #    Propositional clauses             : 0
% 1.39/1.57  #    Propositional clauses after purity: 0
% 1.39/1.57  #    Propositional unsat core size     : 0
% 1.39/1.57  #    Propositional preprocessing time  : 0.000
% 1.39/1.57  #    Propositional encoding time       : 0.000
% 1.39/1.57  #    Propositional solver time         : 0.000
% 1.39/1.57  #    Success case prop preproc time    : 0.000
% 1.39/1.57  #    Success case prop encoding time   : 0.000
% 1.39/1.57  #    Success case prop solver time     : 0.000
% 1.39/1.57  # Current number of processed clauses  : 314
% 1.39/1.57  #    Positive orientable unit clauses  : 36
% 1.39/1.57  #    Positive unorientable unit clauses: 0
% 1.39/1.57  #    Negative unit clauses             : 2
% 1.39/1.57  #    Non-unit-clauses                  : 276
% 1.39/1.57  # Current number of unprocessed clauses: 5709
% 1.39/1.57  # ...number of literals in the above   : 41938
% 1.39/1.57  # Current number of archived formulas  : 0
% 1.39/1.57  # Current number of archived clauses   : 1347
% 1.39/1.57  # Clause-clause subsumption calls (NU) : 316791
% 1.39/1.57  # Rec. Clause-clause subsumption calls : 41117
% 1.39/1.57  # Non-unit clause-clause subsumptions  : 2225
% 1.39/1.57  # Unit Clause-clause subsumption calls : 2386
% 1.39/1.57  # Rewrite failures with RHS unbound    : 0
% 1.39/1.57  # BW rewrite match attempts            : 47
% 1.39/1.57  # BW rewrite match successes           : 16
% 1.39/1.57  # Condensation attempts                : 0
% 1.39/1.57  # Condensation successes               : 0
% 1.39/1.57  # Termbank termtop insertions          : 700677
% 1.39/1.57  
% 1.39/1.57  # -------------------------------------------------
% 1.39/1.57  # User time                : 1.201 s
% 1.39/1.57  # System time              : 0.019 s
% 1.39/1.57  # Total time               : 1.220 s
% 1.39/1.57  # Maximum resident set size: 1600 pages
%------------------------------------------------------------------------------
