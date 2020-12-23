%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:18:16 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 704 expanded)
%              Number of clauses        :   47 ( 233 expanded)
%              Number of leaves         :   15 ( 172 expanded)
%              Depth                    :   17
%              Number of atoms          :  297 (3576 expanded)
%              Number of equality atoms :   30 ( 627 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   24 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t106_tmap_1,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_pre_topc(X2,X1)
          <=> g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k6_tmap_1(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_tmap_1)).

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

fof(d9_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k6_tmap_1(X1,X2) = g1_pre_topc(u1_struct_0(X1),k5_tmap_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_tmap_1)).

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

fof(t25_yellow_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
         => ( v1_tops_2(X2,X1)
          <=> m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(X1))))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_yellow_1)).

fof(t1_yellow_1,axiom,(
    ! [X1] :
      ( u1_struct_0(k2_yellow_1(X1)) = X1
      & u1_orders_2(k2_yellow_1(X1)) = k1_yellow_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_yellow_1)).

fof(dt_u1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(t32_compts_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( v1_tops_2(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
        <=> ( v1_tops_2(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_compts_1)).

fof(fc5_compts_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => v1_tops_2(u1_pre_topc(X1),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_compts_1)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(t102_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => r2_hidden(X2,k5_tmap_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t102_tmap_1)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( v3_pre_topc(X2,X1)
            <=> g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k6_tmap_1(X1,X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t106_tmap_1])).

fof(c_0_16,plain,(
    ! [X27,X28] :
      ( ( ~ r2_hidden(X28,u1_pre_topc(X27))
        | u1_pre_topc(X27) = k5_tmap_1(X27,X28)
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))
        | v2_struct_0(X27)
        | ~ v2_pre_topc(X27)
        | ~ l1_pre_topc(X27) )
      & ( u1_pre_topc(X27) != k5_tmap_1(X27,X28)
        | r2_hidden(X28,u1_pre_topc(X27))
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))
        | v2_struct_0(X27)
        | ~ v2_pre_topc(X27)
        | ~ l1_pre_topc(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t103_tmap_1])])])])])).

fof(c_0_17,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & ( ~ v3_pre_topc(esk2_0,esk1_0)
      | g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)) != k6_tmap_1(esk1_0,esk2_0) )
    & ( v3_pre_topc(esk2_0,esk1_0)
      | g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)) = k6_tmap_1(esk1_0,esk2_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_15])])])])).

fof(c_0_18,plain,(
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

cnf(c_0_19,plain,
    ( u1_pre_topc(X2) = k5_tmap_1(X2,X1)
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,u1_pre_topc(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_21,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( r2_hidden(X1,u1_pre_topc(X2))
    | ~ v3_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,negated_conjecture,
    ( u1_pre_topc(esk1_0) = k5_tmap_1(esk1_0,esk2_0)
    | ~ r2_hidden(esk2_0,u1_pre_topc(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21]),c_0_22])]),c_0_23])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(esk2_0,u1_pre_topc(esk1_0))
    | ~ v3_pre_topc(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_20]),c_0_22])])).

cnf(c_0_27,negated_conjecture,
    ( ~ v3_pre_topc(esk2_0,esk1_0)
    | g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)) != k6_tmap_1(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_28,negated_conjecture,
    ( u1_pre_topc(esk1_0) = k5_tmap_1(esk1_0,esk2_0)
    | ~ v3_pre_topc(esk2_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

fof(c_0_29,plain,(
    ! [X21,X22] :
      ( v2_struct_0(X21)
      | ~ v2_pre_topc(X21)
      | ~ l1_pre_topc(X21)
      | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))
      | k6_tmap_1(X21,X22) = g1_pre_topc(u1_struct_0(X21),k5_tmap_1(X21,X22)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d9_tmap_1])])])])).

fof(c_0_30,plain,(
    ! [X29,X30] :
      ( ( u1_struct_0(k6_tmap_1(X29,X30)) = u1_struct_0(X29)
        | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))
        | v2_struct_0(X29)
        | ~ v2_pre_topc(X29)
        | ~ l1_pre_topc(X29) )
      & ( u1_pre_topc(k6_tmap_1(X29,X30)) = k5_tmap_1(X29,X30)
        | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))
        | v2_struct_0(X29)
        | ~ v2_pre_topc(X29)
        | ~ l1_pre_topc(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t104_tmap_1])])])])])).

fof(c_0_31,plain,(
    ! [X23,X24] :
      ( ( v1_pre_topc(k6_tmap_1(X23,X24))
        | v2_struct_0(X23)
        | ~ v2_pre_topc(X23)
        | ~ l1_pre_topc(X23)
        | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23))) )
      & ( v2_pre_topc(k6_tmap_1(X23,X24))
        | v2_struct_0(X23)
        | ~ v2_pre_topc(X23)
        | ~ l1_pre_topc(X23)
        | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23))) )
      & ( l1_pre_topc(k6_tmap_1(X23,X24))
        | v2_struct_0(X23)
        | ~ v2_pre_topc(X23)
        | ~ l1_pre_topc(X23)
        | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_tmap_1])])])])).

cnf(c_0_32,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk1_0),k5_tmap_1(esk1_0,esk2_0)) != k6_tmap_1(esk1_0,esk2_0)
    | ~ v3_pre_topc(esk2_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_33,plain,
    ( v2_struct_0(X1)
    | k6_tmap_1(X1,X2) = g1_pre_topc(u1_struct_0(X1),k5_tmap_1(X1,X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_34,plain,(
    ! [X19,X20] :
      ( ( ~ v1_tops_2(X20,X19)
        | m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(X19)))))
        | ~ m1_subset_1(X20,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X19))))
        | ~ v2_pre_topc(X19)
        | ~ l1_pre_topc(X19) )
      & ( ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(X19)))))
        | v1_tops_2(X20,X19)
        | ~ m1_subset_1(X20,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X19))))
        | ~ v2_pre_topc(X19)
        | ~ l1_pre_topc(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_yellow_1])])])])).

fof(c_0_35,plain,(
    ! [X18] :
      ( u1_struct_0(k2_yellow_1(X18)) = X18
      & u1_orders_2(k2_yellow_1(X18)) = k1_yellow_1(X18) ) ),
    inference(variable_rename,[status(thm)],[t1_yellow_1])).

fof(c_0_36,plain,(
    ! [X14] :
      ( ~ l1_pre_topc(X14)
      | m1_subset_1(u1_pre_topc(X14),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X14)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).

cnf(c_0_37,plain,
    ( u1_struct_0(k6_tmap_1(X1,X2)) = u1_struct_0(X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_38,plain,
    ( l1_pre_topc(k6_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_39,plain,
    ( u1_pre_topc(k6_tmap_1(X1,X2)) = k5_tmap_1(X1,X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_40,plain,(
    ! [X16,X17] :
      ( ( v1_tops_2(X17,g1_pre_topc(u1_struct_0(X16),u1_pre_topc(X16)))
        | ~ v1_tops_2(X17,X16)
        | ~ m1_subset_1(X17,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X16))))
        | v2_struct_0(X16)
        | ~ v2_pre_topc(X16)
        | ~ l1_pre_topc(X16) )
      & ( m1_subset_1(X17,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X16),u1_pre_topc(X16))))))
        | ~ v1_tops_2(X17,X16)
        | ~ m1_subset_1(X17,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X16))))
        | v2_struct_0(X16)
        | ~ v2_pre_topc(X16)
        | ~ l1_pre_topc(X16) )
      & ( v1_tops_2(X17,X16)
        | ~ v1_tops_2(X17,g1_pre_topc(u1_struct_0(X16),u1_pre_topc(X16)))
        | ~ m1_subset_1(X17,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X16),u1_pre_topc(X16))))))
        | v2_struct_0(X16)
        | ~ v2_pre_topc(X16)
        | ~ l1_pre_topc(X16) )
      & ( m1_subset_1(X17,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X16))))
        | ~ v1_tops_2(X17,g1_pre_topc(u1_struct_0(X16),u1_pre_topc(X16)))
        | ~ m1_subset_1(X17,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X16),u1_pre_topc(X16))))))
        | v2_struct_0(X16)
        | ~ v2_pre_topc(X16)
        | ~ l1_pre_topc(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t32_compts_1])])])])])).

cnf(c_0_41,negated_conjecture,
    ( v3_pre_topc(esk2_0,esk1_0)
    | g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)) = k6_tmap_1(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_42,negated_conjecture,
    ( ~ v3_pre_topc(esk2_0,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_21]),c_0_22]),c_0_20])]),c_0_23])).

fof(c_0_43,plain,(
    ! [X15] :
      ( ~ l1_pre_topc(X15)
      | v1_tops_2(u1_pre_topc(X15),X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc5_compts_1])])).

cnf(c_0_44,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(X2)))))
    | ~ v1_tops_2(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_45,plain,
    ( u1_struct_0(k2_yellow_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_46,plain,
    ( m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_47,negated_conjecture,
    ( u1_struct_0(k6_tmap_1(esk1_0,esk2_0)) = u1_struct_0(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_20]),c_0_21]),c_0_22])]),c_0_23])).

cnf(c_0_48,negated_conjecture,
    ( l1_pre_topc(k6_tmap_1(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_20]),c_0_21]),c_0_22])]),c_0_23])).

cnf(c_0_49,negated_conjecture,
    ( u1_pre_topc(k6_tmap_1(esk1_0,esk2_0)) = k5_tmap_1(esk1_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_20]),c_0_21]),c_0_22])]),c_0_23])).

cnf(c_0_50,plain,
    ( v1_tops_2(X1,X2)
    | v2_struct_0(X2)
    | ~ v1_tops_2(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_51,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)) = k6_tmap_1(esk1_0,esk2_0) ),
    inference(sr,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_52,plain,
    ( v1_tops_2(u1_pre_topc(X1),X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_53,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_pre_topc(X2)))
    | ~ v2_pre_topc(X2)
    | ~ v1_tops_2(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) ),
    inference(rw,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_54,negated_conjecture,
    ( m1_subset_1(k5_tmap_1(esk1_0,esk2_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0)))) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_48])]),c_0_49])).

cnf(c_0_55,negated_conjecture,
    ( v1_tops_2(X1,esk1_0)
    | ~ v1_tops_2(X1,k6_tmap_1(esk1_0,esk2_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_21]),c_0_22]),c_0_47])]),c_0_23])).

cnf(c_0_56,negated_conjecture,
    ( v1_tops_2(k5_tmap_1(esk1_0,esk2_0),k6_tmap_1(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_49]),c_0_48])])).

fof(c_0_57,plain,(
    ! [X6,X7,X8] :
      ( ~ r2_hidden(X6,X7)
      | ~ m1_subset_1(X7,k1_zfmisc_1(X8))
      | m1_subset_1(X6,X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_58,negated_conjecture,
    ( m1_subset_1(k5_tmap_1(esk1_0,esk2_0),k1_zfmisc_1(u1_pre_topc(esk1_0)))
    | ~ v1_tops_2(k5_tmap_1(esk1_0,esk2_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_21]),c_0_22])])).

cnf(c_0_59,negated_conjecture,
    ( v1_tops_2(k5_tmap_1(esk1_0,esk2_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_54]),c_0_56])])).

fof(c_0_60,plain,(
    ! [X25,X26] :
      ( v2_struct_0(X25)
      | ~ v2_pre_topc(X25)
      | ~ l1_pre_topc(X25)
      | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))
      | r2_hidden(X26,k5_tmap_1(X25,X26)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t102_tmap_1])])])])).

cnf(c_0_61,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_62,negated_conjecture,
    ( m1_subset_1(k5_tmap_1(esk1_0,esk2_0),k1_zfmisc_1(u1_pre_topc(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_58,c_0_59])])).

cnf(c_0_63,plain,
    ( v2_struct_0(X1)
    | r2_hidden(X2,k5_tmap_1(X1,X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

fof(c_0_64,plain,(
    ! [X9,X10,X11] :
      ( ~ r2_hidden(X9,X10)
      | ~ m1_subset_1(X10,k1_zfmisc_1(X11))
      | ~ v1_xboole_0(X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

fof(c_0_65,plain,(
    ! [X4,X5] :
      ( ~ m1_subset_1(X4,X5)
      | v1_xboole_0(X5)
      | r2_hidden(X4,X5) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_66,negated_conjecture,
    ( m1_subset_1(X1,u1_pre_topc(esk1_0))
    | ~ r2_hidden(X1,k5_tmap_1(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_67,negated_conjecture,
    ( r2_hidden(esk2_0,k5_tmap_1(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_20]),c_0_21]),c_0_22])]),c_0_23])).

cnf(c_0_68,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_69,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_70,negated_conjecture,
    ( m1_subset_1(esk2_0,u1_pre_topc(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_71,negated_conjecture,
    ( ~ r2_hidden(X1,k5_tmap_1(esk1_0,esk2_0))
    | ~ v1_xboole_0(u1_pre_topc(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_68,c_0_62])).

cnf(c_0_72,negated_conjecture,
    ( r2_hidden(esk2_0,u1_pre_topc(esk1_0))
    | v1_xboole_0(u1_pre_topc(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_73,plain,
    ( v3_pre_topc(X1,X2)
    | ~ r2_hidden(X1,u1_pre_topc(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_74,negated_conjecture,
    ( r2_hidden(esk2_0,u1_pre_topc(esk1_0))
    | ~ r2_hidden(X1,k5_tmap_1(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_75,negated_conjecture,
    ( v3_pre_topc(esk2_0,esk1_0)
    | ~ r2_hidden(esk2_0,u1_pre_topc(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_20]),c_0_22])])).

cnf(c_0_76,negated_conjecture,
    ( r2_hidden(esk2_0,u1_pre_topc(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_74,c_0_67])).

cnf(c_0_77,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_75,c_0_76])]),c_0_42]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 20:31:08 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.38  # AutoSched0-Mode selected heuristic G_E___092_C01_F1_PI_AE_Q4_CS_SP_PS_S0Y
% 0.12/0.38  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.12/0.38  #
% 0.12/0.38  # Preprocessing time       : 0.028 s
% 0.12/0.38  # Presaturation interreduction done
% 0.12/0.38  
% 0.12/0.38  # Proof found!
% 0.12/0.38  # SZS status Theorem
% 0.12/0.38  # SZS output start CNFRefutation
% 0.12/0.38  fof(t106_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))=k6_tmap_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_tmap_1)).
% 0.12/0.38  fof(t103_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(r2_hidden(X2,u1_pre_topc(X1))<=>u1_pre_topc(X1)=k5_tmap_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t103_tmap_1)).
% 0.12/0.38  fof(d5_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>r2_hidden(X2,u1_pre_topc(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_pre_topc)).
% 0.12/0.38  fof(d9_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k6_tmap_1(X1,X2)=g1_pre_topc(u1_struct_0(X1),k5_tmap_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_tmap_1)).
% 0.12/0.38  fof(t104_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(u1_struct_0(k6_tmap_1(X1,X2))=u1_struct_0(X1)&u1_pre_topc(k6_tmap_1(X1,X2))=k5_tmap_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t104_tmap_1)).
% 0.12/0.38  fof(dt_k6_tmap_1, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>((v1_pre_topc(k6_tmap_1(X1,X2))&v2_pre_topc(k6_tmap_1(X1,X2)))&l1_pre_topc(k6_tmap_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_tmap_1)).
% 0.12/0.38  fof(t25_yellow_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>(v1_tops_2(X2,X1)<=>m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(X1)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_yellow_1)).
% 0.12/0.38  fof(t1_yellow_1, axiom, ![X1]:(u1_struct_0(k2_yellow_1(X1))=X1&u1_orders_2(k2_yellow_1(X1))=k1_yellow_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_yellow_1)).
% 0.12/0.38  fof(dt_u1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 0.12/0.38  fof(t32_compts_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((v1_tops_2(X2,X1)&m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))))<=>(v1_tops_2(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))&m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_compts_1)).
% 0.12/0.38  fof(fc5_compts_1, axiom, ![X1]:(l1_pre_topc(X1)=>v1_tops_2(u1_pre_topc(X1),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc5_compts_1)).
% 0.12/0.38  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 0.12/0.38  fof(t102_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>r2_hidden(X2,k5_tmap_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t102_tmap_1)).
% 0.12/0.38  fof(t5_subset, axiom, ![X1, X2, X3]:~(((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))&v1_xboole_0(X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 0.12/0.38  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 0.12/0.38  fof(c_0_15, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))=k6_tmap_1(X1,X2))))), inference(assume_negation,[status(cth)],[t106_tmap_1])).
% 0.12/0.38  fof(c_0_16, plain, ![X27, X28]:((~r2_hidden(X28,u1_pre_topc(X27))|u1_pre_topc(X27)=k5_tmap_1(X27,X28)|~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))|(v2_struct_0(X27)|~v2_pre_topc(X27)|~l1_pre_topc(X27)))&(u1_pre_topc(X27)!=k5_tmap_1(X27,X28)|r2_hidden(X28,u1_pre_topc(X27))|~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))|(v2_struct_0(X27)|~v2_pre_topc(X27)|~l1_pre_topc(X27)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t103_tmap_1])])])])])).
% 0.12/0.38  fof(c_0_17, negated_conjecture, (((~v2_struct_0(esk1_0)&v2_pre_topc(esk1_0))&l1_pre_topc(esk1_0))&(m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&((~v3_pre_topc(esk2_0,esk1_0)|g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))!=k6_tmap_1(esk1_0,esk2_0))&(v3_pre_topc(esk2_0,esk1_0)|g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))=k6_tmap_1(esk1_0,esk2_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_15])])])])).
% 0.12/0.38  fof(c_0_18, plain, ![X12, X13]:((~v3_pre_topc(X13,X12)|r2_hidden(X13,u1_pre_topc(X12))|~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))|~l1_pre_topc(X12))&(~r2_hidden(X13,u1_pre_topc(X12))|v3_pre_topc(X13,X12)|~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))|~l1_pre_topc(X12))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_pre_topc])])])])).
% 0.12/0.38  cnf(c_0_19, plain, (u1_pre_topc(X2)=k5_tmap_1(X2,X1)|v2_struct_0(X2)|~r2_hidden(X1,u1_pre_topc(X2))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.38  cnf(c_0_20, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.12/0.38  cnf(c_0_21, negated_conjecture, (v2_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.12/0.38  cnf(c_0_22, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.12/0.38  cnf(c_0_23, negated_conjecture, (~v2_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.12/0.38  cnf(c_0_24, plain, (r2_hidden(X1,u1_pre_topc(X2))|~v3_pre_topc(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.12/0.38  cnf(c_0_25, negated_conjecture, (u1_pre_topc(esk1_0)=k5_tmap_1(esk1_0,esk2_0)|~r2_hidden(esk2_0,u1_pre_topc(esk1_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_21]), c_0_22])]), c_0_23])).
% 0.12/0.38  cnf(c_0_26, negated_conjecture, (r2_hidden(esk2_0,u1_pre_topc(esk1_0))|~v3_pre_topc(esk2_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_20]), c_0_22])])).
% 0.12/0.38  cnf(c_0_27, negated_conjecture, (~v3_pre_topc(esk2_0,esk1_0)|g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))!=k6_tmap_1(esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.12/0.38  cnf(c_0_28, negated_conjecture, (u1_pre_topc(esk1_0)=k5_tmap_1(esk1_0,esk2_0)|~v3_pre_topc(esk2_0,esk1_0)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.12/0.38  fof(c_0_29, plain, ![X21, X22]:(v2_struct_0(X21)|~v2_pre_topc(X21)|~l1_pre_topc(X21)|(~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))|k6_tmap_1(X21,X22)=g1_pre_topc(u1_struct_0(X21),k5_tmap_1(X21,X22)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d9_tmap_1])])])])).
% 0.12/0.38  fof(c_0_30, plain, ![X29, X30]:((u1_struct_0(k6_tmap_1(X29,X30))=u1_struct_0(X29)|~m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))|(v2_struct_0(X29)|~v2_pre_topc(X29)|~l1_pre_topc(X29)))&(u1_pre_topc(k6_tmap_1(X29,X30))=k5_tmap_1(X29,X30)|~m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))|(v2_struct_0(X29)|~v2_pre_topc(X29)|~l1_pre_topc(X29)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t104_tmap_1])])])])])).
% 0.12/0.38  fof(c_0_31, plain, ![X23, X24]:(((v1_pre_topc(k6_tmap_1(X23,X24))|(v2_struct_0(X23)|~v2_pre_topc(X23)|~l1_pre_topc(X23)|~m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))))&(v2_pre_topc(k6_tmap_1(X23,X24))|(v2_struct_0(X23)|~v2_pre_topc(X23)|~l1_pre_topc(X23)|~m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23))))))&(l1_pre_topc(k6_tmap_1(X23,X24))|(v2_struct_0(X23)|~v2_pre_topc(X23)|~l1_pre_topc(X23)|~m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_tmap_1])])])])).
% 0.12/0.38  cnf(c_0_32, negated_conjecture, (g1_pre_topc(u1_struct_0(esk1_0),k5_tmap_1(esk1_0,esk2_0))!=k6_tmap_1(esk1_0,esk2_0)|~v3_pre_topc(esk2_0,esk1_0)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.12/0.38  cnf(c_0_33, plain, (v2_struct_0(X1)|k6_tmap_1(X1,X2)=g1_pre_topc(u1_struct_0(X1),k5_tmap_1(X1,X2))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.12/0.38  fof(c_0_34, plain, ![X19, X20]:((~v1_tops_2(X20,X19)|m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(X19)))))|~m1_subset_1(X20,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X19))))|(~v2_pre_topc(X19)|~l1_pre_topc(X19)))&(~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(X19)))))|v1_tops_2(X20,X19)|~m1_subset_1(X20,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X19))))|(~v2_pre_topc(X19)|~l1_pre_topc(X19)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_yellow_1])])])])).
% 0.12/0.38  fof(c_0_35, plain, ![X18]:(u1_struct_0(k2_yellow_1(X18))=X18&u1_orders_2(k2_yellow_1(X18))=k1_yellow_1(X18)), inference(variable_rename,[status(thm)],[t1_yellow_1])).
% 0.12/0.38  fof(c_0_36, plain, ![X14]:(~l1_pre_topc(X14)|m1_subset_1(u1_pre_topc(X14),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X14))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).
% 0.12/0.38  cnf(c_0_37, plain, (u1_struct_0(k6_tmap_1(X1,X2))=u1_struct_0(X1)|v2_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.12/0.38  cnf(c_0_38, plain, (l1_pre_topc(k6_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.12/0.38  cnf(c_0_39, plain, (u1_pre_topc(k6_tmap_1(X1,X2))=k5_tmap_1(X1,X2)|v2_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.12/0.38  fof(c_0_40, plain, ![X16, X17]:(((v1_tops_2(X17,g1_pre_topc(u1_struct_0(X16),u1_pre_topc(X16)))|(~v1_tops_2(X17,X16)|~m1_subset_1(X17,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X16)))))|(v2_struct_0(X16)|~v2_pre_topc(X16)|~l1_pre_topc(X16)))&(m1_subset_1(X17,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X16),u1_pre_topc(X16))))))|(~v1_tops_2(X17,X16)|~m1_subset_1(X17,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X16)))))|(v2_struct_0(X16)|~v2_pre_topc(X16)|~l1_pre_topc(X16))))&((v1_tops_2(X17,X16)|(~v1_tops_2(X17,g1_pre_topc(u1_struct_0(X16),u1_pre_topc(X16)))|~m1_subset_1(X17,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X16),u1_pre_topc(X16)))))))|(v2_struct_0(X16)|~v2_pre_topc(X16)|~l1_pre_topc(X16)))&(m1_subset_1(X17,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X16))))|(~v1_tops_2(X17,g1_pre_topc(u1_struct_0(X16),u1_pre_topc(X16)))|~m1_subset_1(X17,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X16),u1_pre_topc(X16)))))))|(v2_struct_0(X16)|~v2_pre_topc(X16)|~l1_pre_topc(X16))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t32_compts_1])])])])])).
% 0.12/0.38  cnf(c_0_41, negated_conjecture, (v3_pre_topc(esk2_0,esk1_0)|g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))=k6_tmap_1(esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.12/0.38  cnf(c_0_42, negated_conjecture, (~v3_pre_topc(esk2_0,esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_21]), c_0_22]), c_0_20])]), c_0_23])).
% 0.12/0.38  fof(c_0_43, plain, ![X15]:(~l1_pre_topc(X15)|v1_tops_2(u1_pre_topc(X15),X15)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc5_compts_1])])).
% 0.12/0.38  cnf(c_0_44, plain, (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(X2)))))|~v1_tops_2(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.12/0.38  cnf(c_0_45, plain, (u1_struct_0(k2_yellow_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.12/0.38  cnf(c_0_46, plain, (m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.12/0.38  cnf(c_0_47, negated_conjecture, (u1_struct_0(k6_tmap_1(esk1_0,esk2_0))=u1_struct_0(esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_20]), c_0_21]), c_0_22])]), c_0_23])).
% 0.12/0.38  cnf(c_0_48, negated_conjecture, (l1_pre_topc(k6_tmap_1(esk1_0,esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_20]), c_0_21]), c_0_22])]), c_0_23])).
% 0.12/0.38  cnf(c_0_49, negated_conjecture, (u1_pre_topc(k6_tmap_1(esk1_0,esk2_0))=k5_tmap_1(esk1_0,esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_20]), c_0_21]), c_0_22])]), c_0_23])).
% 0.12/0.38  cnf(c_0_50, plain, (v1_tops_2(X1,X2)|v2_struct_0(X2)|~v1_tops_2(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.12/0.38  cnf(c_0_51, negated_conjecture, (g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))=k6_tmap_1(esk1_0,esk2_0)), inference(sr,[status(thm)],[c_0_41, c_0_42])).
% 0.12/0.38  cnf(c_0_52, plain, (v1_tops_2(u1_pre_topc(X1),X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.12/0.38  cnf(c_0_53, plain, (m1_subset_1(X1,k1_zfmisc_1(u1_pre_topc(X2)))|~v2_pre_topc(X2)|~v1_tops_2(X1,X2)|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))), inference(rw,[status(thm)],[c_0_44, c_0_45])).
% 0.12/0.38  cnf(c_0_54, negated_conjecture, (m1_subset_1(k5_tmap_1(esk1_0,esk2_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_48])]), c_0_49])).
% 0.12/0.38  cnf(c_0_55, negated_conjecture, (v1_tops_2(X1,esk1_0)|~v1_tops_2(X1,k6_tmap_1(esk1_0,esk2_0))|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_21]), c_0_22]), c_0_47])]), c_0_23])).
% 0.12/0.38  cnf(c_0_56, negated_conjecture, (v1_tops_2(k5_tmap_1(esk1_0,esk2_0),k6_tmap_1(esk1_0,esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_49]), c_0_48])])).
% 0.12/0.38  fof(c_0_57, plain, ![X6, X7, X8]:(~r2_hidden(X6,X7)|~m1_subset_1(X7,k1_zfmisc_1(X8))|m1_subset_1(X6,X8)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.12/0.38  cnf(c_0_58, negated_conjecture, (m1_subset_1(k5_tmap_1(esk1_0,esk2_0),k1_zfmisc_1(u1_pre_topc(esk1_0)))|~v1_tops_2(k5_tmap_1(esk1_0,esk2_0),esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_21]), c_0_22])])).
% 0.12/0.38  cnf(c_0_59, negated_conjecture, (v1_tops_2(k5_tmap_1(esk1_0,esk2_0),esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_54]), c_0_56])])).
% 0.12/0.38  fof(c_0_60, plain, ![X25, X26]:(v2_struct_0(X25)|~v2_pre_topc(X25)|~l1_pre_topc(X25)|(~m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))|r2_hidden(X26,k5_tmap_1(X25,X26)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t102_tmap_1])])])])).
% 0.12/0.38  cnf(c_0_61, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.12/0.38  cnf(c_0_62, negated_conjecture, (m1_subset_1(k5_tmap_1(esk1_0,esk2_0),k1_zfmisc_1(u1_pre_topc(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_58, c_0_59])])).
% 0.12/0.38  cnf(c_0_63, plain, (v2_struct_0(X1)|r2_hidden(X2,k5_tmap_1(X1,X2))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.12/0.38  fof(c_0_64, plain, ![X9, X10, X11]:(~r2_hidden(X9,X10)|~m1_subset_1(X10,k1_zfmisc_1(X11))|~v1_xboole_0(X11)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).
% 0.12/0.38  fof(c_0_65, plain, ![X4, X5]:(~m1_subset_1(X4,X5)|(v1_xboole_0(X5)|r2_hidden(X4,X5))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.12/0.38  cnf(c_0_66, negated_conjecture, (m1_subset_1(X1,u1_pre_topc(esk1_0))|~r2_hidden(X1,k5_tmap_1(esk1_0,esk2_0))), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 0.12/0.38  cnf(c_0_67, negated_conjecture, (r2_hidden(esk2_0,k5_tmap_1(esk1_0,esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_20]), c_0_21]), c_0_22])]), c_0_23])).
% 0.12/0.38  cnf(c_0_68, plain, (~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.12/0.38  cnf(c_0_69, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.12/0.38  cnf(c_0_70, negated_conjecture, (m1_subset_1(esk2_0,u1_pre_topc(esk1_0))), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 0.12/0.38  cnf(c_0_71, negated_conjecture, (~r2_hidden(X1,k5_tmap_1(esk1_0,esk2_0))|~v1_xboole_0(u1_pre_topc(esk1_0))), inference(spm,[status(thm)],[c_0_68, c_0_62])).
% 0.12/0.38  cnf(c_0_72, negated_conjecture, (r2_hidden(esk2_0,u1_pre_topc(esk1_0))|v1_xboole_0(u1_pre_topc(esk1_0))), inference(spm,[status(thm)],[c_0_69, c_0_70])).
% 0.12/0.38  cnf(c_0_73, plain, (v3_pre_topc(X1,X2)|~r2_hidden(X1,u1_pre_topc(X2))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.12/0.38  cnf(c_0_74, negated_conjecture, (r2_hidden(esk2_0,u1_pre_topc(esk1_0))|~r2_hidden(X1,k5_tmap_1(esk1_0,esk2_0))), inference(spm,[status(thm)],[c_0_71, c_0_72])).
% 0.12/0.38  cnf(c_0_75, negated_conjecture, (v3_pre_topc(esk2_0,esk1_0)|~r2_hidden(esk2_0,u1_pre_topc(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_20]), c_0_22])])).
% 0.12/0.38  cnf(c_0_76, negated_conjecture, (r2_hidden(esk2_0,u1_pre_topc(esk1_0))), inference(spm,[status(thm)],[c_0_74, c_0_67])).
% 0.12/0.38  cnf(c_0_77, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_75, c_0_76])]), c_0_42]), ['proof']).
% 0.12/0.38  # SZS output end CNFRefutation
% 0.12/0.38  # Proof object total steps             : 78
% 0.12/0.38  # Proof object clause steps            : 47
% 0.12/0.38  # Proof object formula steps           : 31
% 0.12/0.38  # Proof object conjectures             : 33
% 0.12/0.38  # Proof object clause conjectures      : 30
% 0.12/0.38  # Proof object formula conjectures     : 3
% 0.12/0.38  # Proof object initial clauses used    : 22
% 0.12/0.38  # Proof object initial formulas used   : 15
% 0.12/0.38  # Proof object generating inferences   : 21
% 0.12/0.38  # Proof object simplifying inferences  : 51
% 0.12/0.38  # Training examples: 0 positive, 0 negative
% 0.12/0.38  # Parsed axioms                        : 15
% 0.12/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.38  # Initial clauses                      : 30
% 0.12/0.38  # Removed in clause preprocessing      : 1
% 0.12/0.38  # Initial clauses in saturation        : 29
% 0.12/0.38  # Processed clauses                    : 156
% 0.12/0.38  # ...of these trivial                  : 4
% 0.12/0.38  # ...subsumed                          : 15
% 0.12/0.38  # ...remaining for further processing  : 137
% 0.12/0.38  # Other redundant clauses eliminated   : 0
% 0.12/0.38  # Clauses deleted for lack of memory   : 0
% 0.12/0.38  # Backward-subsumed                    : 7
% 0.12/0.38  # Backward-rewritten                   : 10
% 0.12/0.38  # Generated clauses                    : 297
% 0.12/0.38  # ...of the previous two non-trivial   : 267
% 0.12/0.38  # Contextual simplify-reflections      : 2
% 0.12/0.38  # Paramodulations                      : 296
% 0.12/0.38  # Factorizations                       : 0
% 0.12/0.38  # Equation resolutions                 : 0
% 0.12/0.38  # Propositional unsat checks           : 0
% 0.12/0.38  #    Propositional check models        : 0
% 0.12/0.38  #    Propositional check unsatisfiable : 0
% 0.12/0.38  #    Propositional clauses             : 0
% 0.12/0.38  #    Propositional clauses after purity: 0
% 0.12/0.38  #    Propositional unsat core size     : 0
% 0.12/0.38  #    Propositional preprocessing time  : 0.000
% 0.12/0.38  #    Propositional encoding time       : 0.000
% 0.12/0.38  #    Propositional solver time         : 0.000
% 0.12/0.38  #    Success case prop preproc time    : 0.000
% 0.12/0.38  #    Success case prop encoding time   : 0.000
% 0.12/0.38  #    Success case prop solver time     : 0.000
% 0.12/0.38  # Current number of processed clauses  : 90
% 0.12/0.38  #    Positive orientable unit clauses  : 21
% 0.12/0.38  #    Positive unorientable unit clauses: 0
% 0.12/0.38  #    Negative unit clauses             : 2
% 0.12/0.38  #    Non-unit-clauses                  : 67
% 0.12/0.38  # Current number of unprocessed clauses: 167
% 0.12/0.38  # ...number of literals in the above   : 927
% 0.12/0.38  # Current number of archived formulas  : 0
% 0.12/0.38  # Current number of archived clauses   : 48
% 0.12/0.38  # Clause-clause subsumption calls (NU) : 571
% 0.12/0.38  # Rec. Clause-clause subsumption calls : 181
% 0.12/0.38  # Non-unit clause-clause subsumptions  : 11
% 0.12/0.38  # Unit Clause-clause subsumption calls : 78
% 0.12/0.38  # Rewrite failures with RHS unbound    : 0
% 0.12/0.38  # BW rewrite match attempts            : 5
% 0.12/0.38  # BW rewrite match successes           : 5
% 0.12/0.38  # Condensation attempts                : 0
% 0.12/0.38  # Condensation successes               : 0
% 0.12/0.38  # Termbank termtop insertions          : 10252
% 0.12/0.38  
% 0.12/0.38  # -------------------------------------------------
% 0.12/0.38  # User time                : 0.038 s
% 0.12/0.38  # System time              : 0.005 s
% 0.12/0.38  # Total time               : 0.044 s
% 0.12/0.38  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
