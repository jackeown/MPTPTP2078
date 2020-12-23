%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:18:13 EST 2020

% Result     : Theorem 0.51s
% Output     : CNFRefutation 0.51s
% Verified   : 
% Statistics : Number of formulae       :   86 (2512 expanded)
%              Number of clauses        :   63 ( 944 expanded)
%              Number of leaves         :   11 ( 639 expanded)
%              Depth                    :   17
%              Number of atoms          :  281 (10505 expanded)
%              Number of equality atoms :   48 (2015 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   15 (   3 average)
%              Maximal term depth       :    5 (   2 average)

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_tmap_1)).

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

fof(abstractness_v1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ( v1_pre_topc(X1)
       => X1 = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

fof(d5_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_pre_topc(X2,X1)
          <=> r2_hidden(X2,u1_pre_topc(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_pre_topc)).

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

fof(dt_k2_subset_1,axiom,(
    ! [X1] : m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

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

fof(fc10_tops_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => v3_pre_topc(k2_struct_0(X1),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_tops_1)).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( v3_pre_topc(X2,X1)
            <=> g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k6_tmap_1(X1,X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t106_tmap_1])).

fof(c_0_12,plain,(
    ! [X15,X16] :
      ( ( u1_struct_0(k6_tmap_1(X15,X16)) = u1_struct_0(X15)
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
        | v2_struct_0(X15)
        | ~ v2_pre_topc(X15)
        | ~ l1_pre_topc(X15) )
      & ( u1_pre_topc(k6_tmap_1(X15,X16)) = k5_tmap_1(X15,X16)
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
        | v2_struct_0(X15)
        | ~ v2_pre_topc(X15)
        | ~ l1_pre_topc(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t104_tmap_1])])])])])).

fof(c_0_13,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & ( ~ v3_pre_topc(esk2_0,esk1_0)
      | g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)) != k6_tmap_1(esk1_0,esk2_0) )
    & ( v3_pre_topc(esk2_0,esk1_0)
      | g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)) = k6_tmap_1(esk1_0,esk2_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_11])])])])).

fof(c_0_14,plain,(
    ! [X11,X12] :
      ( ( v1_pre_topc(k6_tmap_1(X11,X12))
        | v2_struct_0(X11)
        | ~ v2_pre_topc(X11)
        | ~ l1_pre_topc(X11)
        | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X11))) )
      & ( v2_pre_topc(k6_tmap_1(X11,X12))
        | v2_struct_0(X11)
        | ~ v2_pre_topc(X11)
        | ~ l1_pre_topc(X11)
        | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X11))) )
      & ( l1_pre_topc(k6_tmap_1(X11,X12))
        | v2_struct_0(X11)
        | ~ v2_pre_topc(X11)
        | ~ l1_pre_topc(X11)
        | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X11))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_tmap_1])])])])).

fof(c_0_15,plain,(
    ! [X5] :
      ( ~ l1_pre_topc(X5)
      | ~ v1_pre_topc(X5)
      | X5 = g1_pre_topc(u1_struct_0(X5),u1_pre_topc(X5)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[abstractness_v1_pre_topc])])).

cnf(c_0_16,plain,
    ( u1_struct_0(k6_tmap_1(X1,X2)) = u1_struct_0(X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,plain,
    ( v1_pre_topc(k6_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,plain,
    ( l1_pre_topc(k6_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_23,plain,(
    ! [X7,X8] :
      ( ( ~ v3_pre_topc(X8,X7)
        | r2_hidden(X8,u1_pre_topc(X7))
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X7)))
        | ~ l1_pre_topc(X7) )
      & ( ~ r2_hidden(X8,u1_pre_topc(X7))
        | v3_pre_topc(X8,X7)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X7)))
        | ~ l1_pre_topc(X7) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_pre_topc])])])])).

fof(c_0_24,plain,(
    ! [X6] :
      ( ~ l1_struct_0(X6)
      | k2_struct_0(X6) = u1_struct_0(X6) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

fof(c_0_25,plain,(
    ! [X9] :
      ( ~ l1_pre_topc(X9)
      | l1_struct_0(X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

fof(c_0_26,plain,(
    ! [X4] : m1_subset_1(k2_subset_1(X4),k1_zfmisc_1(X4)) ),
    inference(variable_rename,[status(thm)],[dt_k2_subset_1])).

fof(c_0_27,plain,(
    ! [X3] : k2_subset_1(X3) = X3 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

cnf(c_0_28,plain,
    ( X1 = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ l1_pre_topc(X1)
    | ~ v1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_29,negated_conjecture,
    ( u1_struct_0(k6_tmap_1(esk1_0,esk2_0)) = u1_struct_0(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18]),c_0_19])]),c_0_20])).

cnf(c_0_30,negated_conjecture,
    ( v1_pre_topc(k6_tmap_1(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_17]),c_0_18]),c_0_19])]),c_0_20])).

cnf(c_0_31,negated_conjecture,
    ( l1_pre_topc(k6_tmap_1(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_17]),c_0_18]),c_0_19])]),c_0_20])).

cnf(c_0_32,plain,
    ( u1_pre_topc(k6_tmap_1(X1,X2)) = k5_tmap_1(X1,X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_33,plain,(
    ! [X13,X14] :
      ( ( ~ r2_hidden(X14,u1_pre_topc(X13))
        | u1_pre_topc(X13) = k5_tmap_1(X13,X14)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | v2_struct_0(X13)
        | ~ v2_pre_topc(X13)
        | ~ l1_pre_topc(X13) )
      & ( u1_pre_topc(X13) != k5_tmap_1(X13,X14)
        | r2_hidden(X14,u1_pre_topc(X13))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | v2_struct_0(X13)
        | ~ v2_pre_topc(X13)
        | ~ l1_pre_topc(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t103_tmap_1])])])])])).

cnf(c_0_34,plain,
    ( r2_hidden(X1,u1_pre_topc(X2))
    | ~ v3_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_35,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_36,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_37,plain,
    ( m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_38,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_39,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(k6_tmap_1(esk1_0,esk2_0))) = k6_tmap_1(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30]),c_0_31])])).

cnf(c_0_40,negated_conjecture,
    ( u1_pre_topc(k6_tmap_1(esk1_0,esk2_0)) = k5_tmap_1(esk1_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_17]),c_0_18]),c_0_19])]),c_0_20])).

cnf(c_0_41,plain,
    ( u1_pre_topc(X2) = k5_tmap_1(X2,X1)
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,u1_pre_topc(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(esk2_0,u1_pre_topc(esk1_0))
    | ~ v3_pre_topc(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_17]),c_0_19])])).

cnf(c_0_43,plain,
    ( u1_struct_0(k6_tmap_1(X1,X2)) = k2_struct_0(X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_35]),c_0_36])).

cnf(c_0_44,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_45,plain,
    ( v2_struct_0(X1)
    | l1_pre_topc(k6_tmap_1(X1,X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_35]),c_0_36])).

cnf(c_0_46,plain,
    ( v2_struct_0(X1)
    | v1_pre_topc(k6_tmap_1(X1,X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_35]),c_0_36])).

cnf(c_0_47,negated_conjecture,
    ( v3_pre_topc(esk2_0,esk1_0)
    | g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)) = k6_tmap_1(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_48,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk1_0),k5_tmap_1(esk1_0,esk2_0)) = k6_tmap_1(esk1_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_49,negated_conjecture,
    ( k5_tmap_1(esk1_0,esk2_0) = u1_pre_topc(esk1_0)
    | ~ v3_pre_topc(esk2_0,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_18]),c_0_19]),c_0_17])]),c_0_20])).

cnf(c_0_50,plain,
    ( u1_struct_0(k6_tmap_1(X1,k2_struct_0(X1))) = k2_struct_0(X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_51,plain,
    ( v2_struct_0(X1)
    | l1_pre_topc(k6_tmap_1(X1,k2_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_45,c_0_44])).

cnf(c_0_52,plain,
    ( v2_struct_0(X1)
    | v1_pre_topc(k6_tmap_1(X1,k2_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_46,c_0_44])).

cnf(c_0_53,plain,
    ( u1_pre_topc(k6_tmap_1(X1,X2)) = k5_tmap_1(X1,X2)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_35]),c_0_36])).

cnf(c_0_54,plain,
    ( r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ v3_pre_topc(u1_struct_0(X1),X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_44])).

fof(c_0_55,plain,(
    ! [X10] :
      ( ~ v2_pre_topc(X10)
      | ~ l1_pre_topc(X10)
      | v3_pre_topc(k2_struct_0(X10),X10) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc10_tops_1])])).

cnf(c_0_56,negated_conjecture,
    ( g1_pre_topc(k2_struct_0(esk1_0),u1_pre_topc(esk1_0)) = k6_tmap_1(esk1_0,esk2_0)
    | v3_pre_topc(esk2_0,esk1_0)
    | ~ l1_struct_0(esk1_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_35])).

cnf(c_0_57,negated_conjecture,
    ( ~ v3_pre_topc(esk2_0,esk1_0)
    | g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)) != k6_tmap_1(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_58,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)) = k6_tmap_1(esk1_0,esk2_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_47])).

cnf(c_0_59,plain,
    ( g1_pre_topc(k2_struct_0(X1),u1_pre_topc(k6_tmap_1(X1,k2_struct_0(X1)))) = k6_tmap_1(X1,k2_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_50]),c_0_51]),c_0_52])).

cnf(c_0_60,plain,
    ( u1_pre_topc(k6_tmap_1(X1,k2_struct_0(X1))) = k5_tmap_1(X1,k2_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_53,c_0_44])).

cnf(c_0_61,plain,
    ( k5_tmap_1(X1,u1_struct_0(X1)) = u1_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ v3_pre_topc(u1_struct_0(X1),X1)
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_54]),c_0_44])])).

cnf(c_0_62,plain,
    ( v3_pre_topc(k2_struct_0(X1),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_63,negated_conjecture,
    ( g1_pre_topc(k2_struct_0(esk1_0),u1_pre_topc(esk1_0)) = k6_tmap_1(esk1_0,esk2_0)
    | v3_pre_topc(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_36]),c_0_19])])).

cnf(c_0_64,negated_conjecture,
    ( ~ v3_pre_topc(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_57,c_0_58])])).

cnf(c_0_65,plain,
    ( g1_pre_topc(k2_struct_0(X1),k5_tmap_1(X1,k2_struct_0(X1))) = k6_tmap_1(X1,k2_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_66,plain,
    ( k5_tmap_1(X1,k2_struct_0(X1)) = u1_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_35]),c_0_36]),c_0_62])).

cnf(c_0_67,negated_conjecture,
    ( g1_pre_topc(k2_struct_0(esk1_0),u1_pre_topc(esk1_0)) = k6_tmap_1(esk1_0,esk2_0) ),
    inference(sr,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_68,plain,
    ( g1_pre_topc(k2_struct_0(X1),u1_pre_topc(X1)) = k6_tmap_1(X1,k2_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_69,plain,
    ( v3_pre_topc(X1,X2)
    | ~ r2_hidden(X1,u1_pre_topc(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_70,negated_conjecture,
    ( k6_tmap_1(esk1_0,k2_struct_0(esk1_0)) = k6_tmap_1(esk1_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_18]),c_0_19])]),c_0_20])).

cnf(c_0_71,plain,
    ( r2_hidden(X2,u1_pre_topc(X1))
    | v2_struct_0(X1)
    | u1_pre_topc(X1) != k5_tmap_1(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_72,plain,
    ( v3_pre_topc(u1_struct_0(X1),X1)
    | ~ r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_69,c_0_44])).

cnf(c_0_73,negated_conjecture,
    ( u1_struct_0(esk1_0) = k2_struct_0(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_70]),c_0_29]),c_0_18]),c_0_19])]),c_0_20])).

cnf(c_0_74,plain,
    ( v2_struct_0(X1)
    | r2_hidden(k2_struct_0(X1),u1_pre_topc(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_71,c_0_66])).

cnf(c_0_75,negated_conjecture,
    ( v3_pre_topc(k2_struct_0(esk1_0),esk1_0)
    | ~ r2_hidden(k2_struct_0(esk1_0),u1_pre_topc(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_19])])).

cnf(c_0_76,plain,
    ( v2_struct_0(X1)
    | r2_hidden(k2_struct_0(X1),u1_pre_topc(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_35]),c_0_44])]),c_0_36])).

cnf(c_0_77,negated_conjecture,
    ( r2_hidden(X1,u1_pre_topc(esk1_0))
    | ~ v3_pre_topc(X1,esk1_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_73]),c_0_19])])).

cnf(c_0_78,negated_conjecture,
    ( v3_pre_topc(k2_struct_0(esk1_0),esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_18]),c_0_19])]),c_0_20])).

cnf(c_0_79,negated_conjecture,
    ( r2_hidden(k2_struct_0(esk1_0),u1_pre_topc(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_44]),c_0_78])])).

cnf(c_0_80,negated_conjecture,
    ( k5_tmap_1(esk1_0,k2_struct_0(esk1_0)) = u1_pre_topc(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_79]),c_0_18]),c_0_19]),c_0_73]),c_0_44])]),c_0_20])).

cnf(c_0_81,plain,
    ( v3_pre_topc(X1,X2)
    | ~ r2_hidden(X1,u1_pre_topc(X2))
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(X2))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_35]),c_0_36])).

cnf(c_0_82,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(k2_struct_0(esk1_0))) ),
    inference(rw,[status(thm)],[c_0_17,c_0_73])).

cnf(c_0_83,negated_conjecture,
    ( k5_tmap_1(esk1_0,esk2_0) = u1_pre_topc(esk1_0) ),
    inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_70]),c_0_40]),c_0_18]),c_0_19])]),c_0_20]),c_0_80])).

cnf(c_0_84,negated_conjecture,
    ( ~ r2_hidden(esk2_0,u1_pre_topc(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_82]),c_0_19])]),c_0_64])).

cnf(c_0_85,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_83]),c_0_18]),c_0_19]),c_0_73]),c_0_82])]),c_0_20]),c_0_84]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:32:30 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.51/0.67  # AutoSched0-Mode selected heuristic G_E___208_C12_02_nc_F1_SE_CS_SP_PS_S06DN
% 0.51/0.67  # and selection function SelectNewComplexAHPExceptUniqMaxHorn.
% 0.51/0.67  #
% 0.51/0.67  # Preprocessing time       : 0.029 s
% 0.51/0.67  # Presaturation interreduction done
% 0.51/0.67  
% 0.51/0.67  # Proof found!
% 0.51/0.67  # SZS status Theorem
% 0.51/0.67  # SZS output start CNFRefutation
% 0.51/0.67  fof(t106_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))=k6_tmap_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_tmap_1)).
% 0.51/0.67  fof(t104_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(u1_struct_0(k6_tmap_1(X1,X2))=u1_struct_0(X1)&u1_pre_topc(k6_tmap_1(X1,X2))=k5_tmap_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t104_tmap_1)).
% 0.51/0.67  fof(dt_k6_tmap_1, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>((v1_pre_topc(k6_tmap_1(X1,X2))&v2_pre_topc(k6_tmap_1(X1,X2)))&l1_pre_topc(k6_tmap_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_tmap_1)).
% 0.51/0.67  fof(abstractness_v1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>(v1_pre_topc(X1)=>X1=g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', abstractness_v1_pre_topc)).
% 0.51/0.67  fof(d5_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>r2_hidden(X2,u1_pre_topc(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_pre_topc)).
% 0.51/0.67  fof(d3_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>k2_struct_0(X1)=u1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 0.51/0.67  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.51/0.67  fof(dt_k2_subset_1, axiom, ![X1]:m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 0.51/0.67  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 0.51/0.67  fof(t103_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(r2_hidden(X2,u1_pre_topc(X1))<=>u1_pre_topc(X1)=k5_tmap_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t103_tmap_1)).
% 0.51/0.67  fof(fc10_tops_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>v3_pre_topc(k2_struct_0(X1),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc10_tops_1)).
% 0.51/0.67  fof(c_0_11, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))=k6_tmap_1(X1,X2))))), inference(assume_negation,[status(cth)],[t106_tmap_1])).
% 0.51/0.67  fof(c_0_12, plain, ![X15, X16]:((u1_struct_0(k6_tmap_1(X15,X16))=u1_struct_0(X15)|~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))|(v2_struct_0(X15)|~v2_pre_topc(X15)|~l1_pre_topc(X15)))&(u1_pre_topc(k6_tmap_1(X15,X16))=k5_tmap_1(X15,X16)|~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))|(v2_struct_0(X15)|~v2_pre_topc(X15)|~l1_pre_topc(X15)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t104_tmap_1])])])])])).
% 0.51/0.67  fof(c_0_13, negated_conjecture, (((~v2_struct_0(esk1_0)&v2_pre_topc(esk1_0))&l1_pre_topc(esk1_0))&(m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&((~v3_pre_topc(esk2_0,esk1_0)|g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))!=k6_tmap_1(esk1_0,esk2_0))&(v3_pre_topc(esk2_0,esk1_0)|g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))=k6_tmap_1(esk1_0,esk2_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_11])])])])).
% 0.51/0.67  fof(c_0_14, plain, ![X11, X12]:(((v1_pre_topc(k6_tmap_1(X11,X12))|(v2_struct_0(X11)|~v2_pre_topc(X11)|~l1_pre_topc(X11)|~m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X11)))))&(v2_pre_topc(k6_tmap_1(X11,X12))|(v2_struct_0(X11)|~v2_pre_topc(X11)|~l1_pre_topc(X11)|~m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X11))))))&(l1_pre_topc(k6_tmap_1(X11,X12))|(v2_struct_0(X11)|~v2_pre_topc(X11)|~l1_pre_topc(X11)|~m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X11)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_tmap_1])])])])).
% 0.51/0.67  fof(c_0_15, plain, ![X5]:(~l1_pre_topc(X5)|(~v1_pre_topc(X5)|X5=g1_pre_topc(u1_struct_0(X5),u1_pre_topc(X5)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[abstractness_v1_pre_topc])])).
% 0.51/0.67  cnf(c_0_16, plain, (u1_struct_0(k6_tmap_1(X1,X2))=u1_struct_0(X1)|v2_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.51/0.67  cnf(c_0_17, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.51/0.67  cnf(c_0_18, negated_conjecture, (v2_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.51/0.67  cnf(c_0_19, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.51/0.67  cnf(c_0_20, negated_conjecture, (~v2_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.51/0.67  cnf(c_0_21, plain, (v1_pre_topc(k6_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.51/0.67  cnf(c_0_22, plain, (l1_pre_topc(k6_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.51/0.67  fof(c_0_23, plain, ![X7, X8]:((~v3_pre_topc(X8,X7)|r2_hidden(X8,u1_pre_topc(X7))|~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X7)))|~l1_pre_topc(X7))&(~r2_hidden(X8,u1_pre_topc(X7))|v3_pre_topc(X8,X7)|~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X7)))|~l1_pre_topc(X7))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_pre_topc])])])])).
% 0.51/0.67  fof(c_0_24, plain, ![X6]:(~l1_struct_0(X6)|k2_struct_0(X6)=u1_struct_0(X6)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).
% 0.51/0.67  fof(c_0_25, plain, ![X9]:(~l1_pre_topc(X9)|l1_struct_0(X9)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.51/0.67  fof(c_0_26, plain, ![X4]:m1_subset_1(k2_subset_1(X4),k1_zfmisc_1(X4)), inference(variable_rename,[status(thm)],[dt_k2_subset_1])).
% 0.51/0.67  fof(c_0_27, plain, ![X3]:k2_subset_1(X3)=X3, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 0.51/0.67  cnf(c_0_28, plain, (X1=g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))|~l1_pre_topc(X1)|~v1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.51/0.67  cnf(c_0_29, negated_conjecture, (u1_struct_0(k6_tmap_1(esk1_0,esk2_0))=u1_struct_0(esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_17]), c_0_18]), c_0_19])]), c_0_20])).
% 0.51/0.67  cnf(c_0_30, negated_conjecture, (v1_pre_topc(k6_tmap_1(esk1_0,esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_17]), c_0_18]), c_0_19])]), c_0_20])).
% 0.51/0.67  cnf(c_0_31, negated_conjecture, (l1_pre_topc(k6_tmap_1(esk1_0,esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_17]), c_0_18]), c_0_19])]), c_0_20])).
% 0.51/0.67  cnf(c_0_32, plain, (u1_pre_topc(k6_tmap_1(X1,X2))=k5_tmap_1(X1,X2)|v2_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.51/0.67  fof(c_0_33, plain, ![X13, X14]:((~r2_hidden(X14,u1_pre_topc(X13))|u1_pre_topc(X13)=k5_tmap_1(X13,X14)|~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))|(v2_struct_0(X13)|~v2_pre_topc(X13)|~l1_pre_topc(X13)))&(u1_pre_topc(X13)!=k5_tmap_1(X13,X14)|r2_hidden(X14,u1_pre_topc(X13))|~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))|(v2_struct_0(X13)|~v2_pre_topc(X13)|~l1_pre_topc(X13)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t103_tmap_1])])])])])).
% 0.51/0.67  cnf(c_0_34, plain, (r2_hidden(X1,u1_pre_topc(X2))|~v3_pre_topc(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.51/0.67  cnf(c_0_35, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.51/0.67  cnf(c_0_36, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.51/0.67  cnf(c_0_37, plain, (m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.51/0.67  cnf(c_0_38, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.51/0.67  cnf(c_0_39, negated_conjecture, (g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(k6_tmap_1(esk1_0,esk2_0)))=k6_tmap_1(esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_30]), c_0_31])])).
% 0.51/0.67  cnf(c_0_40, negated_conjecture, (u1_pre_topc(k6_tmap_1(esk1_0,esk2_0))=k5_tmap_1(esk1_0,esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_17]), c_0_18]), c_0_19])]), c_0_20])).
% 0.51/0.67  cnf(c_0_41, plain, (u1_pre_topc(X2)=k5_tmap_1(X2,X1)|v2_struct_0(X2)|~r2_hidden(X1,u1_pre_topc(X2))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.51/0.67  cnf(c_0_42, negated_conjecture, (r2_hidden(esk2_0,u1_pre_topc(esk1_0))|~v3_pre_topc(esk2_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_17]), c_0_19])])).
% 0.51/0.67  cnf(c_0_43, plain, (u1_struct_0(k6_tmap_1(X1,X2))=k2_struct_0(X1)|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_35]), c_0_36])).
% 0.51/0.67  cnf(c_0_44, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_37, c_0_38])).
% 0.51/0.67  cnf(c_0_45, plain, (v2_struct_0(X1)|l1_pre_topc(k6_tmap_1(X1,X2))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_35]), c_0_36])).
% 0.51/0.67  cnf(c_0_46, plain, (v2_struct_0(X1)|v1_pre_topc(k6_tmap_1(X1,X2))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_35]), c_0_36])).
% 0.51/0.67  cnf(c_0_47, negated_conjecture, (v3_pre_topc(esk2_0,esk1_0)|g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))=k6_tmap_1(esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.51/0.67  cnf(c_0_48, negated_conjecture, (g1_pre_topc(u1_struct_0(esk1_0),k5_tmap_1(esk1_0,esk2_0))=k6_tmap_1(esk1_0,esk2_0)), inference(rw,[status(thm)],[c_0_39, c_0_40])).
% 0.51/0.67  cnf(c_0_49, negated_conjecture, (k5_tmap_1(esk1_0,esk2_0)=u1_pre_topc(esk1_0)|~v3_pre_topc(esk2_0,esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_18]), c_0_19]), c_0_17])]), c_0_20])).
% 0.51/0.67  cnf(c_0_50, plain, (u1_struct_0(k6_tmap_1(X1,k2_struct_0(X1)))=k2_struct_0(X1)|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.51/0.67  cnf(c_0_51, plain, (v2_struct_0(X1)|l1_pre_topc(k6_tmap_1(X1,k2_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_45, c_0_44])).
% 0.51/0.67  cnf(c_0_52, plain, (v2_struct_0(X1)|v1_pre_topc(k6_tmap_1(X1,k2_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_46, c_0_44])).
% 0.51/0.67  cnf(c_0_53, plain, (u1_pre_topc(k6_tmap_1(X1,X2))=k5_tmap_1(X1,X2)|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_35]), c_0_36])).
% 0.51/0.67  cnf(c_0_54, plain, (r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))|~v3_pre_topc(u1_struct_0(X1),X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_34, c_0_44])).
% 0.51/0.67  fof(c_0_55, plain, ![X10]:(~v2_pre_topc(X10)|~l1_pre_topc(X10)|v3_pre_topc(k2_struct_0(X10),X10)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc10_tops_1])])).
% 0.51/0.67  cnf(c_0_56, negated_conjecture, (g1_pre_topc(k2_struct_0(esk1_0),u1_pre_topc(esk1_0))=k6_tmap_1(esk1_0,esk2_0)|v3_pre_topc(esk2_0,esk1_0)|~l1_struct_0(esk1_0)), inference(spm,[status(thm)],[c_0_47, c_0_35])).
% 0.51/0.67  cnf(c_0_57, negated_conjecture, (~v3_pre_topc(esk2_0,esk1_0)|g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))!=k6_tmap_1(esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.51/0.67  cnf(c_0_58, negated_conjecture, (g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))=k6_tmap_1(esk1_0,esk2_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_47])).
% 0.51/0.67  cnf(c_0_59, plain, (g1_pre_topc(k2_struct_0(X1),u1_pre_topc(k6_tmap_1(X1,k2_struct_0(X1))))=k6_tmap_1(X1,k2_struct_0(X1))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_50]), c_0_51]), c_0_52])).
% 0.51/0.67  cnf(c_0_60, plain, (u1_pre_topc(k6_tmap_1(X1,k2_struct_0(X1)))=k5_tmap_1(X1,k2_struct_0(X1))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_53, c_0_44])).
% 0.51/0.67  cnf(c_0_61, plain, (k5_tmap_1(X1,u1_struct_0(X1))=u1_pre_topc(X1)|v2_struct_0(X1)|~v2_pre_topc(X1)|~v3_pre_topc(u1_struct_0(X1),X1)|~l1_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_54]), c_0_44])])).
% 0.51/0.67  cnf(c_0_62, plain, (v3_pre_topc(k2_struct_0(X1),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.51/0.67  cnf(c_0_63, negated_conjecture, (g1_pre_topc(k2_struct_0(esk1_0),u1_pre_topc(esk1_0))=k6_tmap_1(esk1_0,esk2_0)|v3_pre_topc(esk2_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_36]), c_0_19])])).
% 0.51/0.67  cnf(c_0_64, negated_conjecture, (~v3_pre_topc(esk2_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_57, c_0_58])])).
% 0.51/0.67  cnf(c_0_65, plain, (g1_pre_topc(k2_struct_0(X1),k5_tmap_1(X1,k2_struct_0(X1)))=k6_tmap_1(X1,k2_struct_0(X1))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 0.51/0.67  cnf(c_0_66, plain, (k5_tmap_1(X1,k2_struct_0(X1))=u1_pre_topc(X1)|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_35]), c_0_36]), c_0_62])).
% 0.51/0.67  cnf(c_0_67, negated_conjecture, (g1_pre_topc(k2_struct_0(esk1_0),u1_pre_topc(esk1_0))=k6_tmap_1(esk1_0,esk2_0)), inference(sr,[status(thm)],[c_0_63, c_0_64])).
% 0.51/0.67  cnf(c_0_68, plain, (g1_pre_topc(k2_struct_0(X1),u1_pre_topc(X1))=k6_tmap_1(X1,k2_struct_0(X1))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 0.51/0.67  cnf(c_0_69, plain, (v3_pre_topc(X1,X2)|~r2_hidden(X1,u1_pre_topc(X2))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.51/0.67  cnf(c_0_70, negated_conjecture, (k6_tmap_1(esk1_0,k2_struct_0(esk1_0))=k6_tmap_1(esk1_0,esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_18]), c_0_19])]), c_0_20])).
% 0.51/0.67  cnf(c_0_71, plain, (r2_hidden(X2,u1_pre_topc(X1))|v2_struct_0(X1)|u1_pre_topc(X1)!=k5_tmap_1(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.51/0.67  cnf(c_0_72, plain, (v3_pre_topc(u1_struct_0(X1),X1)|~r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_69, c_0_44])).
% 0.51/0.67  cnf(c_0_73, negated_conjecture, (u1_struct_0(esk1_0)=k2_struct_0(esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_70]), c_0_29]), c_0_18]), c_0_19])]), c_0_20])).
% 0.51/0.67  cnf(c_0_74, plain, (v2_struct_0(X1)|r2_hidden(k2_struct_0(X1),u1_pre_topc(X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_71, c_0_66])).
% 0.51/0.67  cnf(c_0_75, negated_conjecture, (v3_pre_topc(k2_struct_0(esk1_0),esk1_0)|~r2_hidden(k2_struct_0(esk1_0),u1_pre_topc(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_73]), c_0_19])])).
% 0.51/0.67  cnf(c_0_76, plain, (v2_struct_0(X1)|r2_hidden(k2_struct_0(X1),u1_pre_topc(X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_35]), c_0_44])]), c_0_36])).
% 0.51/0.67  cnf(c_0_77, negated_conjecture, (r2_hidden(X1,u1_pre_topc(esk1_0))|~v3_pre_topc(X1,esk1_0)|~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_73]), c_0_19])])).
% 0.51/0.67  cnf(c_0_78, negated_conjecture, (v3_pre_topc(k2_struct_0(esk1_0),esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_76]), c_0_18]), c_0_19])]), c_0_20])).
% 0.51/0.67  cnf(c_0_79, negated_conjecture, (r2_hidden(k2_struct_0(esk1_0),u1_pre_topc(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_44]), c_0_78])])).
% 0.51/0.67  cnf(c_0_80, negated_conjecture, (k5_tmap_1(esk1_0,k2_struct_0(esk1_0))=u1_pre_topc(esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_79]), c_0_18]), c_0_19]), c_0_73]), c_0_44])]), c_0_20])).
% 0.51/0.67  cnf(c_0_81, plain, (v3_pre_topc(X1,X2)|~r2_hidden(X1,u1_pre_topc(X2))|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(X2)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_35]), c_0_36])).
% 0.51/0.67  cnf(c_0_82, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(k2_struct_0(esk1_0)))), inference(rw,[status(thm)],[c_0_17, c_0_73])).
% 0.51/0.67  cnf(c_0_83, negated_conjecture, (k5_tmap_1(esk1_0,esk2_0)=u1_pre_topc(esk1_0)), inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_70]), c_0_40]), c_0_18]), c_0_19])]), c_0_20]), c_0_80])).
% 0.51/0.67  cnf(c_0_84, negated_conjecture, (~r2_hidden(esk2_0,u1_pre_topc(esk1_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_82]), c_0_19])]), c_0_64])).
% 0.51/0.67  cnf(c_0_85, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_83]), c_0_18]), c_0_19]), c_0_73]), c_0_82])]), c_0_20]), c_0_84]), ['proof']).
% 0.51/0.67  # SZS output end CNFRefutation
% 0.51/0.67  # Proof object total steps             : 86
% 0.51/0.67  # Proof object clause steps            : 63
% 0.51/0.67  # Proof object formula steps           : 23
% 0.51/0.67  # Proof object conjectures             : 33
% 0.51/0.67  # Proof object clause conjectures      : 30
% 0.51/0.67  # Proof object formula conjectures     : 3
% 0.51/0.67  # Proof object initial clauses used    : 20
% 0.51/0.67  # Proof object initial formulas used   : 11
% 0.51/0.67  # Proof object generating inferences   : 38
% 0.51/0.67  # Proof object simplifying inferences  : 90
% 0.51/0.67  # Training examples: 0 positive, 0 negative
% 0.51/0.67  # Parsed axioms                        : 11
% 0.51/0.67  # Removed by relevancy pruning/SinE    : 0
% 0.51/0.67  # Initial clauses                      : 21
% 0.51/0.67  # Removed in clause preprocessing      : 1
% 0.51/0.67  # Initial clauses in saturation        : 20
% 0.51/0.67  # Processed clauses                    : 2608
% 0.51/0.67  # ...of these trivial                  : 3
% 0.51/0.67  # ...subsumed                          : 1698
% 0.51/0.67  # ...remaining for further processing  : 907
% 0.51/0.67  # Other redundant clauses eliminated   : 0
% 0.51/0.67  # Clauses deleted for lack of memory   : 0
% 0.51/0.67  # Backward-subsumed                    : 204
% 0.51/0.67  # Backward-rewritten                   : 408
% 0.51/0.67  # Generated clauses                    : 5795
% 0.51/0.67  # ...of the previous two non-trivial   : 6076
% 0.51/0.67  # Contextual simplify-reflections      : 451
% 0.51/0.67  # Paramodulations                      : 5794
% 0.51/0.67  # Factorizations                       : 0
% 0.51/0.67  # Equation resolutions                 : 0
% 0.51/0.67  # Propositional unsat checks           : 0
% 0.51/0.67  #    Propositional check models        : 0
% 0.51/0.67  #    Propositional check unsatisfiable : 0
% 0.51/0.67  #    Propositional clauses             : 0
% 0.51/0.67  #    Propositional clauses after purity: 0
% 0.51/0.67  #    Propositional unsat core size     : 0
% 0.51/0.67  #    Propositional preprocessing time  : 0.000
% 0.51/0.67  #    Propositional encoding time       : 0.000
% 0.51/0.67  #    Propositional solver time         : 0.000
% 0.51/0.67  #    Success case prop preproc time    : 0.000
% 0.51/0.67  #    Success case prop encoding time   : 0.000
% 0.51/0.67  #    Success case prop solver time     : 0.000
% 0.51/0.67  # Current number of processed clauses  : 274
% 0.51/0.67  #    Positive orientable unit clauses  : 17
% 0.51/0.67  #    Positive unorientable unit clauses: 0
% 0.51/0.67  #    Negative unit clauses             : 4
% 0.51/0.67  #    Non-unit-clauses                  : 253
% 0.51/0.67  # Current number of unprocessed clauses: 3433
% 0.51/0.67  # ...number of literals in the above   : 21227
% 0.51/0.67  # Current number of archived formulas  : 0
% 0.51/0.67  # Current number of archived clauses   : 634
% 0.51/0.67  # Clause-clause subsumption calls (NU) : 237651
% 0.51/0.67  # Rec. Clause-clause subsumption calls : 43448
% 0.51/0.67  # Non-unit clause-clause subsumptions  : 1851
% 0.51/0.67  # Unit Clause-clause subsumption calls : 1383
% 0.51/0.67  # Rewrite failures with RHS unbound    : 0
% 0.51/0.67  # BW rewrite match attempts            : 12
% 0.51/0.67  # BW rewrite match successes           : 10
% 0.51/0.67  # Condensation attempts                : 0
% 0.51/0.67  # Condensation successes               : 0
% 0.51/0.67  # Termbank termtop insertions          : 237235
% 0.51/0.67  
% 0.51/0.67  # -------------------------------------------------
% 0.51/0.67  # User time                : 0.315 s
% 0.51/0.67  # System time              : 0.006 s
% 0.51/0.67  # Total time               : 0.321 s
% 0.51/0.67  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
