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
% DateTime   : Thu Dec  3 11:18:13 EST 2020

% Result     : Theorem 0.10s
% Output     : CNFRefutation 0.10s
% Verified   : 
% Statistics : Number of formulae       :   84 (1855 expanded)
%              Number of clauses        :   59 ( 608 expanded)
%              Number of leaves         :   12 ( 454 expanded)
%              Depth                    :   17
%              Number of atoms          :  291 (9250 expanded)
%              Number of equality atoms :   41 (1468 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   15 (   2 average)
%              Maximal term depth       :    4 (   2 average)

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

fof(dt_m2_connsp_2,axiom,(
    ! [X1,X2] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ! [X3] :
          ( m2_connsp_2(X3,X1,X2)
         => m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m2_connsp_2)).

fof(t35_connsp_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => m2_connsp_2(k2_struct_0(X1),X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_connsp_2)).

fof(t44_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => r1_tarski(k1_tops_1(X1,X2),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

fof(d2_connsp_2,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( m2_connsp_2(X3,X1,X2)
              <=> r1_tarski(X2,k1_tops_1(X1,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_connsp_2)).

fof(d5_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_pre_topc(X2,X1)
          <=> r2_hidden(X2,u1_pre_topc(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_pre_topc)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

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

fof(fc9_tops_1,axiom,(
    ! [X1,X2] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => v3_pre_topc(k1_tops_1(X1,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

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

fof(c_0_12,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( v3_pre_topc(X2,X1)
            <=> g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k6_tmap_1(X1,X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t106_tmap_1])).

fof(c_0_13,plain,(
    ! [X20,X21,X22] :
      ( ~ v2_pre_topc(X20)
      | ~ l1_pre_topc(X20)
      | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))
      | ~ m2_connsp_2(X22,X20,X21)
      | m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X20))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m2_connsp_2])])])).

fof(c_0_14,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & ( ~ v3_pre_topc(esk2_0,esk1_0)
      | g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)) != k6_tmap_1(esk1_0,esk2_0) )
    & ( v3_pre_topc(esk2_0,esk1_0)
      | g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)) = k6_tmap_1(esk1_0,esk2_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_12])])])])).

cnf(c_0_15,plain,
    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m2_connsp_2(X3,X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_16,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_17,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_19,plain,(
    ! [X23,X24] :
      ( v2_struct_0(X23)
      | ~ v2_pre_topc(X23)
      | ~ l1_pre_topc(X23)
      | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))
      | m2_connsp_2(k2_struct_0(X23),X23,X24) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t35_connsp_2])])])])).

cnf(c_0_20,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m2_connsp_2(X1,esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17]),c_0_18])])).

cnf(c_0_21,plain,
    ( v2_struct_0(X1)
    | m2_connsp_2(k2_struct_0(X1),X1,X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_22,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m2_connsp_2(X2,esk1_0,esk2_0)
    | ~ m2_connsp_2(X1,esk1_0,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_20]),c_0_17]),c_0_18])])).

cnf(c_0_24,negated_conjecture,
    ( m2_connsp_2(k2_struct_0(esk1_0),esk1_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_16]),c_0_17]),c_0_18])]),c_0_22])).

fof(c_0_25,plain,(
    ! [X15,X16] :
      ( ~ l1_pre_topc(X15)
      | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
      | r1_tarski(k1_tops_1(X15,X16),X16) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_tops_1])])])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m2_connsp_2(X1,esk1_0,k2_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_27,negated_conjecture,
    ( m2_connsp_2(k2_struct_0(esk1_0),esk1_0,X1)
    | ~ m2_connsp_2(X1,esk1_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_20]),c_0_17]),c_0_18])]),c_0_22])).

fof(c_0_28,plain,(
    ! [X17,X18,X19] :
      ( ( ~ m2_connsp_2(X19,X17,X18)
        | r1_tarski(X18,k1_tops_1(X17,X19))
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X17)))
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))
        | ~ v2_pre_topc(X17)
        | ~ l1_pre_topc(X17) )
      & ( ~ r1_tarski(X18,k1_tops_1(X17,X19))
        | m2_connsp_2(X19,X17,X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X17)))
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))
        | ~ v2_pre_topc(X17)
        | ~ l1_pre_topc(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_connsp_2])])])])).

fof(c_0_29,plain,(
    ! [X10,X11] :
      ( ( ~ v3_pre_topc(X11,X10)
        | r2_hidden(X11,u1_pre_topc(X10))
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))
        | ~ l1_pre_topc(X10) )
      & ( ~ r2_hidden(X11,u1_pre_topc(X10))
        | v3_pre_topc(X11,X10)
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))
        | ~ l1_pre_topc(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_pre_topc])])])])).

fof(c_0_30,plain,(
    ! [X4,X5] :
      ( ( r1_tarski(X4,X5)
        | X4 != X5 )
      & ( r1_tarski(X5,X4)
        | X4 != X5 )
      & ( ~ r1_tarski(X4,X5)
        | ~ r1_tarski(X5,X4)
        | X4 = X5 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_31,plain,
    ( r1_tarski(k1_tops_1(X1,X2),X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_32,negated_conjecture,
    ( m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_24])])).

cnf(c_0_33,plain,
    ( r1_tarski(X3,k1_tops_1(X2,X1))
    | ~ m2_connsp_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_34,plain,(
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

cnf(c_0_35,plain,
    ( r2_hidden(X1,u1_pre_topc(X2))
    | ~ v3_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_36,plain,(
    ! [X13,X14] :
      ( ~ v2_pre_topc(X13)
      | ~ l1_pre_topc(X13)
      | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
      | v3_pre_topc(k1_tops_1(X13,X14),X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc9_tops_1])])).

cnf(c_0_37,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_38,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,k2_struct_0(esk1_0)),k2_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_18])])).

cnf(c_0_39,plain,
    ( r1_tarski(X1,k1_tops_1(X2,X3))
    | ~ m2_connsp_2(X3,X2,X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(csr,[status(thm)],[c_0_33,c_0_15])).

fof(c_0_40,plain,(
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

fof(c_0_41,plain,(
    ! [X25,X26] :
      ( ( v1_pre_topc(k6_tmap_1(X25,X26))
        | v2_struct_0(X25)
        | ~ v2_pre_topc(X25)
        | ~ l1_pre_topc(X25)
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25))) )
      & ( v2_pre_topc(k6_tmap_1(X25,X26))
        | v2_struct_0(X25)
        | ~ v2_pre_topc(X25)
        | ~ l1_pre_topc(X25)
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25))) )
      & ( l1_pre_topc(k6_tmap_1(X25,X26))
        | v2_struct_0(X25)
        | ~ v2_pre_topc(X25)
        | ~ l1_pre_topc(X25)
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_tmap_1])])])])).

cnf(c_0_42,plain,
    ( u1_pre_topc(X2) = k5_tmap_1(X2,X1)
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,u1_pre_topc(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(X1,u1_pre_topc(esk1_0))
    | ~ m2_connsp_2(X1,esk1_0,esk2_0)
    | ~ v3_pre_topc(X1,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_20]),c_0_18])])).

cnf(c_0_44,plain,
    ( v3_pre_topc(k1_tops_1(X1,X2),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_45,negated_conjecture,
    ( k1_tops_1(esk1_0,k2_struct_0(esk1_0)) = k2_struct_0(esk1_0)
    | ~ r1_tarski(k2_struct_0(esk1_0),k1_tops_1(esk1_0,k2_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_46,negated_conjecture,
    ( r1_tarski(X1,k1_tops_1(esk1_0,X2))
    | ~ m2_connsp_2(X1,esk1_0,esk2_0)
    | ~ m2_connsp_2(X2,esk1_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_20]),c_0_17]),c_0_18])])).

cnf(c_0_47,negated_conjecture,
    ( m2_connsp_2(k2_struct_0(esk1_0),esk1_0,k2_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_32]),c_0_17]),c_0_18])]),c_0_22])).

fof(c_0_48,plain,(
    ! [X8] :
      ( ~ l1_pre_topc(X8)
      | ~ v1_pre_topc(X8)
      | X8 = g1_pre_topc(u1_struct_0(X8),u1_pre_topc(X8)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[abstractness_v1_pre_topc])])).

cnf(c_0_49,plain,
    ( u1_struct_0(k6_tmap_1(X1,X2)) = u1_struct_0(X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_50,plain,
    ( v1_pre_topc(k6_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_51,plain,
    ( l1_pre_topc(k6_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_52,negated_conjecture,
    ( k5_tmap_1(esk1_0,X1) = u1_pre_topc(esk1_0)
    | ~ m2_connsp_2(X1,esk1_0,esk2_0)
    | ~ v3_pre_topc(X1,esk1_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_17]),c_0_18])]),c_0_22]),c_0_20])).

cnf(c_0_53,negated_conjecture,
    ( v3_pre_topc(k1_tops_1(esk1_0,k2_struct_0(esk1_0)),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_32]),c_0_17]),c_0_18])])).

cnf(c_0_54,negated_conjecture,
    ( k1_tops_1(esk1_0,k2_struct_0(esk1_0)) = k2_struct_0(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_24]),c_0_47])])).

cnf(c_0_55,plain,
    ( X1 = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ l1_pre_topc(X1)
    | ~ v1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_56,negated_conjecture,
    ( u1_struct_0(k6_tmap_1(esk1_0,esk2_0)) = u1_struct_0(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_16]),c_0_17]),c_0_18])]),c_0_22])).

cnf(c_0_57,negated_conjecture,
    ( v1_pre_topc(k6_tmap_1(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_16]),c_0_17]),c_0_18])]),c_0_22])).

cnf(c_0_58,negated_conjecture,
    ( l1_pre_topc(k6_tmap_1(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_16]),c_0_17]),c_0_18])]),c_0_22])).

cnf(c_0_59,plain,
    ( u1_pre_topc(k6_tmap_1(X1,X2)) = k5_tmap_1(X1,X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_60,negated_conjecture,
    ( k5_tmap_1(esk1_0,k2_struct_0(esk1_0)) = u1_pre_topc(esk1_0)
    | ~ v3_pre_topc(k2_struct_0(esk1_0),esk1_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_24])).

cnf(c_0_61,negated_conjecture,
    ( v3_pre_topc(k2_struct_0(esk1_0),esk1_0) ),
    inference(rw,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_62,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(k6_tmap_1(esk1_0,esk2_0))) = k6_tmap_1(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_57]),c_0_58])])).

cnf(c_0_63,negated_conjecture,
    ( u1_pre_topc(k6_tmap_1(esk1_0,esk2_0)) = k5_tmap_1(esk1_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_16]),c_0_17]),c_0_18])]),c_0_22])).

cnf(c_0_64,negated_conjecture,
    ( r2_hidden(esk2_0,u1_pre_topc(esk1_0))
    | ~ v3_pre_topc(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_16]),c_0_18])])).

cnf(c_0_65,negated_conjecture,
    ( u1_pre_topc(k6_tmap_1(esk1_0,k2_struct_0(esk1_0))) = k5_tmap_1(esk1_0,k2_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_32]),c_0_17]),c_0_18])]),c_0_22])).

cnf(c_0_66,negated_conjecture,
    ( k5_tmap_1(esk1_0,k2_struct_0(esk1_0)) = u1_pre_topc(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_60,c_0_61])])).

cnf(c_0_67,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk1_0),k5_tmap_1(esk1_0,esk2_0)) = k6_tmap_1(esk1_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_68,negated_conjecture,
    ( k5_tmap_1(esk1_0,esk2_0) = u1_pre_topc(esk1_0)
    | ~ v3_pre_topc(esk2_0,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_64]),c_0_17]),c_0_18]),c_0_16])]),c_0_22])).

cnf(c_0_69,negated_conjecture,
    ( v3_pre_topc(esk2_0,esk1_0)
    | g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)) = k6_tmap_1(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_70,negated_conjecture,
    ( u1_pre_topc(k6_tmap_1(esk1_0,k2_struct_0(esk1_0))) = u1_pre_topc(esk1_0) ),
    inference(rw,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_71,negated_conjecture,
    ( u1_struct_0(k6_tmap_1(esk1_0,k2_struct_0(esk1_0))) = u1_struct_0(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_32]),c_0_17]),c_0_18])]),c_0_22])).

cnf(c_0_72,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)) = k6_tmap_1(esk1_0,esk2_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_69])).

cnf(c_0_73,negated_conjecture,
    ( v1_pre_topc(k6_tmap_1(esk1_0,k2_struct_0(esk1_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_32]),c_0_17]),c_0_18])]),c_0_22])).

cnf(c_0_74,negated_conjecture,
    ( l1_pre_topc(k6_tmap_1(esk1_0,k2_struct_0(esk1_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_32]),c_0_17]),c_0_18])]),c_0_22])).

cnf(c_0_75,negated_conjecture,
    ( k6_tmap_1(esk1_0,k2_struct_0(esk1_0)) = k6_tmap_1(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_70]),c_0_71]),c_0_72]),c_0_73]),c_0_74])])).

cnf(c_0_76,plain,
    ( v3_pre_topc(X1,X2)
    | ~ r2_hidden(X1,u1_pre_topc(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_77,plain,
    ( r2_hidden(X2,u1_pre_topc(X1))
    | v2_struct_0(X1)
    | u1_pre_topc(X1) != k5_tmap_1(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_78,negated_conjecture,
    ( k5_tmap_1(esk1_0,esk2_0) = u1_pre_topc(esk1_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_70,c_0_75]),c_0_63])).

cnf(c_0_79,negated_conjecture,
    ( ~ v3_pre_topc(esk2_0,esk1_0)
    | g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)) != k6_tmap_1(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_80,negated_conjecture,
    ( v3_pre_topc(esk2_0,esk1_0)
    | ~ r2_hidden(esk2_0,u1_pre_topc(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_16]),c_0_18])])).

cnf(c_0_81,negated_conjecture,
    ( r2_hidden(esk2_0,u1_pre_topc(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_17]),c_0_18]),c_0_16])]),c_0_22])).

cnf(c_0_82,negated_conjecture,
    ( ~ v3_pre_topc(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_79,c_0_72])])).

cnf(c_0_83,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_80,c_0_81])]),c_0_82]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.06  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.07  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.06/0.25  % Computer   : n013.cluster.edu
% 0.06/0.25  % Model      : x86_64 x86_64
% 0.06/0.25  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.06/0.25  % Memory     : 8042.1875MB
% 0.06/0.25  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.06/0.25  % CPULimit   : 60
% 0.06/0.25  % WCLimit    : 600
% 0.06/0.25  % DateTime   : Tue Dec  1 14:18:54 EST 2020
% 0.06/0.25  % CPUTime    : 
% 0.06/0.25  # Version: 2.5pre002
% 0.06/0.25  # No SInE strategy applied
% 0.06/0.25  # Trying AutoSched0 for 299 seconds
% 0.10/0.31  # AutoSched0-Mode selected heuristic G_E___208_C12_02_nc_F1_SE_CS_SP_PS_S06DN
% 0.10/0.31  # and selection function SelectNewComplexAHPExceptUniqMaxHorn.
% 0.10/0.31  #
% 0.10/0.31  # Preprocessing time       : 0.014 s
% 0.10/0.31  # Presaturation interreduction done
% 0.10/0.31  
% 0.10/0.31  # Proof found!
% 0.10/0.31  # SZS status Theorem
% 0.10/0.31  # SZS output start CNFRefutation
% 0.10/0.31  fof(t106_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))=k6_tmap_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_tmap_1)).
% 0.10/0.31  fof(dt_m2_connsp_2, axiom, ![X1, X2]:(((v2_pre_topc(X1)&l1_pre_topc(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>![X3]:(m2_connsp_2(X3,X1,X2)=>m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m2_connsp_2)).
% 0.10/0.31  fof(t35_connsp_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>m2_connsp_2(k2_struct_0(X1),X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_connsp_2)).
% 0.10/0.31  fof(t44_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>r1_tarski(k1_tops_1(X1,X2),X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_1)).
% 0.10/0.31  fof(d2_connsp_2, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(m2_connsp_2(X3,X1,X2)<=>r1_tarski(X2,k1_tops_1(X1,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_connsp_2)).
% 0.10/0.31  fof(d5_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>r2_hidden(X2,u1_pre_topc(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_pre_topc)).
% 0.10/0.31  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.10/0.31  fof(t103_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(r2_hidden(X2,u1_pre_topc(X1))<=>u1_pre_topc(X1)=k5_tmap_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t103_tmap_1)).
% 0.10/0.31  fof(fc9_tops_1, axiom, ![X1, X2]:(((v2_pre_topc(X1)&l1_pre_topc(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>v3_pre_topc(k1_tops_1(X1,X2),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_tops_1)).
% 0.10/0.31  fof(t104_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(u1_struct_0(k6_tmap_1(X1,X2))=u1_struct_0(X1)&u1_pre_topc(k6_tmap_1(X1,X2))=k5_tmap_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t104_tmap_1)).
% 0.10/0.31  fof(dt_k6_tmap_1, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>((v1_pre_topc(k6_tmap_1(X1,X2))&v2_pre_topc(k6_tmap_1(X1,X2)))&l1_pre_topc(k6_tmap_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_tmap_1)).
% 0.10/0.31  fof(abstractness_v1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>(v1_pre_topc(X1)=>X1=g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', abstractness_v1_pre_topc)).
% 0.10/0.31  fof(c_0_12, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))=k6_tmap_1(X1,X2))))), inference(assume_negation,[status(cth)],[t106_tmap_1])).
% 0.10/0.31  fof(c_0_13, plain, ![X20, X21, X22]:(~v2_pre_topc(X20)|~l1_pre_topc(X20)|~m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))|(~m2_connsp_2(X22,X20,X21)|m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X20))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m2_connsp_2])])])).
% 0.10/0.31  fof(c_0_14, negated_conjecture, (((~v2_struct_0(esk1_0)&v2_pre_topc(esk1_0))&l1_pre_topc(esk1_0))&(m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&((~v3_pre_topc(esk2_0,esk1_0)|g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))!=k6_tmap_1(esk1_0,esk2_0))&(v3_pre_topc(esk2_0,esk1_0)|g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))=k6_tmap_1(esk1_0,esk2_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_12])])])])).
% 0.10/0.31  cnf(c_0_15, plain, (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m2_connsp_2(X3,X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.10/0.31  cnf(c_0_16, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.10/0.31  cnf(c_0_17, negated_conjecture, (v2_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.10/0.31  cnf(c_0_18, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.10/0.31  fof(c_0_19, plain, ![X23, X24]:(v2_struct_0(X23)|~v2_pre_topc(X23)|~l1_pre_topc(X23)|(~m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))|m2_connsp_2(k2_struct_0(X23),X23,X24))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t35_connsp_2])])])])).
% 0.10/0.31  cnf(c_0_20, negated_conjecture, (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))|~m2_connsp_2(X1,esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_17]), c_0_18])])).
% 0.10/0.31  cnf(c_0_21, plain, (v2_struct_0(X1)|m2_connsp_2(k2_struct_0(X1),X1,X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.10/0.31  cnf(c_0_22, negated_conjecture, (~v2_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.10/0.31  cnf(c_0_23, negated_conjecture, (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))|~m2_connsp_2(X2,esk1_0,esk2_0)|~m2_connsp_2(X1,esk1_0,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_20]), c_0_17]), c_0_18])])).
% 0.10/0.31  cnf(c_0_24, negated_conjecture, (m2_connsp_2(k2_struct_0(esk1_0),esk1_0,esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_16]), c_0_17]), c_0_18])]), c_0_22])).
% 0.10/0.31  fof(c_0_25, plain, ![X15, X16]:(~l1_pre_topc(X15)|(~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))|r1_tarski(k1_tops_1(X15,X16),X16))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_tops_1])])])).
% 0.10/0.31  cnf(c_0_26, negated_conjecture, (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))|~m2_connsp_2(X1,esk1_0,k2_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.10/0.31  cnf(c_0_27, negated_conjecture, (m2_connsp_2(k2_struct_0(esk1_0),esk1_0,X1)|~m2_connsp_2(X1,esk1_0,esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_20]), c_0_17]), c_0_18])]), c_0_22])).
% 0.10/0.31  fof(c_0_28, plain, ![X17, X18, X19]:((~m2_connsp_2(X19,X17,X18)|r1_tarski(X18,k1_tops_1(X17,X19))|~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X17)))|~m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))|(~v2_pre_topc(X17)|~l1_pre_topc(X17)))&(~r1_tarski(X18,k1_tops_1(X17,X19))|m2_connsp_2(X19,X17,X18)|~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X17)))|~m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))|(~v2_pre_topc(X17)|~l1_pre_topc(X17)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_connsp_2])])])])).
% 0.10/0.31  fof(c_0_29, plain, ![X10, X11]:((~v3_pre_topc(X11,X10)|r2_hidden(X11,u1_pre_topc(X10))|~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))|~l1_pre_topc(X10))&(~r2_hidden(X11,u1_pre_topc(X10))|v3_pre_topc(X11,X10)|~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))|~l1_pre_topc(X10))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_pre_topc])])])])).
% 0.10/0.31  fof(c_0_30, plain, ![X4, X5]:(((r1_tarski(X4,X5)|X4!=X5)&(r1_tarski(X5,X4)|X4!=X5))&(~r1_tarski(X4,X5)|~r1_tarski(X5,X4)|X4=X5)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.10/0.31  cnf(c_0_31, plain, (r1_tarski(k1_tops_1(X1,X2),X2)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.10/0.31  cnf(c_0_32, negated_conjecture, (m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_24])])).
% 0.10/0.31  cnf(c_0_33, plain, (r1_tarski(X3,k1_tops_1(X2,X1))|~m2_connsp_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.10/0.31  fof(c_0_34, plain, ![X27, X28]:((~r2_hidden(X28,u1_pre_topc(X27))|u1_pre_topc(X27)=k5_tmap_1(X27,X28)|~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))|(v2_struct_0(X27)|~v2_pre_topc(X27)|~l1_pre_topc(X27)))&(u1_pre_topc(X27)!=k5_tmap_1(X27,X28)|r2_hidden(X28,u1_pre_topc(X27))|~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))|(v2_struct_0(X27)|~v2_pre_topc(X27)|~l1_pre_topc(X27)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t103_tmap_1])])])])])).
% 0.10/0.31  cnf(c_0_35, plain, (r2_hidden(X1,u1_pre_topc(X2))|~v3_pre_topc(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.10/0.31  fof(c_0_36, plain, ![X13, X14]:(~v2_pre_topc(X13)|~l1_pre_topc(X13)|~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))|v3_pre_topc(k1_tops_1(X13,X14),X13)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc9_tops_1])])).
% 0.10/0.31  cnf(c_0_37, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.10/0.31  cnf(c_0_38, negated_conjecture, (r1_tarski(k1_tops_1(esk1_0,k2_struct_0(esk1_0)),k2_struct_0(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_18])])).
% 0.10/0.31  cnf(c_0_39, plain, (r1_tarski(X1,k1_tops_1(X2,X3))|~m2_connsp_2(X3,X2,X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))), inference(csr,[status(thm)],[c_0_33, c_0_15])).
% 0.10/0.31  fof(c_0_40, plain, ![X29, X30]:((u1_struct_0(k6_tmap_1(X29,X30))=u1_struct_0(X29)|~m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))|(v2_struct_0(X29)|~v2_pre_topc(X29)|~l1_pre_topc(X29)))&(u1_pre_topc(k6_tmap_1(X29,X30))=k5_tmap_1(X29,X30)|~m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))|(v2_struct_0(X29)|~v2_pre_topc(X29)|~l1_pre_topc(X29)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t104_tmap_1])])])])])).
% 0.10/0.31  fof(c_0_41, plain, ![X25, X26]:(((v1_pre_topc(k6_tmap_1(X25,X26))|(v2_struct_0(X25)|~v2_pre_topc(X25)|~l1_pre_topc(X25)|~m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))))&(v2_pre_topc(k6_tmap_1(X25,X26))|(v2_struct_0(X25)|~v2_pre_topc(X25)|~l1_pre_topc(X25)|~m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25))))))&(l1_pre_topc(k6_tmap_1(X25,X26))|(v2_struct_0(X25)|~v2_pre_topc(X25)|~l1_pre_topc(X25)|~m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_tmap_1])])])])).
% 0.10/0.31  cnf(c_0_42, plain, (u1_pre_topc(X2)=k5_tmap_1(X2,X1)|v2_struct_0(X2)|~r2_hidden(X1,u1_pre_topc(X2))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.10/0.31  cnf(c_0_43, negated_conjecture, (r2_hidden(X1,u1_pre_topc(esk1_0))|~m2_connsp_2(X1,esk1_0,esk2_0)|~v3_pre_topc(X1,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_20]), c_0_18])])).
% 0.10/0.31  cnf(c_0_44, plain, (v3_pre_topc(k1_tops_1(X1,X2),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.10/0.31  cnf(c_0_45, negated_conjecture, (k1_tops_1(esk1_0,k2_struct_0(esk1_0))=k2_struct_0(esk1_0)|~r1_tarski(k2_struct_0(esk1_0),k1_tops_1(esk1_0,k2_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.10/0.31  cnf(c_0_46, negated_conjecture, (r1_tarski(X1,k1_tops_1(esk1_0,X2))|~m2_connsp_2(X1,esk1_0,esk2_0)|~m2_connsp_2(X2,esk1_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_20]), c_0_17]), c_0_18])])).
% 0.10/0.31  cnf(c_0_47, negated_conjecture, (m2_connsp_2(k2_struct_0(esk1_0),esk1_0,k2_struct_0(esk1_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_32]), c_0_17]), c_0_18])]), c_0_22])).
% 0.10/0.31  fof(c_0_48, plain, ![X8]:(~l1_pre_topc(X8)|(~v1_pre_topc(X8)|X8=g1_pre_topc(u1_struct_0(X8),u1_pre_topc(X8)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[abstractness_v1_pre_topc])])).
% 0.10/0.31  cnf(c_0_49, plain, (u1_struct_0(k6_tmap_1(X1,X2))=u1_struct_0(X1)|v2_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.10/0.31  cnf(c_0_50, plain, (v1_pre_topc(k6_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.10/0.31  cnf(c_0_51, plain, (l1_pre_topc(k6_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.10/0.31  cnf(c_0_52, negated_conjecture, (k5_tmap_1(esk1_0,X1)=u1_pre_topc(esk1_0)|~m2_connsp_2(X1,esk1_0,esk2_0)|~v3_pre_topc(X1,esk1_0)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_17]), c_0_18])]), c_0_22]), c_0_20])).
% 0.10/0.31  cnf(c_0_53, negated_conjecture, (v3_pre_topc(k1_tops_1(esk1_0,k2_struct_0(esk1_0)),esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_32]), c_0_17]), c_0_18])])).
% 0.10/0.31  cnf(c_0_54, negated_conjecture, (k1_tops_1(esk1_0,k2_struct_0(esk1_0))=k2_struct_0(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_24]), c_0_47])])).
% 0.10/0.31  cnf(c_0_55, plain, (X1=g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))|~l1_pre_topc(X1)|~v1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.10/0.31  cnf(c_0_56, negated_conjecture, (u1_struct_0(k6_tmap_1(esk1_0,esk2_0))=u1_struct_0(esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_16]), c_0_17]), c_0_18])]), c_0_22])).
% 0.10/0.31  cnf(c_0_57, negated_conjecture, (v1_pre_topc(k6_tmap_1(esk1_0,esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_16]), c_0_17]), c_0_18])]), c_0_22])).
% 0.10/0.31  cnf(c_0_58, negated_conjecture, (l1_pre_topc(k6_tmap_1(esk1_0,esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_16]), c_0_17]), c_0_18])]), c_0_22])).
% 0.10/0.31  cnf(c_0_59, plain, (u1_pre_topc(k6_tmap_1(X1,X2))=k5_tmap_1(X1,X2)|v2_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.10/0.31  cnf(c_0_60, negated_conjecture, (k5_tmap_1(esk1_0,k2_struct_0(esk1_0))=u1_pre_topc(esk1_0)|~v3_pre_topc(k2_struct_0(esk1_0),esk1_0)), inference(spm,[status(thm)],[c_0_52, c_0_24])).
% 0.10/0.31  cnf(c_0_61, negated_conjecture, (v3_pre_topc(k2_struct_0(esk1_0),esk1_0)), inference(rw,[status(thm)],[c_0_53, c_0_54])).
% 0.10/0.31  cnf(c_0_62, negated_conjecture, (g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(k6_tmap_1(esk1_0,esk2_0)))=k6_tmap_1(esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_57]), c_0_58])])).
% 0.10/0.31  cnf(c_0_63, negated_conjecture, (u1_pre_topc(k6_tmap_1(esk1_0,esk2_0))=k5_tmap_1(esk1_0,esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_16]), c_0_17]), c_0_18])]), c_0_22])).
% 0.10/0.31  cnf(c_0_64, negated_conjecture, (r2_hidden(esk2_0,u1_pre_topc(esk1_0))|~v3_pre_topc(esk2_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_16]), c_0_18])])).
% 0.10/0.31  cnf(c_0_65, negated_conjecture, (u1_pre_topc(k6_tmap_1(esk1_0,k2_struct_0(esk1_0)))=k5_tmap_1(esk1_0,k2_struct_0(esk1_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_32]), c_0_17]), c_0_18])]), c_0_22])).
% 0.10/0.31  cnf(c_0_66, negated_conjecture, (k5_tmap_1(esk1_0,k2_struct_0(esk1_0))=u1_pre_topc(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_60, c_0_61])])).
% 0.10/0.31  cnf(c_0_67, negated_conjecture, (g1_pre_topc(u1_struct_0(esk1_0),k5_tmap_1(esk1_0,esk2_0))=k6_tmap_1(esk1_0,esk2_0)), inference(rw,[status(thm)],[c_0_62, c_0_63])).
% 0.10/0.31  cnf(c_0_68, negated_conjecture, (k5_tmap_1(esk1_0,esk2_0)=u1_pre_topc(esk1_0)|~v3_pre_topc(esk2_0,esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_64]), c_0_17]), c_0_18]), c_0_16])]), c_0_22])).
% 0.10/0.31  cnf(c_0_69, negated_conjecture, (v3_pre_topc(esk2_0,esk1_0)|g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))=k6_tmap_1(esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.10/0.31  cnf(c_0_70, negated_conjecture, (u1_pre_topc(k6_tmap_1(esk1_0,k2_struct_0(esk1_0)))=u1_pre_topc(esk1_0)), inference(rw,[status(thm)],[c_0_65, c_0_66])).
% 0.10/0.31  cnf(c_0_71, negated_conjecture, (u1_struct_0(k6_tmap_1(esk1_0,k2_struct_0(esk1_0)))=u1_struct_0(esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_32]), c_0_17]), c_0_18])]), c_0_22])).
% 0.10/0.31  cnf(c_0_72, negated_conjecture, (g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))=k6_tmap_1(esk1_0,esk2_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_69])).
% 0.10/0.31  cnf(c_0_73, negated_conjecture, (v1_pre_topc(k6_tmap_1(esk1_0,k2_struct_0(esk1_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_32]), c_0_17]), c_0_18])]), c_0_22])).
% 0.10/0.31  cnf(c_0_74, negated_conjecture, (l1_pre_topc(k6_tmap_1(esk1_0,k2_struct_0(esk1_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_32]), c_0_17]), c_0_18])]), c_0_22])).
% 0.10/0.31  cnf(c_0_75, negated_conjecture, (k6_tmap_1(esk1_0,k2_struct_0(esk1_0))=k6_tmap_1(esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_70]), c_0_71]), c_0_72]), c_0_73]), c_0_74])])).
% 0.10/0.31  cnf(c_0_76, plain, (v3_pre_topc(X1,X2)|~r2_hidden(X1,u1_pre_topc(X2))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.10/0.31  cnf(c_0_77, plain, (r2_hidden(X2,u1_pre_topc(X1))|v2_struct_0(X1)|u1_pre_topc(X1)!=k5_tmap_1(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.10/0.31  cnf(c_0_78, negated_conjecture, (k5_tmap_1(esk1_0,esk2_0)=u1_pre_topc(esk1_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_70, c_0_75]), c_0_63])).
% 0.10/0.31  cnf(c_0_79, negated_conjecture, (~v3_pre_topc(esk2_0,esk1_0)|g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))!=k6_tmap_1(esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.10/0.31  cnf(c_0_80, negated_conjecture, (v3_pre_topc(esk2_0,esk1_0)|~r2_hidden(esk2_0,u1_pre_topc(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_16]), c_0_18])])).
% 0.10/0.31  cnf(c_0_81, negated_conjecture, (r2_hidden(esk2_0,u1_pre_topc(esk1_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_78]), c_0_17]), c_0_18]), c_0_16])]), c_0_22])).
% 0.10/0.31  cnf(c_0_82, negated_conjecture, (~v3_pre_topc(esk2_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_79, c_0_72])])).
% 0.10/0.31  cnf(c_0_83, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_80, c_0_81])]), c_0_82]), ['proof']).
% 0.10/0.31  # SZS output end CNFRefutation
% 0.10/0.31  # Proof object total steps             : 84
% 0.10/0.31  # Proof object clause steps            : 59
% 0.10/0.31  # Proof object formula steps           : 25
% 0.10/0.31  # Proof object conjectures             : 46
% 0.10/0.31  # Proof object clause conjectures      : 43
% 0.10/0.31  # Proof object formula conjectures     : 3
% 0.10/0.31  # Proof object initial clauses used    : 21
% 0.10/0.31  # Proof object initial formulas used   : 12
% 0.10/0.31  # Proof object generating inferences   : 30
% 0.10/0.31  # Proof object simplifying inferences  : 106
% 0.10/0.31  # Training examples: 0 positive, 0 negative
% 0.10/0.31  # Parsed axioms                        : 16
% 0.10/0.31  # Removed by relevancy pruning/SinE    : 0
% 0.10/0.31  # Initial clauses                      : 29
% 0.10/0.31  # Removed in clause preprocessing      : 1
% 0.10/0.31  # Initial clauses in saturation        : 28
% 0.10/0.31  # Processed clauses                    : 866
% 0.10/0.31  # ...of these trivial                  : 9
% 0.10/0.31  # ...subsumed                          : 384
% 0.10/0.31  # ...remaining for further processing  : 473
% 0.10/0.31  # Other redundant clauses eliminated   : 2
% 0.10/0.31  # Clauses deleted for lack of memory   : 0
% 0.10/0.31  # Backward-subsumed                    : 91
% 0.10/0.31  # Backward-rewritten                   : 52
% 0.10/0.31  # Generated clauses                    : 2327
% 0.10/0.31  # ...of the previous two non-trivial   : 2180
% 0.10/0.31  # Contextual simplify-reflections      : 131
% 0.10/0.31  # Paramodulations                      : 2324
% 0.10/0.31  # Factorizations                       : 0
% 0.10/0.31  # Equation resolutions                 : 2
% 0.10/0.31  # Propositional unsat checks           : 0
% 0.10/0.31  #    Propositional check models        : 0
% 0.10/0.31  #    Propositional check unsatisfiable : 0
% 0.10/0.31  #    Propositional clauses             : 0
% 0.10/0.31  #    Propositional clauses after purity: 0
% 0.10/0.31  #    Propositional unsat core size     : 0
% 0.10/0.31  #    Propositional preprocessing time  : 0.000
% 0.10/0.31  #    Propositional encoding time       : 0.000
% 0.10/0.31  #    Propositional solver time         : 0.000
% 0.10/0.31  #    Success case prop preproc time    : 0.000
% 0.10/0.31  #    Success case prop encoding time   : 0.000
% 0.10/0.31  #    Success case prop solver time     : 0.000
% 0.10/0.31  # Current number of processed clauses  : 300
% 0.10/0.31  #    Positive orientable unit clauses  : 27
% 0.10/0.31  #    Positive unorientable unit clauses: 0
% 0.10/0.31  #    Negative unit clauses             : 3
% 0.10/0.31  #    Non-unit-clauses                  : 270
% 0.10/0.31  # Current number of unprocessed clauses: 1343
% 0.10/0.31  # ...number of literals in the above   : 6091
% 0.10/0.31  # Current number of archived formulas  : 0
% 0.10/0.31  # Current number of archived clauses   : 172
% 0.10/0.31  # Clause-clause subsumption calls (NU) : 34319
% 0.10/0.31  # Rec. Clause-clause subsumption calls : 16273
% 0.10/0.31  # Non-unit clause-clause subsumptions  : 430
% 0.10/0.31  # Unit Clause-clause subsumption calls : 2150
% 0.10/0.31  # Rewrite failures with RHS unbound    : 0
% 0.10/0.31  # BW rewrite match attempts            : 30
% 0.10/0.31  # BW rewrite match successes           : 19
% 0.10/0.31  # Condensation attempts                : 0
% 0.10/0.31  # Condensation successes               : 0
% 0.10/0.31  # Termbank termtop insertions          : 58638
% 0.10/0.32  
% 0.10/0.32  # -------------------------------------------------
% 0.10/0.32  # User time                : 0.058 s
% 0.10/0.32  # System time              : 0.005 s
% 0.10/0.32  # Total time               : 0.063 s
% 0.10/0.32  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
