%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:18:16 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 384 expanded)
%              Number of clauses        :   38 ( 145 expanded)
%              Number of leaves         :   11 (  92 expanded)
%              Depth                    :   13
%              Number of atoms          :  232 (1750 expanded)
%              Number of equality atoms :   20 ( 240 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   20 (   2 average)
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

fof(t2_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_pre_topc(X1,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

fof(t65_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( l1_pre_topc(X2)
         => ( m1_pre_topc(X1,X2)
          <=> m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_pre_topc)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(t11_tmap_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ( v1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
            & m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_tmap_1)).

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

fof(t39_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
             => m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_pre_topc)).

fof(t60_pre_topc,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( v3_pre_topc(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
        <=> ( v3_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_pre_topc)).

fof(d5_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_pre_topc(X2,X1)
          <=> r2_hidden(X2,u1_pre_topc(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_pre_topc)).

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

fof(d9_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k6_tmap_1(X1,X2) = g1_pre_topc(u1_struct_0(X1),k5_tmap_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_tmap_1)).

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
    ! [X24] :
      ( ~ l1_pre_topc(X24)
      | m1_pre_topc(X24,X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tsep_1])])).

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
    ! [X13,X14] :
      ( ( ~ m1_pre_topc(X13,X14)
        | m1_pre_topc(X13,g1_pre_topc(u1_struct_0(X14),u1_pre_topc(X14)))
        | ~ l1_pre_topc(X14)
        | ~ l1_pre_topc(X13) )
      & ( ~ m1_pre_topc(X13,g1_pre_topc(u1_struct_0(X14),u1_pre_topc(X14)))
        | m1_pre_topc(X13,X14)
        | ~ l1_pre_topc(X14)
        | ~ l1_pre_topc(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_pre_topc])])])])).

fof(c_0_15,plain,(
    ! [X6,X7] :
      ( ~ l1_pre_topc(X6)
      | ~ m1_pre_topc(X7,X6)
      | l1_pre_topc(X7) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

fof(c_0_16,plain,(
    ! [X22,X23] :
      ( ( v1_pre_topc(g1_pre_topc(u1_struct_0(X23),u1_pre_topc(X23)))
        | ~ m1_pre_topc(X23,X22)
        | ~ l1_pre_topc(X22) )
      & ( m1_pre_topc(g1_pre_topc(u1_struct_0(X23),u1_pre_topc(X23)),X22)
        | ~ m1_pre_topc(X23,X22)
        | ~ l1_pre_topc(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_tmap_1])])])])).

cnf(c_0_17,plain,
    ( m1_pre_topc(X1,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( m1_pre_topc(esk1_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

fof(c_0_23,plain,(
    ! [X19,X20,X21] :
      ( v2_struct_0(X19)
      | ~ v2_pre_topc(X19)
      | ~ l1_pre_topc(X19)
      | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))
      | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X19,X20))))
      | X21 != X20
      | v3_pre_topc(X21,k6_tmap_1(X19,X20)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t105_tmap_1])])])])).

fof(c_0_24,plain,(
    ! [X8,X9,X10] :
      ( ~ l1_pre_topc(X8)
      | ~ m1_pre_topc(X9,X8)
      | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9)))
      | m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X8))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t39_pre_topc])])])).

cnf(c_0_25,plain,
    ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_26,negated_conjecture,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_18])])).

cnf(c_0_27,plain,
    ( v2_struct_0(X1)
    | v3_pre_topc(X3,k6_tmap_1(X1,X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X1,X2))))
    | X3 != X2 ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_28,plain,
    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_29,negated_conjecture,
    ( m1_pre_topc(esk1_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_22]),c_0_18])])).

cnf(c_0_30,negated_conjecture,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_26]),c_0_18])])).

cnf(c_0_31,plain,
    ( v2_struct_0(X1)
    | v3_pre_topc(X2,k6_tmap_1(X1,X2))
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X1,X2))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(er,[status(thm)],[c_0_27])).

cnf(c_0_32,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_33,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_34,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_35,plain,(
    ! [X11,X12] :
      ( ( v3_pre_topc(X12,g1_pre_topc(u1_struct_0(X11),u1_pre_topc(X11)))
        | ~ v3_pre_topc(X12,X11)
        | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X11)))
        | ~ v2_pre_topc(X11)
        | ~ l1_pre_topc(X11) )
      & ( m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X11),u1_pre_topc(X11)))))
        | ~ v3_pre_topc(X12,X11)
        | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X11)))
        | ~ v2_pre_topc(X11)
        | ~ l1_pre_topc(X11) )
      & ( v3_pre_topc(X12,X11)
        | ~ v3_pre_topc(X12,g1_pre_topc(u1_struct_0(X11),u1_pre_topc(X11)))
        | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X11),u1_pre_topc(X11)))))
        | ~ v2_pre_topc(X11)
        | ~ l1_pre_topc(X11) )
      & ( m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X11)))
        | ~ v3_pre_topc(X12,g1_pre_topc(u1_struct_0(X11),u1_pre_topc(X11)))
        | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X11),u1_pre_topc(X11)))))
        | ~ v2_pre_topc(X11)
        | ~ l1_pre_topc(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t60_pre_topc])])])])).

cnf(c_0_36,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30])])).

cnf(c_0_37,negated_conjecture,
    ( v3_pre_topc(esk2_0,k6_tmap_1(esk1_0,esk2_0))
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k6_tmap_1(esk1_0,esk2_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33]),c_0_18])]),c_0_34])).

cnf(c_0_38,negated_conjecture,
    ( v3_pre_topc(esk2_0,esk1_0)
    | g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)) = k6_tmap_1(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_39,plain,
    ( v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ v3_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

fof(c_0_40,plain,(
    ! [X4,X5] :
      ( ( ~ v3_pre_topc(X5,X4)
        | r2_hidden(X5,u1_pre_topc(X4))
        | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X4)))
        | ~ l1_pre_topc(X4) )
      & ( ~ r2_hidden(X5,u1_pre_topc(X4))
        | v3_pre_topc(X5,X4)
        | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X4)))
        | ~ l1_pre_topc(X4) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_pre_topc])])])])).

cnf(c_0_41,plain,
    ( v3_pre_topc(X1,X2)
    | ~ v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_42,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))))) ),
    inference(spm,[status(thm)],[c_0_36,c_0_32])).

cnf(c_0_43,negated_conjecture,
    ( v3_pre_topc(esk2_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))
    | v3_pre_topc(esk2_0,esk1_0)
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))))) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_44,negated_conjecture,
    ( v3_pre_topc(esk2_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))
    | ~ v3_pre_topc(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_32]),c_0_33]),c_0_18])])).

fof(c_0_45,plain,(
    ! [X17,X18] :
      ( ( ~ r2_hidden(X18,u1_pre_topc(X17))
        | u1_pre_topc(X17) = k5_tmap_1(X17,X18)
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))
        | v2_struct_0(X17)
        | ~ v2_pre_topc(X17)
        | ~ l1_pre_topc(X17) )
      & ( u1_pre_topc(X17) != k5_tmap_1(X17,X18)
        | r2_hidden(X18,u1_pre_topc(X17))
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))
        | v2_struct_0(X17)
        | ~ v2_pre_topc(X17)
        | ~ l1_pre_topc(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t103_tmap_1])])])])])).

cnf(c_0_46,plain,
    ( r2_hidden(X1,u1_pre_topc(X2))
    | ~ v3_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_47,negated_conjecture,
    ( v3_pre_topc(esk2_0,esk1_0)
    | ~ v3_pre_topc(esk2_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_33]),c_0_18])])).

cnf(c_0_48,negated_conjecture,
    ( v3_pre_topc(esk2_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_42])]),c_0_44])).

fof(c_0_49,plain,(
    ! [X15,X16] :
      ( v2_struct_0(X15)
      | ~ v2_pre_topc(X15)
      | ~ l1_pre_topc(X15)
      | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
      | k6_tmap_1(X15,X16) = g1_pre_topc(u1_struct_0(X15),k5_tmap_1(X15,X16)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d9_tmap_1])])])])).

cnf(c_0_50,plain,
    ( u1_pre_topc(X2) = k5_tmap_1(X2,X1)
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,u1_pre_topc(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_51,negated_conjecture,
    ( r2_hidden(esk2_0,u1_pre_topc(esk1_0))
    | ~ v3_pre_topc(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_32]),c_0_18])])).

cnf(c_0_52,negated_conjecture,
    ( v3_pre_topc(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_48])])).

cnf(c_0_53,plain,
    ( v2_struct_0(X1)
    | k6_tmap_1(X1,X2) = g1_pre_topc(u1_struct_0(X1),k5_tmap_1(X1,X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_54,negated_conjecture,
    ( k5_tmap_1(esk1_0,esk2_0) = u1_pre_topc(esk1_0)
    | ~ r2_hidden(esk2_0,u1_pre_topc(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_32]),c_0_33]),c_0_18])]),c_0_34])).

cnf(c_0_55,negated_conjecture,
    ( r2_hidden(esk2_0,u1_pre_topc(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_52])])).

cnf(c_0_56,negated_conjecture,
    ( ~ v3_pre_topc(esk2_0,esk1_0)
    | g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)) != k6_tmap_1(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_57,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk1_0),k5_tmap_1(esk1_0,esk2_0)) = k6_tmap_1(esk1_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_32]),c_0_33]),c_0_18])]),c_0_34])).

cnf(c_0_58,negated_conjecture,
    ( k5_tmap_1(esk1_0,esk2_0) = u1_pre_topc(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_54,c_0_55])])).

cnf(c_0_59,negated_conjecture,
    ( k6_tmap_1(esk1_0,esk2_0) != g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_52])])).

cnf(c_0_60,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_57,c_0_58]),c_0_59]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:35:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S2i
% 0.19/0.37  # and selection function SelectGrCQArEqFirst.
% 0.19/0.37  #
% 0.19/0.37  # Preprocessing time       : 0.028 s
% 0.19/0.37  # Presaturation interreduction done
% 0.19/0.37  
% 0.19/0.37  # Proof found!
% 0.19/0.37  # SZS status Theorem
% 0.19/0.37  # SZS output start CNFRefutation
% 0.19/0.37  fof(t106_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))=k6_tmap_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_tmap_1)).
% 0.19/0.37  fof(t2_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>m1_pre_topc(X1,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tsep_1)).
% 0.19/0.37  fof(t65_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(l1_pre_topc(X2)=>(m1_pre_topc(X1,X2)<=>m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_pre_topc)).
% 0.19/0.37  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.19/0.37  fof(t11_tmap_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>(v1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))&m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_tmap_1)).
% 0.19/0.37  fof(t105_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X1,X2))))=>(X3=X2=>v3_pre_topc(X3,k6_tmap_1(X1,X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t105_tmap_1)).
% 0.19/0.37  fof(t39_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))=>m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_pre_topc)).
% 0.19/0.37  fof(t60_pre_topc, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:((v3_pre_topc(X2,X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))<=>(v3_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_pre_topc)).
% 0.19/0.37  fof(d5_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>r2_hidden(X2,u1_pre_topc(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_pre_topc)).
% 0.19/0.37  fof(t103_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(r2_hidden(X2,u1_pre_topc(X1))<=>u1_pre_topc(X1)=k5_tmap_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t103_tmap_1)).
% 0.19/0.37  fof(d9_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k6_tmap_1(X1,X2)=g1_pre_topc(u1_struct_0(X1),k5_tmap_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_tmap_1)).
% 0.19/0.37  fof(c_0_11, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))=k6_tmap_1(X1,X2))))), inference(assume_negation,[status(cth)],[t106_tmap_1])).
% 0.19/0.37  fof(c_0_12, plain, ![X24]:(~l1_pre_topc(X24)|m1_pre_topc(X24,X24)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tsep_1])])).
% 0.19/0.37  fof(c_0_13, negated_conjecture, (((~v2_struct_0(esk1_0)&v2_pre_topc(esk1_0))&l1_pre_topc(esk1_0))&(m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&((~v3_pre_topc(esk2_0,esk1_0)|g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))!=k6_tmap_1(esk1_0,esk2_0))&(v3_pre_topc(esk2_0,esk1_0)|g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))=k6_tmap_1(esk1_0,esk2_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_11])])])])).
% 0.19/0.37  fof(c_0_14, plain, ![X13, X14]:((~m1_pre_topc(X13,X14)|m1_pre_topc(X13,g1_pre_topc(u1_struct_0(X14),u1_pre_topc(X14)))|~l1_pre_topc(X14)|~l1_pre_topc(X13))&(~m1_pre_topc(X13,g1_pre_topc(u1_struct_0(X14),u1_pre_topc(X14)))|m1_pre_topc(X13,X14)|~l1_pre_topc(X14)|~l1_pre_topc(X13))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_pre_topc])])])])).
% 0.19/0.37  fof(c_0_15, plain, ![X6, X7]:(~l1_pre_topc(X6)|(~m1_pre_topc(X7,X6)|l1_pre_topc(X7))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.19/0.37  fof(c_0_16, plain, ![X22, X23]:((v1_pre_topc(g1_pre_topc(u1_struct_0(X23),u1_pre_topc(X23)))|~m1_pre_topc(X23,X22)|~l1_pre_topc(X22))&(m1_pre_topc(g1_pre_topc(u1_struct_0(X23),u1_pre_topc(X23)),X22)|~m1_pre_topc(X23,X22)|~l1_pre_topc(X22))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_tmap_1])])])])).
% 0.19/0.37  cnf(c_0_17, plain, (m1_pre_topc(X1,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.37  cnf(c_0_18, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.37  cnf(c_0_19, plain, (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.37  cnf(c_0_20, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.37  cnf(c_0_21, plain, (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.37  cnf(c_0_22, negated_conjecture, (m1_pre_topc(esk1_0,esk1_0)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.19/0.37  fof(c_0_23, plain, ![X19, X20, X21]:(v2_struct_0(X19)|~v2_pre_topc(X19)|~l1_pre_topc(X19)|(~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))|(~m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X19,X20))))|(X21!=X20|v3_pre_topc(X21,k6_tmap_1(X19,X20)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t105_tmap_1])])])])).
% 0.19/0.37  fof(c_0_24, plain, ![X8, X9, X10]:(~l1_pre_topc(X8)|(~m1_pre_topc(X9,X8)|(~m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9)))|m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X8)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t39_pre_topc])])])).
% 0.19/0.37  cnf(c_0_25, plain, (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(csr,[status(thm)],[c_0_19, c_0_20])).
% 0.19/0.37  cnf(c_0_26, negated_conjecture, (m1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_18])])).
% 0.19/0.37  cnf(c_0_27, plain, (v2_struct_0(X1)|v3_pre_topc(X3,k6_tmap_1(X1,X2))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X1,X2))))|X3!=X2), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.37  cnf(c_0_28, plain, (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.37  cnf(c_0_29, negated_conjecture, (m1_pre_topc(esk1_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_22]), c_0_18])])).
% 0.19/0.37  cnf(c_0_30, negated_conjecture, (l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_26]), c_0_18])])).
% 0.19/0.37  cnf(c_0_31, plain, (v2_struct_0(X1)|v3_pre_topc(X2,k6_tmap_1(X1,X2))|~v2_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X1,X2))))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(er,[status(thm)],[c_0_27])).
% 0.19/0.37  cnf(c_0_32, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.37  cnf(c_0_33, negated_conjecture, (v2_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.37  cnf(c_0_34, negated_conjecture, (~v2_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.37  fof(c_0_35, plain, ![X11, X12]:(((v3_pre_topc(X12,g1_pre_topc(u1_struct_0(X11),u1_pre_topc(X11)))|(~v3_pre_topc(X12,X11)|~m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X11))))|(~v2_pre_topc(X11)|~l1_pre_topc(X11)))&(m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X11),u1_pre_topc(X11)))))|(~v3_pre_topc(X12,X11)|~m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X11))))|(~v2_pre_topc(X11)|~l1_pre_topc(X11))))&((v3_pre_topc(X12,X11)|(~v3_pre_topc(X12,g1_pre_topc(u1_struct_0(X11),u1_pre_topc(X11)))|~m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X11),u1_pre_topc(X11))))))|(~v2_pre_topc(X11)|~l1_pre_topc(X11)))&(m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X11)))|(~v3_pre_topc(X12,g1_pre_topc(u1_struct_0(X11),u1_pre_topc(X11)))|~m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X11),u1_pre_topc(X11))))))|(~v2_pre_topc(X11)|~l1_pre_topc(X11))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t60_pre_topc])])])])).
% 0.19/0.37  cnf(c_0_36, negated_conjecture, (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_30])])).
% 0.19/0.37  cnf(c_0_37, negated_conjecture, (v3_pre_topc(esk2_0,k6_tmap_1(esk1_0,esk2_0))|~m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k6_tmap_1(esk1_0,esk2_0))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_33]), c_0_18])]), c_0_34])).
% 0.19/0.37  cnf(c_0_38, negated_conjecture, (v3_pre_topc(esk2_0,esk1_0)|g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))=k6_tmap_1(esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.37  cnf(c_0_39, plain, (v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))|~v3_pre_topc(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.19/0.37  fof(c_0_40, plain, ![X4, X5]:((~v3_pre_topc(X5,X4)|r2_hidden(X5,u1_pre_topc(X4))|~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X4)))|~l1_pre_topc(X4))&(~r2_hidden(X5,u1_pre_topc(X4))|v3_pre_topc(X5,X4)|~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X4)))|~l1_pre_topc(X4))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_pre_topc])])])])).
% 0.19/0.37  cnf(c_0_41, plain, (v3_pre_topc(X1,X2)|~v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.19/0.37  cnf(c_0_42, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))))), inference(spm,[status(thm)],[c_0_36, c_0_32])).
% 0.19/0.37  cnf(c_0_43, negated_conjecture, (v3_pre_topc(esk2_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))|v3_pre_topc(esk2_0,esk1_0)|~m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))))), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.19/0.37  cnf(c_0_44, negated_conjecture, (v3_pre_topc(esk2_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))|~v3_pre_topc(esk2_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_32]), c_0_33]), c_0_18])])).
% 0.19/0.37  fof(c_0_45, plain, ![X17, X18]:((~r2_hidden(X18,u1_pre_topc(X17))|u1_pre_topc(X17)=k5_tmap_1(X17,X18)|~m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))|(v2_struct_0(X17)|~v2_pre_topc(X17)|~l1_pre_topc(X17)))&(u1_pre_topc(X17)!=k5_tmap_1(X17,X18)|r2_hidden(X18,u1_pre_topc(X17))|~m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))|(v2_struct_0(X17)|~v2_pre_topc(X17)|~l1_pre_topc(X17)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t103_tmap_1])])])])])).
% 0.19/0.37  cnf(c_0_46, plain, (r2_hidden(X1,u1_pre_topc(X2))|~v3_pre_topc(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.19/0.37  cnf(c_0_47, negated_conjecture, (v3_pre_topc(esk2_0,esk1_0)|~v3_pre_topc(esk2_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_33]), c_0_18])])).
% 0.19/0.37  cnf(c_0_48, negated_conjecture, (v3_pre_topc(esk2_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_43, c_0_42])]), c_0_44])).
% 0.19/0.37  fof(c_0_49, plain, ![X15, X16]:(v2_struct_0(X15)|~v2_pre_topc(X15)|~l1_pre_topc(X15)|(~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))|k6_tmap_1(X15,X16)=g1_pre_topc(u1_struct_0(X15),k5_tmap_1(X15,X16)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d9_tmap_1])])])])).
% 0.19/0.37  cnf(c_0_50, plain, (u1_pre_topc(X2)=k5_tmap_1(X2,X1)|v2_struct_0(X2)|~r2_hidden(X1,u1_pre_topc(X2))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.19/0.37  cnf(c_0_51, negated_conjecture, (r2_hidden(esk2_0,u1_pre_topc(esk1_0))|~v3_pre_topc(esk2_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_32]), c_0_18])])).
% 0.19/0.37  cnf(c_0_52, negated_conjecture, (v3_pre_topc(esk2_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_47, c_0_48])])).
% 0.19/0.37  cnf(c_0_53, plain, (v2_struct_0(X1)|k6_tmap_1(X1,X2)=g1_pre_topc(u1_struct_0(X1),k5_tmap_1(X1,X2))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.19/0.37  cnf(c_0_54, negated_conjecture, (k5_tmap_1(esk1_0,esk2_0)=u1_pre_topc(esk1_0)|~r2_hidden(esk2_0,u1_pre_topc(esk1_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_32]), c_0_33]), c_0_18])]), c_0_34])).
% 0.19/0.37  cnf(c_0_55, negated_conjecture, (r2_hidden(esk2_0,u1_pre_topc(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_51, c_0_52])])).
% 0.19/0.37  cnf(c_0_56, negated_conjecture, (~v3_pre_topc(esk2_0,esk1_0)|g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))!=k6_tmap_1(esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.37  cnf(c_0_57, negated_conjecture, (g1_pre_topc(u1_struct_0(esk1_0),k5_tmap_1(esk1_0,esk2_0))=k6_tmap_1(esk1_0,esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_32]), c_0_33]), c_0_18])]), c_0_34])).
% 0.19/0.37  cnf(c_0_58, negated_conjecture, (k5_tmap_1(esk1_0,esk2_0)=u1_pre_topc(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_54, c_0_55])])).
% 0.19/0.37  cnf(c_0_59, negated_conjecture, (k6_tmap_1(esk1_0,esk2_0)!=g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_56, c_0_52])])).
% 0.19/0.37  cnf(c_0_60, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_57, c_0_58]), c_0_59]), ['proof']).
% 0.19/0.37  # SZS output end CNFRefutation
% 0.19/0.37  # Proof object total steps             : 61
% 0.19/0.37  # Proof object clause steps            : 38
% 0.19/0.37  # Proof object formula steps           : 23
% 0.19/0.37  # Proof object conjectures             : 28
% 0.19/0.37  # Proof object clause conjectures      : 25
% 0.19/0.37  # Proof object formula conjectures     : 3
% 0.19/0.37  # Proof object initial clauses used    : 17
% 0.19/0.37  # Proof object initial formulas used   : 11
% 0.19/0.37  # Proof object generating inferences   : 13
% 0.19/0.37  # Proof object simplifying inferences  : 43
% 0.19/0.37  # Training examples: 0 positive, 0 negative
% 0.19/0.37  # Parsed axioms                        : 11
% 0.19/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.37  # Initial clauses                      : 23
% 0.19/0.37  # Removed in clause preprocessing      : 0
% 0.19/0.37  # Initial clauses in saturation        : 23
% 0.19/0.37  # Processed clauses                    : 75
% 0.19/0.37  # ...of these trivial                  : 1
% 0.19/0.37  # ...subsumed                          : 0
% 0.19/0.37  # ...remaining for further processing  : 74
% 0.19/0.37  # Other redundant clauses eliminated   : 1
% 0.19/0.37  # Clauses deleted for lack of memory   : 0
% 0.19/0.37  # Backward-subsumed                    : 0
% 0.19/0.37  # Backward-rewritten                   : 10
% 0.19/0.37  # Generated clauses                    : 52
% 0.19/0.37  # ...of the previous two non-trivial   : 43
% 0.19/0.37  # Contextual simplify-reflections      : 2
% 0.19/0.37  # Paramodulations                      : 51
% 0.19/0.37  # Factorizations                       : 0
% 0.19/0.37  # Equation resolutions                 : 1
% 0.19/0.37  # Propositional unsat checks           : 0
% 0.19/0.37  #    Propositional check models        : 0
% 0.19/0.37  #    Propositional check unsatisfiable : 0
% 0.19/0.37  #    Propositional clauses             : 0
% 0.19/0.37  #    Propositional clauses after purity: 0
% 0.19/0.37  #    Propositional unsat core size     : 0
% 0.19/0.37  #    Propositional preprocessing time  : 0.000
% 0.19/0.37  #    Propositional encoding time       : 0.000
% 0.19/0.37  #    Propositional solver time         : 0.000
% 0.19/0.37  #    Success case prop preproc time    : 0.000
% 0.19/0.37  #    Success case prop encoding time   : 0.000
% 0.19/0.37  #    Success case prop solver time     : 0.000
% 0.19/0.37  # Current number of processed clauses  : 40
% 0.19/0.37  #    Positive orientable unit clauses  : 17
% 0.19/0.37  #    Positive unorientable unit clauses: 0
% 0.19/0.37  #    Negative unit clauses             : 2
% 0.19/0.37  #    Non-unit-clauses                  : 21
% 0.19/0.37  # Current number of unprocessed clauses: 14
% 0.19/0.37  # ...number of literals in the above   : 28
% 0.19/0.37  # Current number of archived formulas  : 0
% 0.19/0.37  # Current number of archived clauses   : 33
% 0.19/0.37  # Clause-clause subsumption calls (NU) : 413
% 0.19/0.37  # Rec. Clause-clause subsumption calls : 81
% 0.19/0.37  # Non-unit clause-clause subsumptions  : 2
% 0.19/0.37  # Unit Clause-clause subsumption calls : 10
% 0.19/0.37  # Rewrite failures with RHS unbound    : 0
% 0.19/0.37  # BW rewrite match attempts            : 12
% 0.19/0.37  # BW rewrite match successes           : 5
% 0.19/0.37  # Condensation attempts                : 0
% 0.19/0.37  # Condensation successes               : 0
% 0.19/0.37  # Termbank termtop insertions          : 3976
% 0.19/0.37  
% 0.19/0.37  # -------------------------------------------------
% 0.19/0.37  # User time                : 0.032 s
% 0.19/0.37  # System time              : 0.004 s
% 0.19/0.37  # Total time               : 0.036 s
% 0.19/0.37  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
