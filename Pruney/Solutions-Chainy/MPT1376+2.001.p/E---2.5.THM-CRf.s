%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:14:17 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 584 expanded)
%              Number of clauses        :   44 ( 231 expanded)
%              Number of leaves         :    8 ( 152 expanded)
%              Depth                    :   14
%              Number of atoms          :  232 (2903 expanded)
%              Number of equality atoms :   13 ( 195 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d1_tops_2,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
         => ( v1_tops_2(X2,X1)
          <=> ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ( r2_hidden(X3,X2)
                 => v3_pre_topc(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_2)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(t32_compts_1,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( v1_tops_2(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
        <=> ( v1_tops_2(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_compts_1)).

fof(free_g1_pre_topc,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ! [X3,X4] :
          ( g1_pre_topc(X1,X2) = g1_pre_topc(X3,X4)
         => ( X1 = X3
            & X2 = X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_pre_topc)).

fof(abstractness_v1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ( v1_pre_topc(X1)
       => X1 = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

fof(dt_g1_pre_topc,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ( v1_pre_topc(g1_pre_topc(X1,X2))
        & l1_pre_topc(g1_pre_topc(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_g1_pre_topc)).

fof(dt_u1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

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

fof(c_0_8,plain,(
    ! [X18,X19,X20] :
      ( ( ~ v1_tops_2(X19,X18)
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X18)))
        | ~ r2_hidden(X20,X19)
        | v3_pre_topc(X20,X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X18))))
        | ~ l1_pre_topc(X18) )
      & ( m1_subset_1(esk1_2(X18,X19),k1_zfmisc_1(u1_struct_0(X18)))
        | v1_tops_2(X19,X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X18))))
        | ~ l1_pre_topc(X18) )
      & ( r2_hidden(esk1_2(X18,X19),X19)
        | v1_tops_2(X19,X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X18))))
        | ~ l1_pre_topc(X18) )
      & ( ~ v3_pre_topc(esk1_2(X18,X19),X18)
        | v1_tops_2(X19,X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X18))))
        | ~ l1_pre_topc(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tops_2])])])])])).

fof(c_0_9,plain,(
    ! [X5,X6,X7] :
      ( ~ r2_hidden(X5,X6)
      | ~ m1_subset_1(X6,k1_zfmisc_1(X7))
      | m1_subset_1(X5,X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( v1_tops_2(X2,X1)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
          <=> ( v1_tops_2(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) ) ) ) ),
    inference(assume_negation,[status(cth)],[t32_compts_1])).

fof(c_0_11,plain,(
    ! [X12,X13,X14,X15] :
      ( ( X12 = X14
        | g1_pre_topc(X12,X13) != g1_pre_topc(X14,X15)
        | ~ m1_subset_1(X13,k1_zfmisc_1(k1_zfmisc_1(X12))) )
      & ( X13 = X15
        | g1_pre_topc(X12,X13) != g1_pre_topc(X14,X15)
        | ~ m1_subset_1(X13,k1_zfmisc_1(k1_zfmisc_1(X12))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[free_g1_pre_topc])])])])).

fof(c_0_12,plain,(
    ! [X8] :
      ( ~ l1_pre_topc(X8)
      | ~ v1_pre_topc(X8)
      | X8 = g1_pre_topc(u1_struct_0(X8),u1_pre_topc(X8)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[abstractness_v1_pre_topc])])).

fof(c_0_13,plain,(
    ! [X9,X10] :
      ( ( v1_pre_topc(g1_pre_topc(X9,X10))
        | ~ m1_subset_1(X10,k1_zfmisc_1(k1_zfmisc_1(X9))) )
      & ( l1_pre_topc(g1_pre_topc(X9,X10))
        | ~ m1_subset_1(X10,k1_zfmisc_1(k1_zfmisc_1(X9))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_g1_pre_topc])])])).

cnf(c_0_14,plain,
    ( v3_pre_topc(X3,X2)
    | ~ v1_tops_2(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r2_hidden(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_16,negated_conjecture,
    ( ~ v2_struct_0(esk2_0)
    & v2_pre_topc(esk2_0)
    & l1_pre_topc(esk2_0)
    & ( ~ v1_tops_2(esk3_0,esk2_0)
      | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))))
      | ~ v1_tops_2(esk3_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))
      | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))))) )
    & ( v1_tops_2(esk3_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))
      | v1_tops_2(esk3_0,esk2_0) )
    & ( m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))))))
      | v1_tops_2(esk3_0,esk2_0) )
    & ( v1_tops_2(esk3_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))
      | m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0)))) )
    & ( m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))))))
      | m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0)))) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])])).

cnf(c_0_17,plain,
    ( X1 = X2
    | g1_pre_topc(X1,X3) != g1_pre_topc(X2,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( X1 = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ l1_pre_topc(X1)
    | ~ v1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( l1_pre_topc(g1_pre_topc(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( v1_pre_topc(g1_pre_topc(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,plain,
    ( v3_pre_topc(X1,X2)
    | ~ v1_tops_2(X3,X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ r2_hidden(X1,X3) ),
    inference(csr,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_22,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))))))
    | v1_tops_2(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,negated_conjecture,
    ( v1_tops_2(esk3_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))
    | v1_tops_2(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))))))
    | m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,plain,
    ( u1_struct_0(g1_pre_topc(X1,X2)) = X1
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18])]),c_0_19]),c_0_20])).

fof(c_0_26,plain,(
    ! [X11] :
      ( ~ l1_pre_topc(X11)
      | m1_subset_1(u1_pre_topc(X11),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X11)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).

cnf(c_0_27,negated_conjecture,
    ( v1_tops_2(esk3_0,esk2_0)
    | v3_pre_topc(X1,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))
    | ~ r2_hidden(X1,esk3_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))))
    | ~ m1_subset_1(u1_pre_topc(esk2_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0)))) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_29,plain,
    ( m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_30,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_31,negated_conjecture,
    ( v1_tops_2(esk3_0,esk2_0)
    | v3_pre_topc(X1,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))
    | ~ m1_subset_1(u1_pre_topc(esk2_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))))
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_19])).

cnf(c_0_32,plain,
    ( r2_hidden(esk1_2(X1,X2),X2)
    | v1_tops_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_33,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30])])).

fof(c_0_34,plain,(
    ! [X16,X17] :
      ( ( v3_pre_topc(X17,g1_pre_topc(u1_struct_0(X16),u1_pre_topc(X16)))
        | ~ v3_pre_topc(X17,X16)
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))
        | ~ v2_pre_topc(X16)
        | ~ l1_pre_topc(X16) )
      & ( m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X16),u1_pre_topc(X16)))))
        | ~ v3_pre_topc(X17,X16)
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))
        | ~ v2_pre_topc(X16)
        | ~ l1_pre_topc(X16) )
      & ( v3_pre_topc(X17,X16)
        | ~ v3_pre_topc(X17,g1_pre_topc(u1_struct_0(X16),u1_pre_topc(X16)))
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X16),u1_pre_topc(X16)))))
        | ~ v2_pre_topc(X16)
        | ~ l1_pre_topc(X16) )
      & ( m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))
        | ~ v3_pre_topc(X17,g1_pre_topc(u1_struct_0(X16),u1_pre_topc(X16)))
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X16),u1_pre_topc(X16)))))
        | ~ v2_pre_topc(X16)
        | ~ l1_pre_topc(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t60_pre_topc])])])])).

cnf(c_0_35,negated_conjecture,
    ( v1_tops_2(esk3_0,esk2_0)
    | v3_pre_topc(X1,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))
    | ~ r2_hidden(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_29]),c_0_30])])).

cnf(c_0_36,negated_conjecture,
    ( v1_tops_2(esk3_0,esk2_0)
    | r2_hidden(esk1_2(esk2_0,esk3_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_30])])).

cnf(c_0_37,negated_conjecture,
    ( v1_tops_2(esk3_0,esk2_0)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))))
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_15,c_0_22])).

cnf(c_0_38,plain,
    ( v3_pre_topc(X1,X2)
    | ~ v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_39,negated_conjecture,
    ( v1_tops_2(esk3_0,esk2_0)
    | v3_pre_topc(esk1_2(esk2_0,esk3_0),g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_40,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_41,negated_conjecture,
    ( v1_tops_2(esk3_0,esk2_0)
    | m1_subset_1(esk1_2(esk2_0,esk3_0),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))))) ),
    inference(spm,[status(thm)],[c_0_37,c_0_36])).

cnf(c_0_42,plain,
    ( v1_tops_2(X2,X1)
    | ~ v3_pre_topc(esk1_2(X1,X2),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_43,negated_conjecture,
    ( v1_tops_2(esk3_0,esk2_0)
    | v3_pre_topc(esk1_2(esk2_0,esk3_0),esk2_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40]),c_0_30])]),c_0_41])).

cnf(c_0_44,plain,
    ( v1_tops_2(X1,g1_pre_topc(X2,X3))
    | r2_hidden(esk1_2(g1_pre_topc(X2,X3),X1),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_25]),c_0_19])).

cnf(c_0_45,negated_conjecture,
    ( v3_pre_topc(X1,esk2_0)
    | ~ v1_tops_2(esk3_0,esk2_0)
    | ~ r2_hidden(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_33]),c_0_30])])).

cnf(c_0_46,negated_conjecture,
    ( v1_tops_2(esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_30]),c_0_33])])).

cnf(c_0_47,negated_conjecture,
    ( v1_tops_2(esk3_0,g1_pre_topc(u1_struct_0(esk2_0),X1))
    | r2_hidden(esk1_2(g1_pre_topc(u1_struct_0(esk2_0),X1),esk3_0),esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0)))) ),
    inference(spm,[status(thm)],[c_0_44,c_0_33])).

cnf(c_0_48,negated_conjecture,
    ( ~ v1_tops_2(esk3_0,esk2_0)
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))))
    | ~ v1_tops_2(esk3_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_49,plain,
    ( v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ v3_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_50,negated_conjecture,
    ( v3_pre_topc(X1,esk2_0)
    | ~ r2_hidden(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_46])])).

cnf(c_0_51,negated_conjecture,
    ( v1_tops_2(esk3_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))
    | r2_hidden(esk1_2(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)),esk3_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_29]),c_0_30])])).

cnf(c_0_52,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_15,c_0_33])).

cnf(c_0_53,negated_conjecture,
    ( ~ v1_tops_2(esk3_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))
    | ~ v1_tops_2(esk3_0,esk2_0)
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_33])])).

cnf(c_0_54,plain,
    ( v1_tops_2(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ v3_pre_topc(esk1_2(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X1),X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(esk1_2(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X1),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))) ),
    inference(spm,[status(thm)],[c_0_42,c_0_49])).

cnf(c_0_55,negated_conjecture,
    ( v1_tops_2(esk3_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))
    | v3_pre_topc(esk1_2(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)),esk3_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_56,negated_conjecture,
    ( v1_tops_2(esk3_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))
    | m1_subset_1(esk1_2(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)),esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_52,c_0_51])).

cnf(c_0_57,negated_conjecture,
    ( ~ v1_tops_2(esk3_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_53,c_0_46])])).

cnf(c_0_58,negated_conjecture,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_40]),c_0_30])]),c_0_56]),c_0_57])).

cnf(c_0_59,negated_conjecture,
    ( ~ m1_subset_1(u1_pre_topc(esk2_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0)))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_25]),c_0_33])]),c_0_19])).

cnf(c_0_60,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_29]),c_0_30])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:53:35 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.41  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SOS_SP_PS_S5PRR_RG_S04AN
% 0.21/0.41  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.21/0.41  #
% 0.21/0.41  # Preprocessing time       : 0.028 s
% 0.21/0.41  # Presaturation interreduction done
% 0.21/0.41  
% 0.21/0.41  # Proof found!
% 0.21/0.41  # SZS status Theorem
% 0.21/0.41  # SZS output start CNFRefutation
% 0.21/0.41  fof(d1_tops_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>(v1_tops_2(X2,X1)<=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(r2_hidden(X3,X2)=>v3_pre_topc(X3,X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tops_2)).
% 0.21/0.41  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 0.21/0.41  fof(t32_compts_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((v1_tops_2(X2,X1)&m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))))<=>(v1_tops_2(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))&m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_compts_1)).
% 0.21/0.41  fof(free_g1_pre_topc, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>![X3, X4]:(g1_pre_topc(X1,X2)=g1_pre_topc(X3,X4)=>(X1=X3&X2=X4))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', free_g1_pre_topc)).
% 0.21/0.41  fof(abstractness_v1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>(v1_pre_topc(X1)=>X1=g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', abstractness_v1_pre_topc)).
% 0.21/0.41  fof(dt_g1_pre_topc, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>(v1_pre_topc(g1_pre_topc(X1,X2))&l1_pre_topc(g1_pre_topc(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_g1_pre_topc)).
% 0.21/0.41  fof(dt_u1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 0.21/0.41  fof(t60_pre_topc, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:((v3_pre_topc(X2,X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))<=>(v3_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_pre_topc)).
% 0.21/0.41  fof(c_0_8, plain, ![X18, X19, X20]:((~v1_tops_2(X19,X18)|(~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X18)))|(~r2_hidden(X20,X19)|v3_pre_topc(X20,X18)))|~m1_subset_1(X19,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X18))))|~l1_pre_topc(X18))&((m1_subset_1(esk1_2(X18,X19),k1_zfmisc_1(u1_struct_0(X18)))|v1_tops_2(X19,X18)|~m1_subset_1(X19,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X18))))|~l1_pre_topc(X18))&((r2_hidden(esk1_2(X18,X19),X19)|v1_tops_2(X19,X18)|~m1_subset_1(X19,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X18))))|~l1_pre_topc(X18))&(~v3_pre_topc(esk1_2(X18,X19),X18)|v1_tops_2(X19,X18)|~m1_subset_1(X19,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X18))))|~l1_pre_topc(X18))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tops_2])])])])])).
% 0.21/0.41  fof(c_0_9, plain, ![X5, X6, X7]:(~r2_hidden(X5,X6)|~m1_subset_1(X6,k1_zfmisc_1(X7))|m1_subset_1(X5,X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.21/0.41  fof(c_0_10, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((v1_tops_2(X2,X1)&m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))))<=>(v1_tops_2(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))&m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))), inference(assume_negation,[status(cth)],[t32_compts_1])).
% 0.21/0.41  fof(c_0_11, plain, ![X12, X13, X14, X15]:((X12=X14|g1_pre_topc(X12,X13)!=g1_pre_topc(X14,X15)|~m1_subset_1(X13,k1_zfmisc_1(k1_zfmisc_1(X12))))&(X13=X15|g1_pre_topc(X12,X13)!=g1_pre_topc(X14,X15)|~m1_subset_1(X13,k1_zfmisc_1(k1_zfmisc_1(X12))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[free_g1_pre_topc])])])])).
% 0.21/0.41  fof(c_0_12, plain, ![X8]:(~l1_pre_topc(X8)|(~v1_pre_topc(X8)|X8=g1_pre_topc(u1_struct_0(X8),u1_pre_topc(X8)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[abstractness_v1_pre_topc])])).
% 0.21/0.41  fof(c_0_13, plain, ![X9, X10]:((v1_pre_topc(g1_pre_topc(X9,X10))|~m1_subset_1(X10,k1_zfmisc_1(k1_zfmisc_1(X9))))&(l1_pre_topc(g1_pre_topc(X9,X10))|~m1_subset_1(X10,k1_zfmisc_1(k1_zfmisc_1(X9))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_g1_pre_topc])])])).
% 0.21/0.41  cnf(c_0_14, plain, (v3_pre_topc(X3,X2)|~v1_tops_2(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~r2_hidden(X3,X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.21/0.41  cnf(c_0_15, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.21/0.41  fof(c_0_16, negated_conjecture, (((~v2_struct_0(esk2_0)&v2_pre_topc(esk2_0))&l1_pre_topc(esk2_0))&((~v1_tops_2(esk3_0,esk2_0)|~m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))))|(~v1_tops_2(esk3_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))|~m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))))))))&(((v1_tops_2(esk3_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))|v1_tops_2(esk3_0,esk2_0))&(m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))))))|v1_tops_2(esk3_0,esk2_0)))&((v1_tops_2(esk3_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))|m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0)))))&(m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))))))|m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))))))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])])).
% 0.21/0.41  cnf(c_0_17, plain, (X1=X2|g1_pre_topc(X1,X3)!=g1_pre_topc(X2,X4)|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.21/0.41  cnf(c_0_18, plain, (X1=g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))|~l1_pre_topc(X1)|~v1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.41  cnf(c_0_19, plain, (l1_pre_topc(g1_pre_topc(X1,X2))|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.21/0.41  cnf(c_0_20, plain, (v1_pre_topc(g1_pre_topc(X1,X2))|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.21/0.41  cnf(c_0_21, plain, (v3_pre_topc(X1,X2)|~v1_tops_2(X3,X2)|~l1_pre_topc(X2)|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))|~r2_hidden(X1,X3)), inference(csr,[status(thm)],[c_0_14, c_0_15])).
% 0.21/0.41  cnf(c_0_22, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))))))|v1_tops_2(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.41  cnf(c_0_23, negated_conjecture, (v1_tops_2(esk3_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))|v1_tops_2(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.41  cnf(c_0_24, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))))))|m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.41  cnf(c_0_25, plain, (u1_struct_0(g1_pre_topc(X1,X2))=X1|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18])]), c_0_19]), c_0_20])).
% 0.21/0.41  fof(c_0_26, plain, ![X11]:(~l1_pre_topc(X11)|m1_subset_1(u1_pre_topc(X11),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X11))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).
% 0.21/0.41  cnf(c_0_27, negated_conjecture, (v1_tops_2(esk3_0,esk2_0)|v3_pre_topc(X1,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))|~r2_hidden(X1,esk3_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_23])).
% 0.21/0.41  cnf(c_0_28, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))))|~m1_subset_1(u1_pre_topc(esk2_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))))), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.21/0.41  cnf(c_0_29, plain, (m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.21/0.41  cnf(c_0_30, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.41  cnf(c_0_31, negated_conjecture, (v1_tops_2(esk3_0,esk2_0)|v3_pre_topc(X1,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))|~m1_subset_1(u1_pre_topc(esk2_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))))|~r2_hidden(X1,esk3_0)), inference(spm,[status(thm)],[c_0_27, c_0_19])).
% 0.21/0.41  cnf(c_0_32, plain, (r2_hidden(esk1_2(X1,X2),X2)|v1_tops_2(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.21/0.41  cnf(c_0_33, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_30])])).
% 0.21/0.41  fof(c_0_34, plain, ![X16, X17]:(((v3_pre_topc(X17,g1_pre_topc(u1_struct_0(X16),u1_pre_topc(X16)))|(~v3_pre_topc(X17,X16)|~m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16))))|(~v2_pre_topc(X16)|~l1_pre_topc(X16)))&(m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X16),u1_pre_topc(X16)))))|(~v3_pre_topc(X17,X16)|~m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16))))|(~v2_pre_topc(X16)|~l1_pre_topc(X16))))&((v3_pre_topc(X17,X16)|(~v3_pre_topc(X17,g1_pre_topc(u1_struct_0(X16),u1_pre_topc(X16)))|~m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X16),u1_pre_topc(X16))))))|(~v2_pre_topc(X16)|~l1_pre_topc(X16)))&(m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))|(~v3_pre_topc(X17,g1_pre_topc(u1_struct_0(X16),u1_pre_topc(X16)))|~m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X16),u1_pre_topc(X16))))))|(~v2_pre_topc(X16)|~l1_pre_topc(X16))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t60_pre_topc])])])])).
% 0.21/0.41  cnf(c_0_35, negated_conjecture, (v1_tops_2(esk3_0,esk2_0)|v3_pre_topc(X1,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))|~r2_hidden(X1,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_29]), c_0_30])])).
% 0.21/0.41  cnf(c_0_36, negated_conjecture, (v1_tops_2(esk3_0,esk2_0)|r2_hidden(esk1_2(esk2_0,esk3_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_30])])).
% 0.21/0.41  cnf(c_0_37, negated_conjecture, (v1_tops_2(esk3_0,esk2_0)|m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))))|~r2_hidden(X1,esk3_0)), inference(spm,[status(thm)],[c_0_15, c_0_22])).
% 0.21/0.41  cnf(c_0_38, plain, (v3_pre_topc(X1,X2)|~v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.21/0.41  cnf(c_0_39, negated_conjecture, (v1_tops_2(esk3_0,esk2_0)|v3_pre_topc(esk1_2(esk2_0,esk3_0),g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.21/0.41  cnf(c_0_40, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.41  cnf(c_0_41, negated_conjecture, (v1_tops_2(esk3_0,esk2_0)|m1_subset_1(esk1_2(esk2_0,esk3_0),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))))), inference(spm,[status(thm)],[c_0_37, c_0_36])).
% 0.21/0.41  cnf(c_0_42, plain, (v1_tops_2(X2,X1)|~v3_pre_topc(esk1_2(X1,X2),X1)|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.21/0.41  cnf(c_0_43, negated_conjecture, (v1_tops_2(esk3_0,esk2_0)|v3_pre_topc(esk1_2(esk2_0,esk3_0),esk2_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_40]), c_0_30])]), c_0_41])).
% 0.21/0.41  cnf(c_0_44, plain, (v1_tops_2(X1,g1_pre_topc(X2,X3))|r2_hidden(esk1_2(g1_pre_topc(X2,X3),X1),X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_25]), c_0_19])).
% 0.21/0.41  cnf(c_0_45, negated_conjecture, (v3_pre_topc(X1,esk2_0)|~v1_tops_2(esk3_0,esk2_0)|~r2_hidden(X1,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_33]), c_0_30])])).
% 0.21/0.41  cnf(c_0_46, negated_conjecture, (v1_tops_2(esk3_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_30]), c_0_33])])).
% 0.21/0.41  cnf(c_0_47, negated_conjecture, (v1_tops_2(esk3_0,g1_pre_topc(u1_struct_0(esk2_0),X1))|r2_hidden(esk1_2(g1_pre_topc(u1_struct_0(esk2_0),X1),esk3_0),esk3_0)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))))), inference(spm,[status(thm)],[c_0_44, c_0_33])).
% 0.21/0.41  cnf(c_0_48, negated_conjecture, (~v1_tops_2(esk3_0,esk2_0)|~m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))))|~v1_tops_2(esk3_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))|~m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))))))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.41  cnf(c_0_49, plain, (v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))|~v3_pre_topc(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.21/0.41  cnf(c_0_50, negated_conjecture, (v3_pre_topc(X1,esk2_0)|~r2_hidden(X1,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_45, c_0_46])])).
% 0.21/0.41  cnf(c_0_51, negated_conjecture, (v1_tops_2(esk3_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))|r2_hidden(esk1_2(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)),esk3_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_29]), c_0_30])])).
% 0.21/0.41  cnf(c_0_52, negated_conjecture, (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))|~r2_hidden(X1,esk3_0)), inference(spm,[status(thm)],[c_0_15, c_0_33])).
% 0.21/0.41  cnf(c_0_53, negated_conjecture, (~v1_tops_2(esk3_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))|~v1_tops_2(esk3_0,esk2_0)|~m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_48, c_0_33])])).
% 0.21/0.41  cnf(c_0_54, plain, (v1_tops_2(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))|~v3_pre_topc(esk1_2(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X1),X2)|~v2_pre_topc(X2)|~l1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))|~l1_pre_topc(X2)|~m1_subset_1(esk1_2(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X1),k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))), inference(spm,[status(thm)],[c_0_42, c_0_49])).
% 0.21/0.41  cnf(c_0_55, negated_conjecture, (v1_tops_2(esk3_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))|v3_pre_topc(esk1_2(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)),esk3_0),esk2_0)), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.21/0.41  cnf(c_0_56, negated_conjecture, (v1_tops_2(esk3_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))|m1_subset_1(esk1_2(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)),esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(spm,[status(thm)],[c_0_52, c_0_51])).
% 0.21/0.41  cnf(c_0_57, negated_conjecture, (~v1_tops_2(esk3_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))|~m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_53, c_0_46])])).
% 0.21/0.41  cnf(c_0_58, negated_conjecture, (~l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))|~m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))))))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_40]), c_0_30])]), c_0_56]), c_0_57])).
% 0.21/0.41  cnf(c_0_59, negated_conjecture, (~m1_subset_1(u1_pre_topc(esk2_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_25]), c_0_33])]), c_0_19])).
% 0.21/0.41  cnf(c_0_60, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_29]), c_0_30])]), ['proof']).
% 0.21/0.41  # SZS output end CNFRefutation
% 0.21/0.41  # Proof object total steps             : 61
% 0.21/0.41  # Proof object clause steps            : 44
% 0.21/0.41  # Proof object formula steps           : 17
% 0.21/0.41  # Proof object conjectures             : 32
% 0.21/0.41  # Proof object clause conjectures      : 29
% 0.21/0.41  # Proof object formula conjectures     : 3
% 0.21/0.41  # Proof object initial clauses used    : 17
% 0.21/0.41  # Proof object initial formulas used   : 8
% 0.21/0.41  # Proof object generating inferences   : 23
% 0.21/0.41  # Proof object simplifying inferences  : 39
% 0.21/0.41  # Training examples: 0 positive, 0 negative
% 0.21/0.41  # Parsed axioms                        : 8
% 0.21/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.41  # Initial clauses                      : 23
% 0.21/0.41  # Removed in clause preprocessing      : 0
% 0.21/0.41  # Initial clauses in saturation        : 23
% 0.21/0.41  # Processed clauses                    : 295
% 0.21/0.41  # ...of these trivial                  : 2
% 0.21/0.41  # ...subsumed                          : 120
% 0.21/0.41  # ...remaining for further processing  : 173
% 0.21/0.41  # Other redundant clauses eliminated   : 10
% 0.21/0.41  # Clauses deleted for lack of memory   : 0
% 0.21/0.41  # Backward-subsumed                    : 6
% 0.21/0.41  # Backward-rewritten                   : 34
% 0.21/0.41  # Generated clauses                    : 781
% 0.21/0.41  # ...of the previous two non-trivial   : 637
% 0.21/0.41  # Contextual simplify-reflections      : 35
% 0.21/0.41  # Paramodulations                      : 768
% 0.21/0.41  # Factorizations                       : 0
% 0.21/0.41  # Equation resolutions                 : 13
% 0.21/0.41  # Propositional unsat checks           : 0
% 0.21/0.41  #    Propositional check models        : 0
% 0.21/0.41  #    Propositional check unsatisfiable : 0
% 0.21/0.41  #    Propositional clauses             : 0
% 0.21/0.41  #    Propositional clauses after purity: 0
% 0.21/0.41  #    Propositional unsat core size     : 0
% 0.21/0.41  #    Propositional preprocessing time  : 0.000
% 0.21/0.41  #    Propositional encoding time       : 0.000
% 0.21/0.41  #    Propositional solver time         : 0.000
% 0.21/0.41  #    Success case prop preproc time    : 0.000
% 0.21/0.41  #    Success case prop encoding time   : 0.000
% 0.21/0.41  #    Success case prop solver time     : 0.000
% 0.21/0.41  # Current number of processed clauses  : 110
% 0.21/0.41  #    Positive orientable unit clauses  : 6
% 0.21/0.41  #    Positive unorientable unit clauses: 0
% 0.21/0.41  #    Negative unit clauses             : 3
% 0.21/0.41  #    Non-unit-clauses                  : 101
% 0.21/0.41  # Current number of unprocessed clauses: 383
% 0.21/0.41  # ...number of literals in the above   : 2220
% 0.21/0.41  # Current number of archived formulas  : 0
% 0.21/0.41  # Current number of archived clauses   : 63
% 0.21/0.41  # Clause-clause subsumption calls (NU) : 3178
% 0.21/0.41  # Rec. Clause-clause subsumption calls : 1146
% 0.21/0.41  # Non-unit clause-clause subsumptions  : 147
% 0.21/0.41  # Unit Clause-clause subsumption calls : 13
% 0.21/0.41  # Rewrite failures with RHS unbound    : 0
% 0.21/0.41  # BW rewrite match attempts            : 5
% 0.21/0.41  # BW rewrite match successes           : 4
% 0.21/0.41  # Condensation attempts                : 0
% 0.21/0.41  # Condensation successes               : 0
% 0.21/0.41  # Termbank termtop insertions          : 25965
% 0.21/0.41  
% 0.21/0.41  # -------------------------------------------------
% 0.21/0.41  # User time                : 0.056 s
% 0.21/0.41  # System time              : 0.005 s
% 0.21/0.41  # Total time               : 0.061 s
% 0.21/0.41  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
