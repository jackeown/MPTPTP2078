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
% DateTime   : Thu Dec  3 11:13:00 EST 2020

% Result     : Theorem 22.96s
% Output     : CNFRefutation 22.96s
% Verified   : 
% Statistics : Number of formulae       :  106 (9053 expanded)
%              Number of clauses        :   87 (3630 expanded)
%              Number of leaves         :    9 (2276 expanded)
%              Depth                    :   32
%              Number of atoms          :  416 (37820 expanded)
%              Number of equality atoms :    8 ( 707 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   26 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t16_tops_2,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
         => ( v2_tops_2(X2,X1)
          <=> v1_tops_2(k7_setfam_1(u1_struct_0(X1),X2),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_tops_2)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(dt_k7_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => m1_subset_1(k7_setfam_1(X1,X2),k1_zfmisc_1(k1_zfmisc_1(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_setfam_1)).

fof(d8_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
         => ( X3 = k7_setfam_1(X1,X2)
          <=> ! [X4] :
                ( m1_subset_1(X4,k1_zfmisc_1(X1))
               => ( r2_hidden(X4,X3)
                <=> r2_hidden(k3_subset_1(X1,X4),X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_setfam_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_2)).

fof(t49_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => ( r2_hidden(k3_subset_1(X1,X3),k7_setfam_1(X1,X2))
          <=> r2_hidden(X3,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_setfam_1)).

fof(d2_tops_2,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
         => ( v2_tops_2(X2,X1)
          <=> ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ( r2_hidden(X3,X2)
                 => v4_pre_topc(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tops_2)).

fof(t29_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v4_pre_topc(X2,X1)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X1),X2),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tops_1)).

fof(t30_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_pre_topc(X2,X1)
          <=> v4_pre_topc(k3_subset_1(u1_struct_0(X1),X2),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_tops_1)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
           => ( v2_tops_2(X2,X1)
            <=> v1_tops_2(k7_setfam_1(u1_struct_0(X1),X2),X1) ) ) ) ),
    inference(assume_negation,[status(cth)],[t16_tops_2])).

fof(c_0_10,plain,(
    ! [X15,X16,X17] :
      ( ~ r2_hidden(X15,X16)
      | ~ m1_subset_1(X16,k1_zfmisc_1(X17))
      | m1_subset_1(X15,X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_11,plain,(
    ! [X10,X11] :
      ( ~ m1_subset_1(X11,k1_zfmisc_1(k1_zfmisc_1(X10)))
      | m1_subset_1(k7_setfam_1(X10,X11),k1_zfmisc_1(k1_zfmisc_1(X10))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_setfam_1])])).

fof(c_0_12,negated_conjecture,
    ( l1_pre_topc(esk4_0)
    & m1_subset_1(esk5_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0))))
    & ( ~ v2_tops_2(esk5_0,esk4_0)
      | ~ v1_tops_2(k7_setfam_1(u1_struct_0(esk4_0),esk5_0),esk4_0) )
    & ( v2_tops_2(esk5_0,esk4_0)
      | v1_tops_2(k7_setfam_1(u1_struct_0(esk4_0),esk5_0),esk4_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).

fof(c_0_13,plain,(
    ! [X5,X6,X7,X8] :
      ( ( ~ r2_hidden(X8,X7)
        | r2_hidden(k3_subset_1(X5,X8),X6)
        | ~ m1_subset_1(X8,k1_zfmisc_1(X5))
        | X7 != k7_setfam_1(X5,X6)
        | ~ m1_subset_1(X7,k1_zfmisc_1(k1_zfmisc_1(X5)))
        | ~ m1_subset_1(X6,k1_zfmisc_1(k1_zfmisc_1(X5))) )
      & ( ~ r2_hidden(k3_subset_1(X5,X8),X6)
        | r2_hidden(X8,X7)
        | ~ m1_subset_1(X8,k1_zfmisc_1(X5))
        | X7 != k7_setfam_1(X5,X6)
        | ~ m1_subset_1(X7,k1_zfmisc_1(k1_zfmisc_1(X5)))
        | ~ m1_subset_1(X6,k1_zfmisc_1(k1_zfmisc_1(X5))) )
      & ( m1_subset_1(esk1_3(X5,X6,X7),k1_zfmisc_1(X5))
        | X7 = k7_setfam_1(X5,X6)
        | ~ m1_subset_1(X7,k1_zfmisc_1(k1_zfmisc_1(X5)))
        | ~ m1_subset_1(X6,k1_zfmisc_1(k1_zfmisc_1(X5))) )
      & ( ~ r2_hidden(esk1_3(X5,X6,X7),X7)
        | ~ r2_hidden(k3_subset_1(X5,esk1_3(X5,X6,X7)),X6)
        | X7 = k7_setfam_1(X5,X6)
        | ~ m1_subset_1(X7,k1_zfmisc_1(k1_zfmisc_1(X5)))
        | ~ m1_subset_1(X6,k1_zfmisc_1(k1_zfmisc_1(X5))) )
      & ( r2_hidden(esk1_3(X5,X6,X7),X7)
        | r2_hidden(k3_subset_1(X5,esk1_3(X5,X6,X7)),X6)
        | X7 = k7_setfam_1(X5,X6)
        | ~ m1_subset_1(X7,k1_zfmisc_1(k1_zfmisc_1(X5)))
        | ~ m1_subset_1(X6,k1_zfmisc_1(k1_zfmisc_1(X5))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_setfam_1])])])])])).

fof(c_0_14,plain,(
    ! [X22,X23,X24] :
      ( ( ~ v1_tops_2(X23,X22)
        | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X22)))
        | ~ r2_hidden(X24,X23)
        | v3_pre_topc(X24,X22)
        | ~ m1_subset_1(X23,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X22))))
        | ~ l1_pre_topc(X22) )
      & ( m1_subset_1(esk2_2(X22,X23),k1_zfmisc_1(u1_struct_0(X22)))
        | v1_tops_2(X23,X22)
        | ~ m1_subset_1(X23,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X22))))
        | ~ l1_pre_topc(X22) )
      & ( r2_hidden(esk2_2(X22,X23),X23)
        | v1_tops_2(X23,X22)
        | ~ m1_subset_1(X23,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X22))))
        | ~ l1_pre_topc(X22) )
      & ( ~ v3_pre_topc(esk2_2(X22,X23),X22)
        | v1_tops_2(X23,X22)
        | ~ m1_subset_1(X23,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X22))))
        | ~ l1_pre_topc(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tops_2])])])])])).

cnf(c_0_15,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( m1_subset_1(k7_setfam_1(X2,X1),k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( r2_hidden(k3_subset_1(X3,X1),X4)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3))
    | X2 != k7_setfam_1(X3,X4)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( ~ v2_tops_2(esk5_0,esk4_0)
    | ~ v1_tops_2(k7_setfam_1(u1_struct_0(esk4_0),esk5_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,plain,
    ( r2_hidden(esk2_2(X1,X2),X2)
    | v1_tops_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_22,plain,(
    ! [X12,X13,X14] :
      ( ( ~ r2_hidden(k3_subset_1(X12,X14),k7_setfam_1(X12,X13))
        | r2_hidden(X14,X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(X12))
        | ~ m1_subset_1(X13,k1_zfmisc_1(k1_zfmisc_1(X12))) )
      & ( ~ r2_hidden(X14,X13)
        | r2_hidden(k3_subset_1(X12,X14),k7_setfam_1(X12,X13))
        | ~ m1_subset_1(X14,k1_zfmisc_1(X12))
        | ~ m1_subset_1(X13,k1_zfmisc_1(k1_zfmisc_1(X12))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t49_setfam_1])])])])).

cnf(c_0_23,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X1,k7_setfam_1(X2,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_24,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_15,c_0_17])).

cnf(c_0_25,plain,
    ( r2_hidden(k3_subset_1(X1,X2),X3)
    | ~ r2_hidden(X2,k7_setfam_1(X1,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_18,c_0_15])]),c_0_16])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(esk2_2(esk4_0,k7_setfam_1(u1_struct_0(esk4_0),esk5_0)),k7_setfam_1(u1_struct_0(esk4_0),esk5_0))
    | ~ v2_tops_2(esk5_0,esk4_0)
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0(esk4_0),esk5_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21])])).

fof(c_0_27,plain,(
    ! [X26,X27,X28] :
      ( ( ~ v2_tops_2(X27,X26)
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X26)))
        | ~ r2_hidden(X28,X27)
        | v4_pre_topc(X28,X26)
        | ~ m1_subset_1(X27,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X26))))
        | ~ l1_pre_topc(X26) )
      & ( m1_subset_1(esk3_2(X26,X27),k1_zfmisc_1(u1_struct_0(X26)))
        | v2_tops_2(X27,X26)
        | ~ m1_subset_1(X27,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X26))))
        | ~ l1_pre_topc(X26) )
      & ( r2_hidden(esk3_2(X26,X27),X27)
        | v2_tops_2(X27,X26)
        | ~ m1_subset_1(X27,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X26))))
        | ~ l1_pre_topc(X26) )
      & ( ~ v4_pre_topc(esk3_2(X26,X27),X26)
        | v2_tops_2(X27,X26)
        | ~ m1_subset_1(X27,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X26))))
        | ~ l1_pre_topc(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tops_2])])])])])).

cnf(c_0_28,plain,
    ( r2_hidden(X2,X3)
    | ~ r2_hidden(k3_subset_1(X1,X2),k7_setfam_1(X1,X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X1,k7_setfam_1(X2,k7_setfam_1(X2,X3)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(spm,[status(thm)],[c_0_23,c_0_16])).

cnf(c_0_30,plain,
    ( r2_hidden(k3_subset_1(X3,X1),k7_setfam_1(X3,X2))
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_31,plain,
    ( r2_hidden(X2,X4)
    | ~ r2_hidden(k3_subset_1(X1,X2),X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | X4 != k7_setfam_1(X1,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_32,negated_conjecture,
    ( m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ r2_hidden(X2,k7_setfam_1(X1,esk5_0))
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(esk2_2(esk4_0,k7_setfam_1(u1_struct_0(esk4_0),esk5_0)),k7_setfam_1(u1_struct_0(esk4_0),esk5_0))
    | ~ v2_tops_2(esk5_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_16]),c_0_17])])).

cnf(c_0_34,plain,
    ( m1_subset_1(esk3_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_tops_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_35,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k7_setfam_1(X3,k7_setfam_1(X3,X2)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X3))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_25]),c_0_29]),c_0_16])).

cnf(c_0_36,plain,
    ( r2_hidden(k3_subset_1(X1,X2),k7_setfam_1(X1,X3))
    | ~ r2_hidden(X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(csr,[status(thm)],[c_0_30,c_0_15])).

cnf(c_0_37,plain,
    ( r2_hidden(X1,k7_setfam_1(X2,X3))
    | ~ r2_hidden(k3_subset_1(X2,X1),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_31]),c_0_16])).

fof(c_0_38,plain,(
    ! [X18,X19] :
      ( ( ~ v4_pre_topc(X19,X18)
        | v3_pre_topc(k3_subset_1(u1_struct_0(X18),X19),X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))
        | ~ l1_pre_topc(X18) )
      & ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X18),X19),X18)
        | v4_pre_topc(X19,X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))
        | ~ l1_pre_topc(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_tops_1])])])])).

cnf(c_0_39,negated_conjecture,
    ( m1_subset_1(k3_subset_1(u1_struct_0(esk4_0),X1),k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ r2_hidden(X1,k7_setfam_1(u1_struct_0(esk4_0),esk5_0)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_17])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(esk2_2(esk4_0,k7_setfam_1(u1_struct_0(esk4_0),esk5_0)),k7_setfam_1(u1_struct_0(esk4_0),esk5_0))
    | m1_subset_1(esk3_2(esk4_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_21]),c_0_17])])).

cnf(c_0_41,plain,
    ( r2_hidden(esk3_2(X1,X2),X2)
    | v2_tops_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_42,plain,
    ( r2_hidden(k3_subset_1(X1,X2),X3)
    | ~ r2_hidden(X2,k7_setfam_1(X1,k7_setfam_1(X4,k7_setfam_1(X4,X3))))
    | ~ m1_subset_1(k7_setfam_1(X4,k7_setfam_1(X4,X3)),k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X4))) ),
    inference(spm,[status(thm)],[c_0_35,c_0_25])).

cnf(c_0_43,plain,
    ( m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,k7_setfam_1(X1,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_36]),c_0_16])).

cnf(c_0_44,plain,
    ( r2_hidden(X1,k7_setfam_1(X2,k7_setfam_1(X2,X3)))
    | ~ r2_hidden(k3_subset_1(X2,X1),k7_setfam_1(X2,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_16])).

fof(c_0_45,plain,(
    ! [X20,X21] :
      ( ( ~ v3_pre_topc(X21,X20)
        | v4_pre_topc(k3_subset_1(u1_struct_0(X20),X21),X20)
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))
        | ~ l1_pre_topc(X20) )
      & ( ~ v4_pre_topc(k3_subset_1(u1_struct_0(X20),X21),X20)
        | v3_pre_topc(X21,X20)
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))
        | ~ l1_pre_topc(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t30_tops_1])])])])).

cnf(c_0_46,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(X2),X1),X2)
    | ~ v4_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_47,negated_conjecture,
    ( m1_subset_1(k3_subset_1(u1_struct_0(esk4_0),esk2_2(esk4_0,k7_setfam_1(u1_struct_0(esk4_0),esk5_0))),k1_zfmisc_1(u1_struct_0(esk4_0)))
    | m1_subset_1(esk3_2(esk4_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_48,plain,
    ( v4_pre_topc(X3,X2)
    | ~ v2_tops_2(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r2_hidden(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_49,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ r2_hidden(X1,k7_setfam_1(u1_struct_0(esk4_0),esk5_0)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_17])).

cnf(c_0_50,negated_conjecture,
    ( r2_hidden(esk2_2(esk4_0,k7_setfam_1(u1_struct_0(esk4_0),esk5_0)),k7_setfam_1(u1_struct_0(esk4_0),esk5_0))
    | r2_hidden(esk3_2(esk4_0,esk5_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_41]),c_0_21]),c_0_17])])).

cnf(c_0_51,plain,
    ( r2_hidden(k3_subset_1(X1,X2),X3)
    | ~ r2_hidden(X2,k7_setfam_1(X1,k7_setfam_1(X1,k7_setfam_1(X1,X3))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_16]),c_0_16])).

cnf(c_0_52,plain,
    ( m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,k7_setfam_1(X1,k7_setfam_1(X1,X3)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(spm,[status(thm)],[c_0_43,c_0_16])).

cnf(c_0_53,plain,
    ( r2_hidden(X1,k7_setfam_1(X2,k7_setfam_1(X2,X3)))
    | ~ r2_hidden(X1,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_36]),c_0_15])).

cnf(c_0_54,plain,
    ( v3_pre_topc(X2,X1)
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0(X1),X2),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_55,plain,
    ( v4_pre_topc(X2,X1)
    | ~ v3_pre_topc(k3_subset_1(u1_struct_0(X1),X2),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_56,negated_conjecture,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(esk4_0),k3_subset_1(u1_struct_0(esk4_0),esk2_2(esk4_0,k7_setfam_1(u1_struct_0(esk4_0),esk5_0)))),esk4_0)
    | m1_subset_1(esk3_2(esk4_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0(esk4_0),esk2_2(esk4_0,k7_setfam_1(u1_struct_0(esk4_0),esk5_0))),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_21])])).

cnf(c_0_57,plain,
    ( v4_pre_topc(X1,X2)
    | ~ v2_tops_2(X3,X2)
    | ~ l1_pre_topc(X2)
    | ~ r2_hidden(X1,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) ),
    inference(csr,[status(thm)],[c_0_48,c_0_15])).

cnf(c_0_58,negated_conjecture,
    ( r2_hidden(esk3_2(esk4_0,esk5_0),esk5_0)
    | m1_subset_1(esk2_2(esk4_0,k7_setfam_1(u1_struct_0(esk4_0),esk5_0)),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_59,negated_conjecture,
    ( r2_hidden(X1,k7_setfam_1(u1_struct_0(esk4_0),esk5_0))
    | ~ r2_hidden(k3_subset_1(u1_struct_0(esk4_0),X1),esk5_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_37,c_0_17])).

cnf(c_0_60,plain,
    ( r2_hidden(k3_subset_1(X1,k3_subset_1(X1,X2)),X3)
    | ~ r2_hidden(X2,k7_setfam_1(X1,k7_setfam_1(X1,X3)))
    | ~ m1_subset_1(k7_setfam_1(X1,k7_setfam_1(X1,X3)),k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(spm,[status(thm)],[c_0_51,c_0_36])).

cnf(c_0_61,plain,
    ( m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_62,plain,
    ( v1_tops_2(X2,X1)
    | ~ v3_pre_topc(esk2_2(X1,X2),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_63,plain,
    ( v3_pre_topc(X1,X2)
    | ~ v3_pre_topc(k3_subset_1(u1_struct_0(X2),k3_subset_1(u1_struct_0(X2),X1)),X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(X2),X1),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_64,negated_conjecture,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(esk4_0),k3_subset_1(u1_struct_0(esk4_0),esk2_2(esk4_0,k7_setfam_1(u1_struct_0(esk4_0),esk5_0)))),esk4_0)
    | m1_subset_1(esk3_2(esk4_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ v2_tops_2(X1,esk4_0)
    | ~ r2_hidden(k3_subset_1(u1_struct_0(esk4_0),esk2_2(esk4_0,k7_setfam_1(u1_struct_0(esk4_0),esk5_0))),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_21])])).

cnf(c_0_65,negated_conjecture,
    ( m1_subset_1(esk2_2(esk4_0,k7_setfam_1(u1_struct_0(esk4_0),esk5_0)),k1_zfmisc_1(u1_struct_0(esk4_0)))
    | m1_subset_1(esk3_2(esk4_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_24,c_0_58])).

cnf(c_0_66,negated_conjecture,
    ( r2_hidden(k3_subset_1(u1_struct_0(esk4_0),X1),k7_setfam_1(u1_struct_0(esk4_0),esk5_0))
    | ~ r2_hidden(X1,k7_setfam_1(u1_struct_0(esk4_0),k7_setfam_1(u1_struct_0(esk4_0),esk5_0)))
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0(esk4_0),k7_setfam_1(u1_struct_0(esk4_0),esk5_0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0)))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_17])]),c_0_61])).

cnf(c_0_67,plain,
    ( v1_tops_2(k7_setfam_1(u1_struct_0(X1),X2),X1)
    | ~ v3_pre_topc(esk2_2(X1,k7_setfam_1(u1_struct_0(X1),X2)),X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ),
    inference(spm,[status(thm)],[c_0_62,c_0_16])).

cnf(c_0_68,negated_conjecture,
    ( v3_pre_topc(esk2_2(esk4_0,k7_setfam_1(u1_struct_0(esk4_0),esk5_0)),esk4_0)
    | m1_subset_1(esk3_2(esk4_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ v2_tops_2(X1,esk4_0)
    | ~ r2_hidden(k3_subset_1(u1_struct_0(esk4_0),esk2_2(esk4_0,k7_setfam_1(u1_struct_0(esk4_0),esk5_0))),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0)))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_21])]),c_0_65]),c_0_15])).

cnf(c_0_69,negated_conjecture,
    ( r2_hidden(X1,esk5_0)
    | ~ r2_hidden(X1,k7_setfam_1(u1_struct_0(esk4_0),k7_setfam_1(u1_struct_0(esk4_0),esk5_0)))
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0(esk4_0),k7_setfam_1(u1_struct_0(esk4_0),esk5_0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0)))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_66]),c_0_17])]),c_0_15])).

cnf(c_0_70,negated_conjecture,
    ( v1_tops_2(k7_setfam_1(u1_struct_0(esk4_0),esk5_0),esk4_0)
    | m1_subset_1(esk3_2(esk4_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ v2_tops_2(X1,esk4_0)
    | ~ r2_hidden(k3_subset_1(u1_struct_0(esk4_0),esk2_2(esk4_0,k7_setfam_1(u1_struct_0(esk4_0),esk5_0))),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_21]),c_0_17])])).

cnf(c_0_71,negated_conjecture,
    ( r2_hidden(X1,esk5_0)
    | ~ r2_hidden(X1,k7_setfam_1(u1_struct_0(esk4_0),k7_setfam_1(u1_struct_0(esk4_0),esk5_0)))
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0(esk4_0),esk5_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0)))) ),
    inference(spm,[status(thm)],[c_0_69,c_0_16])).

cnf(c_0_72,negated_conjecture,
    ( m1_subset_1(esk3_2(esk4_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ v2_tops_2(esk5_0,esk4_0)
    | ~ v2_tops_2(X1,esk4_0)
    | ~ r2_hidden(k3_subset_1(u1_struct_0(esk4_0),esk2_2(esk4_0,k7_setfam_1(u1_struct_0(esk4_0),esk5_0))),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0)))) ),
    inference(spm,[status(thm)],[c_0_19,c_0_70])).

cnf(c_0_73,negated_conjecture,
    ( r2_hidden(X1,esk5_0)
    | ~ r2_hidden(X1,k7_setfam_1(u1_struct_0(esk4_0),k7_setfam_1(u1_struct_0(esk4_0),esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_16]),c_0_17])])).

cnf(c_0_74,plain,
    ( v2_tops_2(X2,X1)
    | ~ v4_pre_topc(esk3_2(X1,X2),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_75,negated_conjecture,
    ( m1_subset_1(esk3_2(esk4_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ v2_tops_2(X1,esk4_0)
    | ~ r2_hidden(k3_subset_1(u1_struct_0(esk4_0),esk2_2(esk4_0,k7_setfam_1(u1_struct_0(esk4_0),esk5_0))),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_34]),c_0_21]),c_0_17])])).

cnf(c_0_76,negated_conjecture,
    ( r2_hidden(k3_subset_1(u1_struct_0(esk4_0),X1),esk5_0)
    | ~ r2_hidden(X1,k7_setfam_1(u1_struct_0(esk4_0),esk5_0))
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0(esk4_0),esk5_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0)))) ),
    inference(spm,[status(thm)],[c_0_73,c_0_36])).

cnf(c_0_77,negated_conjecture,
    ( v2_tops_2(esk5_0,esk4_0)
    | ~ v4_pre_topc(esk3_2(esk4_0,esk5_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_17]),c_0_21])])).

cnf(c_0_78,plain,
    ( v3_pre_topc(X3,X2)
    | ~ v1_tops_2(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r2_hidden(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_79,negated_conjecture,
    ( m1_subset_1(esk3_2(esk4_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ v2_tops_2(esk5_0,esk4_0)
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0(esk4_0),esk5_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0)))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_17])]),c_0_40])).

cnf(c_0_80,negated_conjecture,
    ( v2_tops_2(esk5_0,esk4_0)
    | ~ v3_pre_topc(k3_subset_1(u1_struct_0(esk4_0),esk3_2(esk4_0,esk5_0)),esk4_0)
    | ~ m1_subset_1(esk3_2(esk4_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_55]),c_0_21])])).

cnf(c_0_81,plain,
    ( v3_pre_topc(X1,X2)
    | ~ v1_tops_2(X3,X2)
    | ~ l1_pre_topc(X2)
    | ~ r2_hidden(X1,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) ),
    inference(csr,[status(thm)],[c_0_78,c_0_15])).

cnf(c_0_82,negated_conjecture,
    ( m1_subset_1(esk3_2(esk4_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ v2_tops_2(esk5_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_16]),c_0_17])])).

cnf(c_0_83,negated_conjecture,
    ( v2_tops_2(esk5_0,esk4_0)
    | ~ v1_tops_2(X1,esk4_0)
    | ~ r2_hidden(k3_subset_1(u1_struct_0(esk4_0),esk3_2(esk4_0,esk5_0)),X1)
    | ~ m1_subset_1(esk3_2(esk4_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_81]),c_0_21])])).

cnf(c_0_84,negated_conjecture,
    ( m1_subset_1(esk3_2(esk4_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_34]),c_0_21]),c_0_17])])).

cnf(c_0_85,negated_conjecture,
    ( v2_tops_2(esk5_0,esk4_0)
    | ~ v1_tops_2(X1,esk4_0)
    | ~ r2_hidden(k3_subset_1(u1_struct_0(esk4_0),esk3_2(esk4_0,esk5_0)),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_83,c_0_84])])).

cnf(c_0_86,negated_conjecture,
    ( v2_tops_2(esk5_0,esk4_0)
    | ~ v1_tops_2(k7_setfam_1(u1_struct_0(esk4_0),X1),esk4_0)
    | ~ r2_hidden(esk3_2(esk4_0,esk5_0),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_36]),c_0_16])).

cnf(c_0_87,negated_conjecture,
    ( v2_tops_2(esk5_0,esk4_0)
    | v1_tops_2(k7_setfam_1(u1_struct_0(esk4_0),esk5_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_88,negated_conjecture,
    ( v2_tops_2(esk5_0,esk4_0)
    | ~ r2_hidden(esk3_2(esk4_0,esk5_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_87]),c_0_17])])).

cnf(c_0_89,negated_conjecture,
    ( r2_hidden(esk2_2(esk4_0,k7_setfam_1(u1_struct_0(esk4_0),esk5_0)),k7_setfam_1(u1_struct_0(esk4_0),esk5_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_88]),c_0_50])).

cnf(c_0_90,plain,
    ( m1_subset_1(esk2_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | v1_tops_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_91,negated_conjecture,
    ( m1_subset_1(k3_subset_1(u1_struct_0(esk4_0),esk2_2(esk4_0,k7_setfam_1(u1_struct_0(esk4_0),esk5_0))),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_39,c_0_89])).

cnf(c_0_92,negated_conjecture,
    ( m1_subset_1(esk2_2(esk4_0,k7_setfam_1(u1_struct_0(esk4_0),esk5_0)),k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ v2_tops_2(esk5_0,esk4_0)
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0(esk4_0),esk5_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_90]),c_0_21])])).

cnf(c_0_93,negated_conjecture,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(esk4_0),k3_subset_1(u1_struct_0(esk4_0),esk2_2(esk4_0,k7_setfam_1(u1_struct_0(esk4_0),esk5_0)))),esk4_0)
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0(esk4_0),esk2_2(esk4_0,k7_setfam_1(u1_struct_0(esk4_0),esk5_0))),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_91]),c_0_21])])).

cnf(c_0_94,negated_conjecture,
    ( m1_subset_1(esk2_2(esk4_0,k7_setfam_1(u1_struct_0(esk4_0),esk5_0)),k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ v2_tops_2(esk5_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_16]),c_0_17])])).

cnf(c_0_95,negated_conjecture,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(esk4_0),k3_subset_1(u1_struct_0(esk4_0),esk2_2(esk4_0,k7_setfam_1(u1_struct_0(esk4_0),esk5_0)))),esk4_0)
    | ~ v2_tops_2(X1,esk4_0)
    | ~ r2_hidden(k3_subset_1(u1_struct_0(esk4_0),esk2_2(esk4_0,k7_setfam_1(u1_struct_0(esk4_0),esk5_0))),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_57]),c_0_21])])).

cnf(c_0_96,negated_conjecture,
    ( m1_subset_1(esk2_2(esk4_0,k7_setfam_1(u1_struct_0(esk4_0),esk5_0)),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_88]),c_0_58])).

cnf(c_0_97,negated_conjecture,
    ( v3_pre_topc(esk2_2(esk4_0,k7_setfam_1(u1_struct_0(esk4_0),esk5_0)),esk4_0)
    | ~ v2_tops_2(X1,esk4_0)
    | ~ r2_hidden(k3_subset_1(u1_struct_0(esk4_0),esk2_2(esk4_0,k7_setfam_1(u1_struct_0(esk4_0),esk5_0))),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_95]),c_0_21]),c_0_91]),c_0_96])])).

cnf(c_0_98,negated_conjecture,
    ( v1_tops_2(k7_setfam_1(u1_struct_0(esk4_0),esk5_0),esk4_0)
    | ~ v2_tops_2(X1,esk4_0)
    | ~ r2_hidden(k3_subset_1(u1_struct_0(esk4_0),esk2_2(esk4_0,k7_setfam_1(u1_struct_0(esk4_0),esk5_0))),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_97]),c_0_21]),c_0_17])])).

cnf(c_0_99,negated_conjecture,
    ( ~ v2_tops_2(esk5_0,esk4_0)
    | ~ v2_tops_2(X1,esk4_0)
    | ~ r2_hidden(k3_subset_1(u1_struct_0(esk4_0),esk2_2(esk4_0,k7_setfam_1(u1_struct_0(esk4_0),esk5_0))),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0)))) ),
    inference(spm,[status(thm)],[c_0_19,c_0_98])).

cnf(c_0_100,negated_conjecture,
    ( ~ v2_tops_2(X1,esk4_0)
    | ~ r2_hidden(k3_subset_1(u1_struct_0(esk4_0),esk2_2(esk4_0,k7_setfam_1(u1_struct_0(esk4_0),esk5_0))),X1)
    | ~ r2_hidden(esk3_2(esk4_0,esk5_0),esk5_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0)))) ),
    inference(spm,[status(thm)],[c_0_99,c_0_88])).

cnf(c_0_101,negated_conjecture,
    ( ~ v2_tops_2(X1,esk4_0)
    | ~ r2_hidden(k3_subset_1(u1_struct_0(esk4_0),esk2_2(esk4_0,k7_setfam_1(u1_struct_0(esk4_0),esk5_0))),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0)))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_41]),c_0_21]),c_0_17])]),c_0_100])).

cnf(c_0_102,negated_conjecture,
    ( ~ v2_tops_2(esk5_0,esk4_0)
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0(esk4_0),esk5_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_76]),c_0_17]),c_0_89])])).

cnf(c_0_103,negated_conjecture,
    ( ~ v2_tops_2(esk5_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_16]),c_0_17])])).

cnf(c_0_104,negated_conjecture,
    ( ~ r2_hidden(esk3_2(esk4_0,esk5_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_103,c_0_88])).

cnf(c_0_105,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_41]),c_0_21]),c_0_17])]),c_0_104]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:42:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 22.96/23.17  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S039A
% 22.96/23.17  # and selection function PSelectUnlessUniqMaxPos.
% 22.96/23.17  #
% 22.96/23.17  # Preprocessing time       : 0.028 s
% 22.96/23.17  # Presaturation interreduction done
% 22.96/23.17  
% 22.96/23.17  # Proof found!
% 22.96/23.17  # SZS status Theorem
% 22.96/23.17  # SZS output start CNFRefutation
% 22.96/23.17  fof(t16_tops_2, conjecture, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>(v2_tops_2(X2,X1)<=>v1_tops_2(k7_setfam_1(u1_struct_0(X1),X2),X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_tops_2)).
% 22.96/23.17  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 22.96/23.17  fof(dt_k7_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>m1_subset_1(k7_setfam_1(X1,X2),k1_zfmisc_1(k1_zfmisc_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_setfam_1)).
% 22.96/23.17  fof(d8_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))=>(X3=k7_setfam_1(X1,X2)<=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(X1))=>(r2_hidden(X4,X3)<=>r2_hidden(k3_subset_1(X1,X4),X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_setfam_1)).
% 22.96/23.17  fof(d1_tops_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>(v1_tops_2(X2,X1)<=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(r2_hidden(X3,X2)=>v3_pre_topc(X3,X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tops_2)).
% 22.96/23.17  fof(t49_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(r2_hidden(k3_subset_1(X1,X3),k7_setfam_1(X1,X2))<=>r2_hidden(X3,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_setfam_1)).
% 22.96/23.17  fof(d2_tops_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>(v2_tops_2(X2,X1)<=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(r2_hidden(X3,X2)=>v4_pre_topc(X3,X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tops_2)).
% 22.96/23.17  fof(t29_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v4_pre_topc(X2,X1)<=>v3_pre_topc(k3_subset_1(u1_struct_0(X1),X2),X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_tops_1)).
% 22.96/23.17  fof(t30_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>v4_pre_topc(k3_subset_1(u1_struct_0(X1),X2),X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_tops_1)).
% 22.96/23.17  fof(c_0_9, negated_conjecture, ~(![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>(v2_tops_2(X2,X1)<=>v1_tops_2(k7_setfam_1(u1_struct_0(X1),X2),X1))))), inference(assume_negation,[status(cth)],[t16_tops_2])).
% 22.96/23.17  fof(c_0_10, plain, ![X15, X16, X17]:(~r2_hidden(X15,X16)|~m1_subset_1(X16,k1_zfmisc_1(X17))|m1_subset_1(X15,X17)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 22.96/23.17  fof(c_0_11, plain, ![X10, X11]:(~m1_subset_1(X11,k1_zfmisc_1(k1_zfmisc_1(X10)))|m1_subset_1(k7_setfam_1(X10,X11),k1_zfmisc_1(k1_zfmisc_1(X10)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_setfam_1])])).
% 22.96/23.17  fof(c_0_12, negated_conjecture, (l1_pre_topc(esk4_0)&(m1_subset_1(esk5_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0))))&((~v2_tops_2(esk5_0,esk4_0)|~v1_tops_2(k7_setfam_1(u1_struct_0(esk4_0),esk5_0),esk4_0))&(v2_tops_2(esk5_0,esk4_0)|v1_tops_2(k7_setfam_1(u1_struct_0(esk4_0),esk5_0),esk4_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).
% 22.96/23.17  fof(c_0_13, plain, ![X5, X6, X7, X8]:(((~r2_hidden(X8,X7)|r2_hidden(k3_subset_1(X5,X8),X6)|~m1_subset_1(X8,k1_zfmisc_1(X5))|X7!=k7_setfam_1(X5,X6)|~m1_subset_1(X7,k1_zfmisc_1(k1_zfmisc_1(X5)))|~m1_subset_1(X6,k1_zfmisc_1(k1_zfmisc_1(X5))))&(~r2_hidden(k3_subset_1(X5,X8),X6)|r2_hidden(X8,X7)|~m1_subset_1(X8,k1_zfmisc_1(X5))|X7!=k7_setfam_1(X5,X6)|~m1_subset_1(X7,k1_zfmisc_1(k1_zfmisc_1(X5)))|~m1_subset_1(X6,k1_zfmisc_1(k1_zfmisc_1(X5)))))&((m1_subset_1(esk1_3(X5,X6,X7),k1_zfmisc_1(X5))|X7=k7_setfam_1(X5,X6)|~m1_subset_1(X7,k1_zfmisc_1(k1_zfmisc_1(X5)))|~m1_subset_1(X6,k1_zfmisc_1(k1_zfmisc_1(X5))))&((~r2_hidden(esk1_3(X5,X6,X7),X7)|~r2_hidden(k3_subset_1(X5,esk1_3(X5,X6,X7)),X6)|X7=k7_setfam_1(X5,X6)|~m1_subset_1(X7,k1_zfmisc_1(k1_zfmisc_1(X5)))|~m1_subset_1(X6,k1_zfmisc_1(k1_zfmisc_1(X5))))&(r2_hidden(esk1_3(X5,X6,X7),X7)|r2_hidden(k3_subset_1(X5,esk1_3(X5,X6,X7)),X6)|X7=k7_setfam_1(X5,X6)|~m1_subset_1(X7,k1_zfmisc_1(k1_zfmisc_1(X5)))|~m1_subset_1(X6,k1_zfmisc_1(k1_zfmisc_1(X5))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_setfam_1])])])])])).
% 22.96/23.17  fof(c_0_14, plain, ![X22, X23, X24]:((~v1_tops_2(X23,X22)|(~m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X22)))|(~r2_hidden(X24,X23)|v3_pre_topc(X24,X22)))|~m1_subset_1(X23,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X22))))|~l1_pre_topc(X22))&((m1_subset_1(esk2_2(X22,X23),k1_zfmisc_1(u1_struct_0(X22)))|v1_tops_2(X23,X22)|~m1_subset_1(X23,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X22))))|~l1_pre_topc(X22))&((r2_hidden(esk2_2(X22,X23),X23)|v1_tops_2(X23,X22)|~m1_subset_1(X23,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X22))))|~l1_pre_topc(X22))&(~v3_pre_topc(esk2_2(X22,X23),X22)|v1_tops_2(X23,X22)|~m1_subset_1(X23,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X22))))|~l1_pre_topc(X22))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tops_2])])])])])).
% 22.96/23.17  cnf(c_0_15, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 22.96/23.17  cnf(c_0_16, plain, (m1_subset_1(k7_setfam_1(X2,X1),k1_zfmisc_1(k1_zfmisc_1(X2)))|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 22.96/23.17  cnf(c_0_17, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0))))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 22.96/23.17  cnf(c_0_18, plain, (r2_hidden(k3_subset_1(X3,X1),X4)|~r2_hidden(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X3))|X2!=k7_setfam_1(X3,X4)|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X3)))|~m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X3)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 22.96/23.17  cnf(c_0_19, negated_conjecture, (~v2_tops_2(esk5_0,esk4_0)|~v1_tops_2(k7_setfam_1(u1_struct_0(esk4_0),esk5_0),esk4_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 22.96/23.17  cnf(c_0_20, plain, (r2_hidden(esk2_2(X1,X2),X2)|v1_tops_2(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 22.96/23.17  cnf(c_0_21, negated_conjecture, (l1_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 22.96/23.17  fof(c_0_22, plain, ![X12, X13, X14]:((~r2_hidden(k3_subset_1(X12,X14),k7_setfam_1(X12,X13))|r2_hidden(X14,X13)|~m1_subset_1(X14,k1_zfmisc_1(X12))|~m1_subset_1(X13,k1_zfmisc_1(k1_zfmisc_1(X12))))&(~r2_hidden(X14,X13)|r2_hidden(k3_subset_1(X12,X14),k7_setfam_1(X12,X13))|~m1_subset_1(X14,k1_zfmisc_1(X12))|~m1_subset_1(X13,k1_zfmisc_1(k1_zfmisc_1(X12))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t49_setfam_1])])])])).
% 22.96/23.17  cnf(c_0_23, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X1,k7_setfam_1(X2,X3))|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 22.96/23.17  cnf(c_0_24, negated_conjecture, (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))|~r2_hidden(X1,esk5_0)), inference(spm,[status(thm)],[c_0_15, c_0_17])).
% 22.96/23.17  cnf(c_0_25, plain, (r2_hidden(k3_subset_1(X1,X2),X3)|~r2_hidden(X2,k7_setfam_1(X1,X3))|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_18, c_0_15])]), c_0_16])).
% 22.96/23.17  cnf(c_0_26, negated_conjecture, (r2_hidden(esk2_2(esk4_0,k7_setfam_1(u1_struct_0(esk4_0),esk5_0)),k7_setfam_1(u1_struct_0(esk4_0),esk5_0))|~v2_tops_2(esk5_0,esk4_0)|~m1_subset_1(k7_setfam_1(u1_struct_0(esk4_0),esk5_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_21])])).
% 22.96/23.17  fof(c_0_27, plain, ![X26, X27, X28]:((~v2_tops_2(X27,X26)|(~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X26)))|(~r2_hidden(X28,X27)|v4_pre_topc(X28,X26)))|~m1_subset_1(X27,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X26))))|~l1_pre_topc(X26))&((m1_subset_1(esk3_2(X26,X27),k1_zfmisc_1(u1_struct_0(X26)))|v2_tops_2(X27,X26)|~m1_subset_1(X27,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X26))))|~l1_pre_topc(X26))&((r2_hidden(esk3_2(X26,X27),X27)|v2_tops_2(X27,X26)|~m1_subset_1(X27,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X26))))|~l1_pre_topc(X26))&(~v4_pre_topc(esk3_2(X26,X27),X26)|v2_tops_2(X27,X26)|~m1_subset_1(X27,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X26))))|~l1_pre_topc(X26))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tops_2])])])])])).
% 22.96/23.17  cnf(c_0_28, plain, (r2_hidden(X2,X3)|~r2_hidden(k3_subset_1(X1,X2),k7_setfam_1(X1,X3))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 22.96/23.17  cnf(c_0_29, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X1,k7_setfam_1(X2,k7_setfam_1(X2,X3)))|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(spm,[status(thm)],[c_0_23, c_0_16])).
% 22.96/23.17  cnf(c_0_30, plain, (r2_hidden(k3_subset_1(X3,X1),k7_setfam_1(X3,X2))|~r2_hidden(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X3))|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X3)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 22.96/23.17  cnf(c_0_31, plain, (r2_hidden(X2,X4)|~r2_hidden(k3_subset_1(X1,X2),X3)|~m1_subset_1(X2,k1_zfmisc_1(X1))|X4!=k7_setfam_1(X1,X3)|~m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X1)))|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 22.96/23.17  cnf(c_0_32, negated_conjecture, (m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(u1_struct_0(esk4_0)))|~r2_hidden(X2,k7_setfam_1(X1,esk5_0))|~m1_subset_1(esk5_0,k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 22.96/23.17  cnf(c_0_33, negated_conjecture, (r2_hidden(esk2_2(esk4_0,k7_setfam_1(u1_struct_0(esk4_0),esk5_0)),k7_setfam_1(u1_struct_0(esk4_0),esk5_0))|~v2_tops_2(esk5_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_16]), c_0_17])])).
% 22.96/23.17  cnf(c_0_34, plain, (m1_subset_1(esk3_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|v2_tops_2(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 22.96/23.17  cnf(c_0_35, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k7_setfam_1(X3,k7_setfam_1(X3,X2)))|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X3)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_25]), c_0_29]), c_0_16])).
% 22.96/23.17  cnf(c_0_36, plain, (r2_hidden(k3_subset_1(X1,X2),k7_setfam_1(X1,X3))|~r2_hidden(X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(csr,[status(thm)],[c_0_30, c_0_15])).
% 22.96/23.17  cnf(c_0_37, plain, (r2_hidden(X1,k7_setfam_1(X2,X3))|~r2_hidden(k3_subset_1(X2,X1),X3)|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_31]), c_0_16])).
% 22.96/23.17  fof(c_0_38, plain, ![X18, X19]:((~v4_pre_topc(X19,X18)|v3_pre_topc(k3_subset_1(u1_struct_0(X18),X19),X18)|~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))|~l1_pre_topc(X18))&(~v3_pre_topc(k3_subset_1(u1_struct_0(X18),X19),X18)|v4_pre_topc(X19,X18)|~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))|~l1_pre_topc(X18))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_tops_1])])])])).
% 22.96/23.17  cnf(c_0_39, negated_conjecture, (m1_subset_1(k3_subset_1(u1_struct_0(esk4_0),X1),k1_zfmisc_1(u1_struct_0(esk4_0)))|~r2_hidden(X1,k7_setfam_1(u1_struct_0(esk4_0),esk5_0))), inference(spm,[status(thm)],[c_0_32, c_0_17])).
% 22.96/23.17  cnf(c_0_40, negated_conjecture, (r2_hidden(esk2_2(esk4_0,k7_setfam_1(u1_struct_0(esk4_0),esk5_0)),k7_setfam_1(u1_struct_0(esk4_0),esk5_0))|m1_subset_1(esk3_2(esk4_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_21]), c_0_17])])).
% 22.96/23.17  cnf(c_0_41, plain, (r2_hidden(esk3_2(X1,X2),X2)|v2_tops_2(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 22.96/23.17  cnf(c_0_42, plain, (r2_hidden(k3_subset_1(X1,X2),X3)|~r2_hidden(X2,k7_setfam_1(X1,k7_setfam_1(X4,k7_setfam_1(X4,X3))))|~m1_subset_1(k7_setfam_1(X4,k7_setfam_1(X4,X3)),k1_zfmisc_1(k1_zfmisc_1(X1)))|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X4)))), inference(spm,[status(thm)],[c_0_35, c_0_25])).
% 22.96/23.17  cnf(c_0_43, plain, (m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1))|~r2_hidden(X2,k7_setfam_1(X1,X3))|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_36]), c_0_16])).
% 22.96/23.17  cnf(c_0_44, plain, (r2_hidden(X1,k7_setfam_1(X2,k7_setfam_1(X2,X3)))|~r2_hidden(k3_subset_1(X2,X1),k7_setfam_1(X2,X3))|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_37, c_0_16])).
% 22.96/23.17  fof(c_0_45, plain, ![X20, X21]:((~v3_pre_topc(X21,X20)|v4_pre_topc(k3_subset_1(u1_struct_0(X20),X21),X20)|~m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))|~l1_pre_topc(X20))&(~v4_pre_topc(k3_subset_1(u1_struct_0(X20),X21),X20)|v3_pre_topc(X21,X20)|~m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))|~l1_pre_topc(X20))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t30_tops_1])])])])).
% 22.96/23.17  cnf(c_0_46, plain, (v3_pre_topc(k3_subset_1(u1_struct_0(X2),X1),X2)|~v4_pre_topc(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 22.96/23.17  cnf(c_0_47, negated_conjecture, (m1_subset_1(k3_subset_1(u1_struct_0(esk4_0),esk2_2(esk4_0,k7_setfam_1(u1_struct_0(esk4_0),esk5_0))),k1_zfmisc_1(u1_struct_0(esk4_0)))|m1_subset_1(esk3_2(esk4_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 22.96/23.17  cnf(c_0_48, plain, (v4_pre_topc(X3,X2)|~v2_tops_2(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~r2_hidden(X3,X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 22.96/23.17  cnf(c_0_49, negated_conjecture, (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))|~r2_hidden(X1,k7_setfam_1(u1_struct_0(esk4_0),esk5_0))), inference(spm,[status(thm)],[c_0_23, c_0_17])).
% 22.96/23.17  cnf(c_0_50, negated_conjecture, (r2_hidden(esk2_2(esk4_0,k7_setfam_1(u1_struct_0(esk4_0),esk5_0)),k7_setfam_1(u1_struct_0(esk4_0),esk5_0))|r2_hidden(esk3_2(esk4_0,esk5_0),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_41]), c_0_21]), c_0_17])])).
% 22.96/23.17  cnf(c_0_51, plain, (r2_hidden(k3_subset_1(X1,X2),X3)|~r2_hidden(X2,k7_setfam_1(X1,k7_setfam_1(X1,k7_setfam_1(X1,X3))))|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_16]), c_0_16])).
% 22.96/23.17  cnf(c_0_52, plain, (m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1))|~r2_hidden(X2,k7_setfam_1(X1,k7_setfam_1(X1,X3)))|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(spm,[status(thm)],[c_0_43, c_0_16])).
% 22.96/23.17  cnf(c_0_53, plain, (r2_hidden(X1,k7_setfam_1(X2,k7_setfam_1(X2,X3)))|~r2_hidden(X1,X3)|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_36]), c_0_15])).
% 22.96/23.17  cnf(c_0_54, plain, (v3_pre_topc(X2,X1)|~v4_pre_topc(k3_subset_1(u1_struct_0(X1),X2),X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 22.96/23.17  cnf(c_0_55, plain, (v4_pre_topc(X2,X1)|~v3_pre_topc(k3_subset_1(u1_struct_0(X1),X2),X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 22.96/23.17  cnf(c_0_56, negated_conjecture, (v3_pre_topc(k3_subset_1(u1_struct_0(esk4_0),k3_subset_1(u1_struct_0(esk4_0),esk2_2(esk4_0,k7_setfam_1(u1_struct_0(esk4_0),esk5_0)))),esk4_0)|m1_subset_1(esk3_2(esk4_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0)))|~v4_pre_topc(k3_subset_1(u1_struct_0(esk4_0),esk2_2(esk4_0,k7_setfam_1(u1_struct_0(esk4_0),esk5_0))),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_21])])).
% 22.96/23.17  cnf(c_0_57, plain, (v4_pre_topc(X1,X2)|~v2_tops_2(X3,X2)|~l1_pre_topc(X2)|~r2_hidden(X1,X3)|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))), inference(csr,[status(thm)],[c_0_48, c_0_15])).
% 22.96/23.17  cnf(c_0_58, negated_conjecture, (r2_hidden(esk3_2(esk4_0,esk5_0),esk5_0)|m1_subset_1(esk2_2(esk4_0,k7_setfam_1(u1_struct_0(esk4_0),esk5_0)),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 22.96/23.17  cnf(c_0_59, negated_conjecture, (r2_hidden(X1,k7_setfam_1(u1_struct_0(esk4_0),esk5_0))|~r2_hidden(k3_subset_1(u1_struct_0(esk4_0),X1),esk5_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(spm,[status(thm)],[c_0_37, c_0_17])).
% 22.96/23.17  cnf(c_0_60, plain, (r2_hidden(k3_subset_1(X1,k3_subset_1(X1,X2)),X3)|~r2_hidden(X2,k7_setfam_1(X1,k7_setfam_1(X1,X3)))|~m1_subset_1(k7_setfam_1(X1,k7_setfam_1(X1,X3)),k1_zfmisc_1(k1_zfmisc_1(X1)))|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(spm,[status(thm)],[c_0_51, c_0_36])).
% 22.96/23.17  cnf(c_0_61, plain, (m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1))|~r2_hidden(X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 22.96/23.17  cnf(c_0_62, plain, (v1_tops_2(X2,X1)|~v3_pre_topc(esk2_2(X1,X2),X1)|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 22.96/23.17  cnf(c_0_63, plain, (v3_pre_topc(X1,X2)|~v3_pre_topc(k3_subset_1(u1_struct_0(X2),k3_subset_1(u1_struct_0(X2),X1)),X2)|~l1_pre_topc(X2)|~m1_subset_1(k3_subset_1(u1_struct_0(X2),X1),k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 22.96/23.17  cnf(c_0_64, negated_conjecture, (v3_pre_topc(k3_subset_1(u1_struct_0(esk4_0),k3_subset_1(u1_struct_0(esk4_0),esk2_2(esk4_0,k7_setfam_1(u1_struct_0(esk4_0),esk5_0)))),esk4_0)|m1_subset_1(esk3_2(esk4_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0)))|~v2_tops_2(X1,esk4_0)|~r2_hidden(k3_subset_1(u1_struct_0(esk4_0),esk2_2(esk4_0,k7_setfam_1(u1_struct_0(esk4_0),esk5_0))),X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_21])])).
% 22.96/23.17  cnf(c_0_65, negated_conjecture, (m1_subset_1(esk2_2(esk4_0,k7_setfam_1(u1_struct_0(esk4_0),esk5_0)),k1_zfmisc_1(u1_struct_0(esk4_0)))|m1_subset_1(esk3_2(esk4_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(spm,[status(thm)],[c_0_24, c_0_58])).
% 22.96/23.17  cnf(c_0_66, negated_conjecture, (r2_hidden(k3_subset_1(u1_struct_0(esk4_0),X1),k7_setfam_1(u1_struct_0(esk4_0),esk5_0))|~r2_hidden(X1,k7_setfam_1(u1_struct_0(esk4_0),k7_setfam_1(u1_struct_0(esk4_0),esk5_0)))|~m1_subset_1(k7_setfam_1(u1_struct_0(esk4_0),k7_setfam_1(u1_struct_0(esk4_0),esk5_0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0))))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_17])]), c_0_61])).
% 22.96/23.17  cnf(c_0_67, plain, (v1_tops_2(k7_setfam_1(u1_struct_0(X1),X2),X1)|~v3_pre_topc(esk2_2(X1,k7_setfam_1(u1_struct_0(X1),X2)),X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))), inference(spm,[status(thm)],[c_0_62, c_0_16])).
% 22.96/23.17  cnf(c_0_68, negated_conjecture, (v3_pre_topc(esk2_2(esk4_0,k7_setfam_1(u1_struct_0(esk4_0),esk5_0)),esk4_0)|m1_subset_1(esk3_2(esk4_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0)))|~v2_tops_2(X1,esk4_0)|~r2_hidden(k3_subset_1(u1_struct_0(esk4_0),esk2_2(esk4_0,k7_setfam_1(u1_struct_0(esk4_0),esk5_0))),X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0))))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_21])]), c_0_65]), c_0_15])).
% 22.96/23.17  cnf(c_0_69, negated_conjecture, (r2_hidden(X1,esk5_0)|~r2_hidden(X1,k7_setfam_1(u1_struct_0(esk4_0),k7_setfam_1(u1_struct_0(esk4_0),esk5_0)))|~m1_subset_1(k7_setfam_1(u1_struct_0(esk4_0),k7_setfam_1(u1_struct_0(esk4_0),esk5_0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0))))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_66]), c_0_17])]), c_0_15])).
% 22.96/23.17  cnf(c_0_70, negated_conjecture, (v1_tops_2(k7_setfam_1(u1_struct_0(esk4_0),esk5_0),esk4_0)|m1_subset_1(esk3_2(esk4_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0)))|~v2_tops_2(X1,esk4_0)|~r2_hidden(k3_subset_1(u1_struct_0(esk4_0),esk2_2(esk4_0,k7_setfam_1(u1_struct_0(esk4_0),esk5_0))),X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_21]), c_0_17])])).
% 22.96/23.17  cnf(c_0_71, negated_conjecture, (r2_hidden(X1,esk5_0)|~r2_hidden(X1,k7_setfam_1(u1_struct_0(esk4_0),k7_setfam_1(u1_struct_0(esk4_0),esk5_0)))|~m1_subset_1(k7_setfam_1(u1_struct_0(esk4_0),esk5_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0))))), inference(spm,[status(thm)],[c_0_69, c_0_16])).
% 22.96/23.17  cnf(c_0_72, negated_conjecture, (m1_subset_1(esk3_2(esk4_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0)))|~v2_tops_2(esk5_0,esk4_0)|~v2_tops_2(X1,esk4_0)|~r2_hidden(k3_subset_1(u1_struct_0(esk4_0),esk2_2(esk4_0,k7_setfam_1(u1_struct_0(esk4_0),esk5_0))),X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0))))), inference(spm,[status(thm)],[c_0_19, c_0_70])).
% 22.96/23.17  cnf(c_0_73, negated_conjecture, (r2_hidden(X1,esk5_0)|~r2_hidden(X1,k7_setfam_1(u1_struct_0(esk4_0),k7_setfam_1(u1_struct_0(esk4_0),esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_16]), c_0_17])])).
% 22.96/23.17  cnf(c_0_74, plain, (v2_tops_2(X2,X1)|~v4_pre_topc(esk3_2(X1,X2),X1)|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 22.96/23.17  cnf(c_0_75, negated_conjecture, (m1_subset_1(esk3_2(esk4_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0)))|~v2_tops_2(X1,esk4_0)|~r2_hidden(k3_subset_1(u1_struct_0(esk4_0),esk2_2(esk4_0,k7_setfam_1(u1_struct_0(esk4_0),esk5_0))),X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_34]), c_0_21]), c_0_17])])).
% 22.96/23.17  cnf(c_0_76, negated_conjecture, (r2_hidden(k3_subset_1(u1_struct_0(esk4_0),X1),esk5_0)|~r2_hidden(X1,k7_setfam_1(u1_struct_0(esk4_0),esk5_0))|~m1_subset_1(k7_setfam_1(u1_struct_0(esk4_0),esk5_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0))))), inference(spm,[status(thm)],[c_0_73, c_0_36])).
% 22.96/23.17  cnf(c_0_77, negated_conjecture, (v2_tops_2(esk5_0,esk4_0)|~v4_pre_topc(esk3_2(esk4_0,esk5_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_17]), c_0_21])])).
% 22.96/23.17  cnf(c_0_78, plain, (v3_pre_topc(X3,X2)|~v1_tops_2(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~r2_hidden(X3,X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 22.96/23.17  cnf(c_0_79, negated_conjecture, (m1_subset_1(esk3_2(esk4_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0)))|~v2_tops_2(esk5_0,esk4_0)|~m1_subset_1(k7_setfam_1(u1_struct_0(esk4_0),esk5_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0))))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_76]), c_0_17])]), c_0_40])).
% 22.96/23.17  cnf(c_0_80, negated_conjecture, (v2_tops_2(esk5_0,esk4_0)|~v3_pre_topc(k3_subset_1(u1_struct_0(esk4_0),esk3_2(esk4_0,esk5_0)),esk4_0)|~m1_subset_1(esk3_2(esk4_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_55]), c_0_21])])).
% 22.96/23.17  cnf(c_0_81, plain, (v3_pre_topc(X1,X2)|~v1_tops_2(X3,X2)|~l1_pre_topc(X2)|~r2_hidden(X1,X3)|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))), inference(csr,[status(thm)],[c_0_78, c_0_15])).
% 22.96/23.17  cnf(c_0_82, negated_conjecture, (m1_subset_1(esk3_2(esk4_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0)))|~v2_tops_2(esk5_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_16]), c_0_17])])).
% 22.96/23.17  cnf(c_0_83, negated_conjecture, (v2_tops_2(esk5_0,esk4_0)|~v1_tops_2(X1,esk4_0)|~r2_hidden(k3_subset_1(u1_struct_0(esk4_0),esk3_2(esk4_0,esk5_0)),X1)|~m1_subset_1(esk3_2(esk4_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0)))|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_81]), c_0_21])])).
% 22.96/23.17  cnf(c_0_84, negated_conjecture, (m1_subset_1(esk3_2(esk4_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_34]), c_0_21]), c_0_17])])).
% 22.96/23.17  cnf(c_0_85, negated_conjecture, (v2_tops_2(esk5_0,esk4_0)|~v1_tops_2(X1,esk4_0)|~r2_hidden(k3_subset_1(u1_struct_0(esk4_0),esk3_2(esk4_0,esk5_0)),X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_83, c_0_84])])).
% 22.96/23.17  cnf(c_0_86, negated_conjecture, (v2_tops_2(esk5_0,esk4_0)|~v1_tops_2(k7_setfam_1(u1_struct_0(esk4_0),X1),esk4_0)|~r2_hidden(esk3_2(esk4_0,esk5_0),X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_36]), c_0_16])).
% 22.96/23.17  cnf(c_0_87, negated_conjecture, (v2_tops_2(esk5_0,esk4_0)|v1_tops_2(k7_setfam_1(u1_struct_0(esk4_0),esk5_0),esk4_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 22.96/23.17  cnf(c_0_88, negated_conjecture, (v2_tops_2(esk5_0,esk4_0)|~r2_hidden(esk3_2(esk4_0,esk5_0),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_87]), c_0_17])])).
% 22.96/23.17  cnf(c_0_89, negated_conjecture, (r2_hidden(esk2_2(esk4_0,k7_setfam_1(u1_struct_0(esk4_0),esk5_0)),k7_setfam_1(u1_struct_0(esk4_0),esk5_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_88]), c_0_50])).
% 22.96/23.17  cnf(c_0_90, plain, (m1_subset_1(esk2_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|v1_tops_2(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 22.96/23.17  cnf(c_0_91, negated_conjecture, (m1_subset_1(k3_subset_1(u1_struct_0(esk4_0),esk2_2(esk4_0,k7_setfam_1(u1_struct_0(esk4_0),esk5_0))),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(spm,[status(thm)],[c_0_39, c_0_89])).
% 22.96/23.17  cnf(c_0_92, negated_conjecture, (m1_subset_1(esk2_2(esk4_0,k7_setfam_1(u1_struct_0(esk4_0),esk5_0)),k1_zfmisc_1(u1_struct_0(esk4_0)))|~v2_tops_2(esk5_0,esk4_0)|~m1_subset_1(k7_setfam_1(u1_struct_0(esk4_0),esk5_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_90]), c_0_21])])).
% 22.96/23.17  cnf(c_0_93, negated_conjecture, (v3_pre_topc(k3_subset_1(u1_struct_0(esk4_0),k3_subset_1(u1_struct_0(esk4_0),esk2_2(esk4_0,k7_setfam_1(u1_struct_0(esk4_0),esk5_0)))),esk4_0)|~v4_pre_topc(k3_subset_1(u1_struct_0(esk4_0),esk2_2(esk4_0,k7_setfam_1(u1_struct_0(esk4_0),esk5_0))),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_91]), c_0_21])])).
% 22.96/23.17  cnf(c_0_94, negated_conjecture, (m1_subset_1(esk2_2(esk4_0,k7_setfam_1(u1_struct_0(esk4_0),esk5_0)),k1_zfmisc_1(u1_struct_0(esk4_0)))|~v2_tops_2(esk5_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_16]), c_0_17])])).
% 22.96/23.17  cnf(c_0_95, negated_conjecture, (v3_pre_topc(k3_subset_1(u1_struct_0(esk4_0),k3_subset_1(u1_struct_0(esk4_0),esk2_2(esk4_0,k7_setfam_1(u1_struct_0(esk4_0),esk5_0)))),esk4_0)|~v2_tops_2(X1,esk4_0)|~r2_hidden(k3_subset_1(u1_struct_0(esk4_0),esk2_2(esk4_0,k7_setfam_1(u1_struct_0(esk4_0),esk5_0))),X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_57]), c_0_21])])).
% 22.96/23.17  cnf(c_0_96, negated_conjecture, (m1_subset_1(esk2_2(esk4_0,k7_setfam_1(u1_struct_0(esk4_0),esk5_0)),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_88]), c_0_58])).
% 22.96/23.17  cnf(c_0_97, negated_conjecture, (v3_pre_topc(esk2_2(esk4_0,k7_setfam_1(u1_struct_0(esk4_0),esk5_0)),esk4_0)|~v2_tops_2(X1,esk4_0)|~r2_hidden(k3_subset_1(u1_struct_0(esk4_0),esk2_2(esk4_0,k7_setfam_1(u1_struct_0(esk4_0),esk5_0))),X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_95]), c_0_21]), c_0_91]), c_0_96])])).
% 22.96/23.17  cnf(c_0_98, negated_conjecture, (v1_tops_2(k7_setfam_1(u1_struct_0(esk4_0),esk5_0),esk4_0)|~v2_tops_2(X1,esk4_0)|~r2_hidden(k3_subset_1(u1_struct_0(esk4_0),esk2_2(esk4_0,k7_setfam_1(u1_struct_0(esk4_0),esk5_0))),X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_97]), c_0_21]), c_0_17])])).
% 22.96/23.17  cnf(c_0_99, negated_conjecture, (~v2_tops_2(esk5_0,esk4_0)|~v2_tops_2(X1,esk4_0)|~r2_hidden(k3_subset_1(u1_struct_0(esk4_0),esk2_2(esk4_0,k7_setfam_1(u1_struct_0(esk4_0),esk5_0))),X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0))))), inference(spm,[status(thm)],[c_0_19, c_0_98])).
% 22.96/23.17  cnf(c_0_100, negated_conjecture, (~v2_tops_2(X1,esk4_0)|~r2_hidden(k3_subset_1(u1_struct_0(esk4_0),esk2_2(esk4_0,k7_setfam_1(u1_struct_0(esk4_0),esk5_0))),X1)|~r2_hidden(esk3_2(esk4_0,esk5_0),esk5_0)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0))))), inference(spm,[status(thm)],[c_0_99, c_0_88])).
% 22.96/23.17  cnf(c_0_101, negated_conjecture, (~v2_tops_2(X1,esk4_0)|~r2_hidden(k3_subset_1(u1_struct_0(esk4_0),esk2_2(esk4_0,k7_setfam_1(u1_struct_0(esk4_0),esk5_0))),X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0))))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_41]), c_0_21]), c_0_17])]), c_0_100])).
% 22.96/23.17  cnf(c_0_102, negated_conjecture, (~v2_tops_2(esk5_0,esk4_0)|~m1_subset_1(k7_setfam_1(u1_struct_0(esk4_0),esk5_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101, c_0_76]), c_0_17]), c_0_89])])).
% 22.96/23.17  cnf(c_0_103, negated_conjecture, (~v2_tops_2(esk5_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102, c_0_16]), c_0_17])])).
% 22.96/23.17  cnf(c_0_104, negated_conjecture, (~r2_hidden(esk3_2(esk4_0,esk5_0),esk5_0)), inference(spm,[status(thm)],[c_0_103, c_0_88])).
% 22.96/23.17  cnf(c_0_105, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103, c_0_41]), c_0_21]), c_0_17])]), c_0_104]), ['proof']).
% 22.96/23.17  # SZS output end CNFRefutation
% 22.96/23.17  # Proof object total steps             : 106
% 22.96/23.17  # Proof object clause steps            : 87
% 22.96/23.17  # Proof object formula steps           : 19
% 22.96/23.17  # Proof object conjectures             : 55
% 22.96/23.17  # Proof object clause conjectures      : 52
% 22.96/23.17  # Proof object formula conjectures     : 3
% 22.96/23.17  # Proof object initial clauses used    : 21
% 22.96/23.17  # Proof object initial formulas used   : 9
% 22.96/23.17  # Proof object generating inferences   : 60
% 22.96/23.17  # Proof object simplifying inferences  : 94
% 22.96/23.17  # Training examples: 0 positive, 0 negative
% 22.96/23.17  # Parsed axioms                        : 9
% 22.96/23.17  # Removed by relevancy pruning/SinE    : 0
% 22.96/23.17  # Initial clauses                      : 25
% 22.96/23.17  # Removed in clause preprocessing      : 0
% 22.96/23.17  # Initial clauses in saturation        : 25
% 22.96/23.17  # Processed clauses                    : 15374
% 22.96/23.17  # ...of these trivial                  : 25
% 22.96/23.17  # ...subsumed                          : 8626
% 22.96/23.17  # ...remaining for further processing  : 6722
% 22.96/23.17  # Other redundant clauses eliminated   : 2
% 22.96/23.17  # Clauses deleted for lack of memory   : 0
% 22.96/23.17  # Backward-subsumed                    : 2764
% 22.96/23.17  # Backward-rewritten                   : 1376
% 22.96/23.17  # Generated clauses                    : 1455438
% 22.96/23.17  # ...of the previous two non-trivial   : 1436046
% 22.96/23.17  # Contextual simplify-reflections      : 770
% 22.96/23.17  # Paramodulations                      : 1455200
% 22.96/23.17  # Factorizations                       : 220
% 22.96/23.17  # Equation resolutions                 : 2
% 22.96/23.17  # Propositional unsat checks           : 0
% 22.96/23.17  #    Propositional check models        : 0
% 22.96/23.17  #    Propositional check unsatisfiable : 0
% 22.96/23.17  #    Propositional clauses             : 0
% 22.96/23.17  #    Propositional clauses after purity: 0
% 22.96/23.17  #    Propositional unsat core size     : 0
% 22.96/23.17  #    Propositional preprocessing time  : 0.000
% 22.96/23.17  #    Propositional encoding time       : 0.000
% 22.96/23.17  #    Propositional solver time         : 0.000
% 22.96/23.17  #    Success case prop preproc time    : 0.000
% 22.96/23.17  #    Success case prop encoding time   : 0.000
% 22.96/23.17  #    Success case prop solver time     : 0.000
% 22.96/23.17  # Current number of processed clauses  : 2539
% 22.96/23.17  #    Positive orientable unit clauses  : 17
% 22.96/23.17  #    Positive unorientable unit clauses: 0
% 22.96/23.17  #    Negative unit clauses             : 2
% 22.96/23.17  #    Non-unit-clauses                  : 2520
% 22.96/23.17  # Current number of unprocessed clauses: 1417423
% 22.96/23.17  # ...number of literals in the above   : 17557098
% 22.96/23.17  # Current number of archived formulas  : 0
% 22.96/23.17  # Current number of archived clauses   : 4181
% 22.96/23.17  # Clause-clause subsumption calls (NU) : 3478160
% 22.96/23.17  # Rec. Clause-clause subsumption calls : 279198
% 22.96/23.17  # Non-unit clause-clause subsumptions  : 11866
% 22.96/23.17  # Unit Clause-clause subsumption calls : 15687
% 22.96/23.17  # Rewrite failures with RHS unbound    : 0
% 22.96/23.17  # BW rewrite match attempts            : 482
% 22.96/23.17  # BW rewrite match successes           : 15
% 22.96/23.17  # Condensation attempts                : 0
% 22.96/23.17  # Condensation successes               : 0
% 22.96/23.17  # Termbank termtop insertions          : 84038111
% 23.03/23.25  
% 23.03/23.25  # -------------------------------------------------
% 23.03/23.25  # User time                : 22.137 s
% 23.03/23.25  # System time              : 0.780 s
% 23.03/23.25  # Total time               : 22.917 s
% 23.03/23.25  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
