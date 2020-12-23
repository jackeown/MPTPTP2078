%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:13:00 EST 2020

% Result     : Theorem 35.33s
% Output     : CNFRefutation 35.33s
% Verified   : 
% Statistics : Number of formulae       :   98 (8155 expanded)
%              Number of clauses        :   87 (3215 expanded)
%              Number of leaves         :    5 (1958 expanded)
%              Depth                    :   31
%              Number of atoms          :  466 (33860 expanded)
%              Number of equality atoms :   14 (1163 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal clause size      :   26 (   5 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t16_tops_2,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
         => ( v2_tops_2(X2,X1)
          <=> v1_tops_2(k7_setfam_1(u1_struct_0(X1),X2),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_tops_2)).

fof(dt_k7_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => m1_subset_1(k7_setfam_1(X1,X2),k1_zfmisc_1(k1_zfmisc_1(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_setfam_1)).

fof(t17_tops_2,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
         => ( v1_tops_2(X2,X1)
          <=> v2_tops_2(k7_setfam_1(u1_struct_0(X1),X2),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_tops_2)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_setfam_1)).

fof(t49_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => ( r2_hidden(k3_subset_1(X1,X3),k7_setfam_1(X1,X2))
          <=> r2_hidden(X3,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_setfam_1)).

fof(c_0_5,plain,(
    ! [X15,X16] :
      ( ( ~ v2_tops_2(X16,X15)
        | v1_tops_2(k7_setfam_1(u1_struct_0(X15),X16),X15)
        | ~ m1_subset_1(X16,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X15))))
        | ~ l1_pre_topc(X15) )
      & ( ~ v1_tops_2(k7_setfam_1(u1_struct_0(X15),X16),X15)
        | v2_tops_2(X16,X15)
        | ~ m1_subset_1(X16,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X15))))
        | ~ l1_pre_topc(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t16_tops_2])])])])).

fof(c_0_6,plain,(
    ! [X10,X11] :
      ( ~ m1_subset_1(X11,k1_zfmisc_1(k1_zfmisc_1(X10)))
      | m1_subset_1(k7_setfam_1(X10,X11),k1_zfmisc_1(k1_zfmisc_1(X10))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_setfam_1])])).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
           => ( v1_tops_2(X2,X1)
            <=> v2_tops_2(k7_setfam_1(u1_struct_0(X1),X2),X1) ) ) ) ),
    inference(assume_negation,[status(cth)],[t17_tops_2])).

cnf(c_0_8,plain,
    ( v1_tops_2(k7_setfam_1(u1_struct_0(X2),X1),X2)
    | ~ v2_tops_2(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( m1_subset_1(k7_setfam_1(X2,X1),k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_10,negated_conjecture,
    ( l1_pre_topc(esk2_0)
    & m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))))
    & ( ~ v1_tops_2(esk3_0,esk2_0)
      | ~ v2_tops_2(k7_setfam_1(u1_struct_0(esk2_0),esk3_0),esk2_0) )
    & ( v1_tops_2(esk3_0,esk2_0)
      | v2_tops_2(k7_setfam_1(u1_struct_0(esk2_0),esk3_0),esk2_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

cnf(c_0_11,plain,
    ( v1_tops_2(k7_setfam_1(u1_struct_0(X1),k7_setfam_1(u1_struct_0(X1),X2)),X1)
    | ~ v2_tops_2(k7_setfam_1(u1_struct_0(X1),X2),X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ),
    inference(spm,[status(thm)],[c_0_8,c_0_9])).

cnf(c_0_12,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_13,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,plain,
    ( v2_tops_2(X2,X1)
    | ~ v1_tops_2(k7_setfam_1(u1_struct_0(X1),X2),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_15,plain,(
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

cnf(c_0_16,negated_conjecture,
    ( v1_tops_2(k7_setfam_1(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0)),esk2_0)
    | ~ v2_tops_2(k7_setfam_1(u1_struct_0(esk2_0),esk3_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_12]),c_0_13])])).

cnf(c_0_17,negated_conjecture,
    ( v1_tops_2(esk3_0,esk2_0)
    | v2_tops_2(k7_setfam_1(u1_struct_0(esk2_0),esk3_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,plain,
    ( v2_tops_2(k7_setfam_1(u1_struct_0(X1),X2),X1)
    | ~ v1_tops_2(k7_setfam_1(u1_struct_0(X1),k7_setfam_1(u1_struct_0(X1),X2)),X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ),
    inference(spm,[status(thm)],[c_0_14,c_0_9])).

cnf(c_0_19,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(X1))
    | X3 = k7_setfam_1(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X3)
    | r2_hidden(k3_subset_1(X1,esk1_3(X1,X2,X3)),X2)
    | X3 = k7_setfam_1(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,negated_conjecture,
    ( v1_tops_2(k7_setfam_1(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0)),esk2_0)
    | v1_tops_2(esk3_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_22,plain,
    ( X3 = k7_setfam_1(X1,X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ r2_hidden(k3_subset_1(X1,esk1_3(X1,X2,X3)),X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,plain,
    ( v2_tops_2(k7_setfam_1(u1_struct_0(X1),X2),X1)
    | m1_subset_1(esk1_3(u1_struct_0(X1),k7_setfam_1(u1_struct_0(X1),X2),X3),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_tops_2(X3,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_9])).

cnf(c_0_24,plain,
    ( v2_tops_2(k7_setfam_1(u1_struct_0(X1),X2),X1)
    | r2_hidden(k3_subset_1(u1_struct_0(X1),esk1_3(u1_struct_0(X1),k7_setfam_1(u1_struct_0(X1),X2),X3)),k7_setfam_1(u1_struct_0(X1),X2))
    | r2_hidden(esk1_3(u1_struct_0(X1),k7_setfam_1(u1_struct_0(X1),X2),X3),X3)
    | ~ v1_tops_2(X3,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_20]),c_0_9])).

cnf(c_0_25,negated_conjecture,
    ( v1_tops_2(esk3_0,esk2_0)
    | v1_tops_2(X1,esk2_0)
    | ~ r2_hidden(k3_subset_1(u1_struct_0(esk2_0),esk1_3(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0),X1)),k7_setfam_1(u1_struct_0(esk2_0),esk3_0))
    | ~ r2_hidden(esk1_3(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0),X1),X1)
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0(esk2_0),esk3_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0)))) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

fof(c_0_26,plain,(
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

cnf(c_0_27,negated_conjecture,
    ( v1_tops_2(esk3_0,esk2_0)
    | v1_tops_2(X1,esk2_0)
    | m1_subset_1(esk1_3(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0),X1),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0(esk2_0),esk3_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0)))) ),
    inference(spm,[status(thm)],[c_0_21,c_0_19])).

cnf(c_0_28,negated_conjecture,
    ( v2_tops_2(k7_setfam_1(u1_struct_0(esk2_0),esk3_0),esk2_0)
    | m1_subset_1(esk1_3(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0),X1),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ v1_tops_2(X1,esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_12]),c_0_13])])).

cnf(c_0_29,negated_conjecture,
    ( v2_tops_2(k7_setfam_1(u1_struct_0(esk2_0),esk3_0),esk2_0)
    | r2_hidden(k3_subset_1(u1_struct_0(esk2_0),esk1_3(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0),X1)),k7_setfam_1(u1_struct_0(esk2_0),esk3_0))
    | r2_hidden(esk1_3(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0),X1),X1)
    | ~ v1_tops_2(X1,esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_12]),c_0_13])])).

cnf(c_0_30,negated_conjecture,
    ( v1_tops_2(esk3_0,esk2_0)
    | v1_tops_2(X1,esk2_0)
    | ~ r2_hidden(k3_subset_1(u1_struct_0(esk2_0),esk1_3(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0),X1)),k7_setfam_1(u1_struct_0(esk2_0),esk3_0))
    | ~ r2_hidden(esk1_3(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0),X1),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_9]),c_0_12])])).

cnf(c_0_31,plain,
    ( r2_hidden(k3_subset_1(X3,X1),k7_setfam_1(X3,X2))
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_32,negated_conjecture,
    ( v1_tops_2(esk3_0,esk2_0)
    | v1_tops_2(X1,esk2_0)
    | m1_subset_1(esk1_3(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0),X1),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_9]),c_0_12])])).

cnf(c_0_33,negated_conjecture,
    ( v1_tops_2(k7_setfam_1(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0)),esk2_0)
    | m1_subset_1(esk1_3(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0),X1),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ v1_tops_2(X1,esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0)))) ),
    inference(spm,[status(thm)],[c_0_16,c_0_28])).

cnf(c_0_34,negated_conjecture,
    ( v1_tops_2(k7_setfam_1(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0)),esk2_0)
    | r2_hidden(k3_subset_1(u1_struct_0(esk2_0),esk1_3(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0),X1)),k7_setfam_1(u1_struct_0(esk2_0),esk3_0))
    | r2_hidden(esk1_3(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0),X1),X1)
    | ~ v1_tops_2(X1,esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0)))) ),
    inference(spm,[status(thm)],[c_0_16,c_0_29])).

cnf(c_0_35,negated_conjecture,
    ( v1_tops_2(esk3_0,esk2_0)
    | v1_tops_2(X1,esk2_0)
    | r2_hidden(k3_subset_1(u1_struct_0(esk2_0),esk1_3(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0),X1)),k7_setfam_1(u1_struct_0(esk2_0),esk3_0))
    | r2_hidden(esk1_3(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0),X1),X1)
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0(esk2_0),esk3_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0)))) ),
    inference(spm,[status(thm)],[c_0_21,c_0_20])).

cnf(c_0_36,negated_conjecture,
    ( v1_tops_2(esk3_0,esk2_0)
    | v1_tops_2(X1,esk2_0)
    | ~ r2_hidden(esk1_3(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0),X1),esk3_0)
    | ~ r2_hidden(esk1_3(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0),X1),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0)))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_12])]),c_0_32])).

cnf(c_0_37,negated_conjecture,
    ( v1_tops_2(k7_setfam_1(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0)),esk2_0)
    | m1_subset_1(esk1_3(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0),esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_12]),c_0_21])).

cnf(c_0_38,negated_conjecture,
    ( v1_tops_2(k7_setfam_1(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0)),esk2_0)
    | r2_hidden(k3_subset_1(u1_struct_0(esk2_0),esk1_3(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0),esk3_0)),k7_setfam_1(u1_struct_0(esk2_0),esk3_0))
    | r2_hidden(esk1_3(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0),esk3_0),esk3_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_12]),c_0_21])).

cnf(c_0_39,negated_conjecture,
    ( v1_tops_2(esk3_0,esk2_0)
    | v1_tops_2(X1,esk2_0)
    | r2_hidden(k3_subset_1(u1_struct_0(esk2_0),esk1_3(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0),X1)),k7_setfam_1(u1_struct_0(esk2_0),esk3_0))
    | r2_hidden(esk1_3(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0),X1),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_9]),c_0_12])])).

cnf(c_0_40,negated_conjecture,
    ( v1_tops_2(esk3_0,esk2_0)
    | ~ r2_hidden(esk1_3(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0),esk3_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(ef,[status(thm)],[c_0_36]),c_0_12])])).

cnf(c_0_41,negated_conjecture,
    ( ~ v1_tops_2(esk3_0,esk2_0)
    | ~ v2_tops_2(k7_setfam_1(u1_struct_0(esk2_0),esk3_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_42,negated_conjecture,
    ( v2_tops_2(k7_setfam_1(u1_struct_0(esk2_0),esk3_0),esk2_0)
    | m1_subset_1(esk1_3(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0),esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_37]),c_0_13]),c_0_12])])).

cnf(c_0_43,negated_conjecture,
    ( v2_tops_2(k7_setfam_1(u1_struct_0(esk2_0),esk3_0),esk2_0)
    | r2_hidden(k3_subset_1(u1_struct_0(esk2_0),esk1_3(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0),esk3_0)),k7_setfam_1(u1_struct_0(esk2_0),esk3_0))
    | r2_hidden(esk1_3(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0),esk3_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_38]),c_0_13]),c_0_12])])).

cnf(c_0_44,negated_conjecture,
    ( v1_tops_2(esk3_0,esk2_0)
    | r2_hidden(k3_subset_1(u1_struct_0(esk2_0),esk1_3(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0),esk3_0)),k7_setfam_1(u1_struct_0(esk2_0),esk3_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(ef,[status(thm)],[c_0_39]),c_0_12])]),c_0_40])).

cnf(c_0_45,negated_conjecture,
    ( m1_subset_1(esk1_3(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0),esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ v1_tops_2(esk3_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_46,plain,
    ( r2_hidden(X2,X3)
    | ~ r2_hidden(k3_subset_1(X1,X2),k7_setfam_1(X1,X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(k3_subset_1(u1_struct_0(esk2_0),esk1_3(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0),esk3_0)),k7_setfam_1(u1_struct_0(esk2_0),esk3_0))
    | r2_hidden(esk1_3(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0),esk3_0),esk3_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_43]),c_0_44])).

cnf(c_0_48,negated_conjecture,
    ( m1_subset_1(esk1_3(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0),esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(ef,[status(thm)],[c_0_32]),c_0_12])]),c_0_45])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(esk1_3(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0),esk3_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_12]),c_0_48])])).

cnf(c_0_50,negated_conjecture,
    ( v1_tops_2(esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_49])])).

cnf(c_0_51,plain,
    ( X1 = X2
    | m1_subset_1(esk1_3(X3,X4,X2),k1_zfmisc_1(X3))
    | m1_subset_1(esk1_3(X3,X4,X1),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X3)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X3))) ),
    inference(spm,[status(thm)],[c_0_19,c_0_19])).

cnf(c_0_52,negated_conjecture,
    ( v1_tops_2(X1,esk2_0)
    | m1_subset_1(esk1_3(X2,X3,esk3_0),k1_zfmisc_1(X2))
    | m1_subset_1(esk1_3(X2,X3,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_53,negated_conjecture,
    ( ~ v2_tops_2(k7_setfam_1(u1_struct_0(esk2_0),esk3_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_50])])).

cnf(c_0_54,negated_conjecture,
    ( v2_tops_2(k7_setfam_1(u1_struct_0(esk2_0),X1),esk2_0)
    | m1_subset_1(esk1_3(X2,X3,k7_setfam_1(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),X1))),k1_zfmisc_1(X2))
    | m1_subset_1(esk1_3(X2,X3,esk3_0),k1_zfmisc_1(X2))
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),X1)),k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_52]),c_0_13])])).

cnf(c_0_55,negated_conjecture,
    ( m1_subset_1(esk1_3(X1,X2,k7_setfam_1(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0))),k1_zfmisc_1(X1))
    | m1_subset_1(esk1_3(X1,X2,esk3_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0)),k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_12])])).

cnf(c_0_56,negated_conjecture,
    ( m1_subset_1(esk1_3(X1,X2,esk3_0),k1_zfmisc_1(X1))
    | m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))))
    | m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(X1))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(spm,[status(thm)],[c_0_12,c_0_51])).

cnf(c_0_57,plain,
    ( r2_hidden(X2,X4)
    | ~ r2_hidden(k3_subset_1(X1,X2),X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | X4 != k7_setfam_1(X1,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_58,negated_conjecture,
    ( m1_subset_1(esk1_3(X1,X2,esk3_0),k1_zfmisc_1(X1))
    | m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(X1))
    | ~ r2_hidden(k3_subset_1(u1_struct_0(esk2_0),esk1_3(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0),X3)),k7_setfam_1(u1_struct_0(esk2_0),esk3_0))
    | ~ r2_hidden(esk1_3(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0),X3),X3)
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0(esk2_0),esk3_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_22]),c_0_56])).

cnf(c_0_59,plain,
    ( X1 = X2
    | m1_subset_1(esk1_3(X3,X4,X1),k1_zfmisc_1(X3))
    | ~ r2_hidden(k3_subset_1(X3,esk1_3(X3,X4,X2)),X4)
    | ~ r2_hidden(esk1_3(X3,X4,X2),X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X3)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X3))) ),
    inference(spm,[status(thm)],[c_0_19,c_0_22])).

cnf(c_0_60,plain,
    ( r2_hidden(X1,k7_setfam_1(X2,X3))
    | ~ r2_hidden(k3_subset_1(X2,X1),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_57]),c_0_9])).

cnf(c_0_61,negated_conjecture,
    ( m1_subset_1(esk1_3(X1,X2,esk3_0),k1_zfmisc_1(X1))
    | m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(X1))
    | ~ r2_hidden(k3_subset_1(u1_struct_0(esk2_0),esk1_3(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0),X3)),k7_setfam_1(u1_struct_0(esk2_0),esk3_0))
    | ~ r2_hidden(esk1_3(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0),X3),X3)
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_9]),c_0_12])])).

cnf(c_0_62,negated_conjecture,
    ( v1_tops_2(X1,esk2_0)
    | m1_subset_1(esk1_3(X2,X3,X1),k1_zfmisc_1(X2))
    | ~ r2_hidden(k3_subset_1(X2,esk1_3(X2,X3,esk3_0)),X3)
    | ~ r2_hidden(esk1_3(X2,X3,esk3_0),esk3_0)
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(spm,[status(thm)],[c_0_50,c_0_59])).

cnf(c_0_63,plain,
    ( r2_hidden(X1,k7_setfam_1(X2,X3))
    | m1_subset_1(esk1_3(X2,X3,k7_setfam_1(X4,X5)),k1_zfmisc_1(X2))
    | ~ r2_hidden(k3_subset_1(X4,X1),X5)
    | ~ m1_subset_1(k7_setfam_1(X4,X5),k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k1_zfmisc_1(X4)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X4)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_19])).

cnf(c_0_64,negated_conjecture,
    ( m1_subset_1(esk1_3(X1,X2,esk3_0),k1_zfmisc_1(X1))
    | ~ r2_hidden(k3_subset_1(u1_struct_0(esk2_0),esk1_3(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0),esk3_0)),k7_setfam_1(u1_struct_0(esk2_0),esk3_0))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(ef,[status(thm)],[c_0_61]),c_0_49])])).

cnf(c_0_65,negated_conjecture,
    ( v2_tops_2(k7_setfam_1(u1_struct_0(esk2_0),X1),esk2_0)
    | m1_subset_1(esk1_3(X2,X3,k7_setfam_1(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),X1))),k1_zfmisc_1(X2))
    | ~ r2_hidden(k3_subset_1(X2,esk1_3(X2,X3,esk3_0)),X3)
    | ~ r2_hidden(esk1_3(X2,X3,esk3_0),esk3_0)
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),X1)),k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_62]),c_0_13])])).

cnf(c_0_66,plain,
    ( r2_hidden(X1,k7_setfam_1(X2,X3))
    | m1_subset_1(esk1_3(X2,X3,k7_setfam_1(X2,X4)),k1_zfmisc_1(X2))
    | ~ r2_hidden(k3_subset_1(X2,X1),X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_63,c_0_9])).

cnf(c_0_67,plain,
    ( X1 = X2
    | ~ r2_hidden(k3_subset_1(X3,esk1_3(X3,X4,X1)),X4)
    | ~ r2_hidden(k3_subset_1(X3,esk1_3(X3,X4,X2)),X4)
    | ~ r2_hidden(esk1_3(X3,X4,X1),X1)
    | ~ r2_hidden(esk1_3(X3,X4,X2),X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X3)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X3))) ),
    inference(spm,[status(thm)],[c_0_22,c_0_22])).

cnf(c_0_68,negated_conjecture,
    ( m1_subset_1(esk1_3(X1,X2,esk3_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_31]),c_0_49]),c_0_12]),c_0_48])])).

cnf(c_0_69,negated_conjecture,
    ( m1_subset_1(esk1_3(X1,X2,k7_setfam_1(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0))),k1_zfmisc_1(X1))
    | ~ r2_hidden(k3_subset_1(X1,esk1_3(X1,X2,esk3_0)),X2)
    | ~ r2_hidden(esk1_3(X1,X2,esk3_0),esk3_0)
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0)),k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_65]),c_0_12])])).

cnf(c_0_70,plain,
    ( r2_hidden(X1,k7_setfam_1(X2,X3))
    | m1_subset_1(esk1_3(X2,X3,k7_setfam_1(X2,k7_setfam_1(X2,X4))),k1_zfmisc_1(X2))
    | ~ r2_hidden(k3_subset_1(X2,X1),k7_setfam_1(X2,X4))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_66,c_0_9])).

cnf(c_0_71,negated_conjecture,
    ( v1_tops_2(X1,esk2_0)
    | ~ r2_hidden(k3_subset_1(X2,esk1_3(X2,X3,esk3_0)),X3)
    | ~ r2_hidden(k3_subset_1(X2,esk1_3(X2,X3,X1)),X3)
    | ~ r2_hidden(esk1_3(X2,X3,esk3_0),esk3_0)
    | ~ r2_hidden(esk1_3(X2,X3,X1),X1)
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(spm,[status(thm)],[c_0_50,c_0_67])).

cnf(c_0_72,negated_conjecture,
    ( m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(X1))
    | m1_subset_1(esk1_3(X4,X5,X3),k1_zfmisc_1(X4))
    | ~ r2_hidden(k3_subset_1(X1,esk1_3(X1,X2,esk3_0)),X2)
    | ~ r2_hidden(esk1_3(X1,X2,esk3_0),esk3_0)
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X4)))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k1_zfmisc_1(X4)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(spm,[status(thm)],[c_0_68,c_0_59])).

cnf(c_0_73,negated_conjecture,
    ( m1_subset_1(esk1_3(u1_struct_0(esk2_0),X1,k7_setfam_1(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0))),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ r2_hidden(k3_subset_1(u1_struct_0(esk2_0),esk1_3(u1_struct_0(esk2_0),X1,esk3_0)),X1)
    | ~ r2_hidden(esk1_3(u1_struct_0(esk2_0),X1,esk3_0),esk3_0)
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0(esk2_0),esk3_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_9]),c_0_12])])).

cnf(c_0_74,plain,
    ( r2_hidden(k3_subset_1(X3,X1),X4)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3))
    | X2 != k7_setfam_1(X3,X4)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_75,plain,
    ( r2_hidden(X1,k7_setfam_1(X2,X3))
    | m1_subset_1(esk1_3(X2,X3,k7_setfam_1(X2,k7_setfam_1(X2,X4))),k1_zfmisc_1(X2))
    | ~ r2_hidden(X1,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_70,c_0_31])).

cnf(c_0_76,negated_conjecture,
    ( v2_tops_2(k7_setfam_1(u1_struct_0(esk2_0),X1),esk2_0)
    | ~ r2_hidden(esk1_3(X2,X3,k7_setfam_1(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),X1))),k7_setfam_1(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),X1)))
    | ~ r2_hidden(k3_subset_1(X2,esk1_3(X2,X3,k7_setfam_1(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),X1)))),X3)
    | ~ r2_hidden(k3_subset_1(X2,esk1_3(X2,X3,esk3_0)),X3)
    | ~ r2_hidden(esk1_3(X2,X3,esk3_0),esk3_0)
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),X1)),k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_71]),c_0_13])])).

cnf(c_0_77,plain,
    ( r2_hidden(X1,k7_setfam_1(X2,k7_setfam_1(X2,X3)))
    | ~ r2_hidden(k3_subset_1(X2,X1),k7_setfam_1(X2,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_9])).

cnf(c_0_78,negated_conjecture,
    ( m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(X1))
    | ~ r2_hidden(k3_subset_1(X1,esk1_3(X1,X2,esk3_0)),X2)
    | ~ r2_hidden(esk1_3(X1,X2,esk3_0),esk3_0)
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(ef,[status(thm)],[c_0_72])).

cnf(c_0_79,negated_conjecture,
    ( m1_subset_1(esk1_3(u1_struct_0(esk2_0),X1,k7_setfam_1(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0))),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ r2_hidden(k3_subset_1(u1_struct_0(esk2_0),esk1_3(u1_struct_0(esk2_0),X1,esk3_0)),X1)
    | ~ r2_hidden(esk1_3(u1_struct_0(esk2_0),X1,esk3_0),esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_9]),c_0_12])])).

cnf(c_0_80,plain,
    ( r2_hidden(k3_subset_1(X1,X2),X3)
    | ~ r2_hidden(X2,k7_setfam_1(X1,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_74]),c_0_9])).

cnf(c_0_81,plain,
    ( r2_hidden(X1,k7_setfam_1(X2,k7_setfam_1(X2,X3)))
    | m1_subset_1(esk1_3(X2,k7_setfam_1(X2,X3),k7_setfam_1(X2,k7_setfam_1(X2,X4))),k1_zfmisc_1(X2))
    | ~ r2_hidden(X1,X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_75,c_0_9])).

cnf(c_0_82,negated_conjecture,
    ( ~ r2_hidden(esk1_3(X1,X2,k7_setfam_1(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0))),k7_setfam_1(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0)))
    | ~ r2_hidden(k3_subset_1(X1,esk1_3(X1,X2,k7_setfam_1(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0)))),X2)
    | ~ r2_hidden(k3_subset_1(X1,esk1_3(X1,X2,esk3_0)),X2)
    | ~ r2_hidden(esk1_3(X1,X2,esk3_0),esk3_0)
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0)),k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_76]),c_0_12])])).

cnf(c_0_83,plain,
    ( r2_hidden(X1,k7_setfam_1(X2,k7_setfam_1(X2,X3)))
    | ~ r2_hidden(X1,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_77,c_0_31])).

cnf(c_0_84,negated_conjecture,
    ( m1_subset_1(esk1_3(X1,k7_setfam_1(X1,X2),X3),k1_zfmisc_1(X1))
    | ~ r2_hidden(esk1_3(X1,k7_setfam_1(X1,X2),esk3_0),esk3_0)
    | ~ r2_hidden(esk1_3(X1,k7_setfam_1(X1,X2),esk3_0),X2)
    | ~ m1_subset_1(esk1_3(X1,k7_setfam_1(X1,X2),esk3_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_31]),c_0_9])).

cnf(c_0_85,negated_conjecture,
    ( m1_subset_1(esk1_3(u1_struct_0(esk2_0),X1,k7_setfam_1(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0))),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ r2_hidden(esk1_3(u1_struct_0(esk2_0),X1,esk3_0),k7_setfam_1(u1_struct_0(esk2_0),X1))
    | ~ r2_hidden(esk1_3(u1_struct_0(esk2_0),X1,esk3_0),esk3_0)
    | ~ m1_subset_1(esk1_3(u1_struct_0(esk2_0),X1,esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0)))) ),
    inference(spm,[status(thm)],[c_0_79,c_0_80])).

cnf(c_0_86,negated_conjecture,
    ( r2_hidden(X1,k7_setfam_1(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),X2)))
    | m1_subset_1(esk1_3(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),X2),k7_setfam_1(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0))),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ r2_hidden(X1,esk3_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_81,c_0_12])).

cnf(c_0_87,negated_conjecture,
    ( ~ r2_hidden(k3_subset_1(X1,esk1_3(X1,X2,k7_setfam_1(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0)))),X2)
    | ~ r2_hidden(esk1_3(X1,X2,k7_setfam_1(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0))),esk3_0)
    | ~ r2_hidden(k3_subset_1(X1,esk1_3(X1,X2,esk3_0)),X2)
    | ~ r2_hidden(esk1_3(X1,X2,esk3_0),esk3_0)
    | ~ m1_subset_1(esk1_3(X1,X2,k7_setfam_1(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0))),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0)),k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_12])])).

cnf(c_0_88,negated_conjecture,
    ( m1_subset_1(esk1_3(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0),X1),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_48]),c_0_49]),c_0_12])])).

cnf(c_0_89,negated_conjecture,
    ( m1_subset_1(esk1_3(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),X1),k7_setfam_1(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0))),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ r2_hidden(esk1_3(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),X1),esk3_0),esk3_0)
    | ~ m1_subset_1(esk1_3(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),X1),esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_86]),c_0_9])).

cnf(c_0_90,negated_conjecture,
    ( ~ r2_hidden(k3_subset_1(u1_struct_0(esk2_0),esk1_3(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0),k7_setfam_1(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0)))),k7_setfam_1(u1_struct_0(esk2_0),esk3_0))
    | ~ r2_hidden(esk1_3(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0),k7_setfam_1(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0))),esk3_0)
    | ~ r2_hidden(k3_subset_1(u1_struct_0(esk2_0),esk1_3(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0),esk3_0)),k7_setfam_1(u1_struct_0(esk2_0),esk3_0))
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0(esk2_0),esk3_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0)))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_88]),c_0_49]),c_0_12])]),c_0_9])).

cnf(c_0_91,negated_conjecture,
    ( m1_subset_1(esk1_3(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0),k7_setfam_1(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0))),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_48]),c_0_49]),c_0_12])])).

cnf(c_0_92,negated_conjecture,
    ( ~ r2_hidden(esk1_3(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0),k7_setfam_1(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0))),esk3_0)
    | ~ r2_hidden(k3_subset_1(u1_struct_0(esk2_0),esk1_3(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0),esk3_0)),k7_setfam_1(u1_struct_0(esk2_0),esk3_0))
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0(esk2_0),esk3_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_31]),c_0_12]),c_0_91])])).

cnf(c_0_93,negated_conjecture,
    ( ~ r2_hidden(k3_subset_1(u1_struct_0(esk2_0),esk1_3(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0),esk3_0)),k7_setfam_1(u1_struct_0(esk2_0),esk3_0))
    | ~ r2_hidden(k3_subset_1(u1_struct_0(esk2_0),esk1_3(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0),X1)),k7_setfam_1(u1_struct_0(esk2_0),esk3_0))
    | ~ r2_hidden(esk1_3(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0),X1),esk3_0)
    | ~ r2_hidden(esk1_3(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0),X1),X1)
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0(esk2_0),esk3_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0)))) ),
    inference(spm,[status(thm)],[c_0_92,c_0_22])).

cnf(c_0_94,negated_conjecture,
    ( ~ r2_hidden(k3_subset_1(u1_struct_0(esk2_0),esk1_3(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0),X1)),k7_setfam_1(u1_struct_0(esk2_0),esk3_0))
    | ~ r2_hidden(esk1_3(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0),X1),esk3_0)
    | ~ r2_hidden(esk1_3(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0),X1),X1)
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0(esk2_0),esk3_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_31]),c_0_49]),c_0_12]),c_0_48])])).

cnf(c_0_95,negated_conjecture,
    ( ~ r2_hidden(k3_subset_1(u1_struct_0(esk2_0),esk1_3(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0),X1)),k7_setfam_1(u1_struct_0(esk2_0),esk3_0))
    | ~ r2_hidden(esk1_3(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0),X1),esk3_0)
    | ~ r2_hidden(esk1_3(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0),X1),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_9]),c_0_12])])).

cnf(c_0_96,negated_conjecture,
    ( ~ r2_hidden(esk1_3(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0),X1),esk3_0)
    | ~ r2_hidden(esk1_3(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0),X1),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0)))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_31]),c_0_12])]),c_0_88])).

cnf(c_0_97,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_49]),c_0_49]),c_0_12])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:51:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 35.33/35.53  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S039A
% 35.33/35.53  # and selection function PSelectUnlessUniqMaxPos.
% 35.33/35.53  #
% 35.33/35.53  # Preprocessing time       : 0.027 s
% 35.33/35.53  # Presaturation interreduction done
% 35.33/35.53  
% 35.33/35.53  # Proof found!
% 35.33/35.53  # SZS status Theorem
% 35.33/35.53  # SZS output start CNFRefutation
% 35.33/35.53  fof(t16_tops_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>(v2_tops_2(X2,X1)<=>v1_tops_2(k7_setfam_1(u1_struct_0(X1),X2),X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_tops_2)).
% 35.33/35.53  fof(dt_k7_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>m1_subset_1(k7_setfam_1(X1,X2),k1_zfmisc_1(k1_zfmisc_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_setfam_1)).
% 35.33/35.53  fof(t17_tops_2, conjecture, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>(v1_tops_2(X2,X1)<=>v2_tops_2(k7_setfam_1(u1_struct_0(X1),X2),X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_tops_2)).
% 35.33/35.53  fof(d8_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))=>(X3=k7_setfam_1(X1,X2)<=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(X1))=>(r2_hidden(X4,X3)<=>r2_hidden(k3_subset_1(X1,X4),X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_setfam_1)).
% 35.33/35.53  fof(t49_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(r2_hidden(k3_subset_1(X1,X3),k7_setfam_1(X1,X2))<=>r2_hidden(X3,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_setfam_1)).
% 35.33/35.53  fof(c_0_5, plain, ![X15, X16]:((~v2_tops_2(X16,X15)|v1_tops_2(k7_setfam_1(u1_struct_0(X15),X16),X15)|~m1_subset_1(X16,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X15))))|~l1_pre_topc(X15))&(~v1_tops_2(k7_setfam_1(u1_struct_0(X15),X16),X15)|v2_tops_2(X16,X15)|~m1_subset_1(X16,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X15))))|~l1_pre_topc(X15))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t16_tops_2])])])])).
% 35.33/35.53  fof(c_0_6, plain, ![X10, X11]:(~m1_subset_1(X11,k1_zfmisc_1(k1_zfmisc_1(X10)))|m1_subset_1(k7_setfam_1(X10,X11),k1_zfmisc_1(k1_zfmisc_1(X10)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_setfam_1])])).
% 35.33/35.53  fof(c_0_7, negated_conjecture, ~(![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>(v1_tops_2(X2,X1)<=>v2_tops_2(k7_setfam_1(u1_struct_0(X1),X2),X1))))), inference(assume_negation,[status(cth)],[t17_tops_2])).
% 35.33/35.53  cnf(c_0_8, plain, (v1_tops_2(k7_setfam_1(u1_struct_0(X2),X1),X2)|~v2_tops_2(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 35.33/35.53  cnf(c_0_9, plain, (m1_subset_1(k7_setfam_1(X2,X1),k1_zfmisc_1(k1_zfmisc_1(X2)))|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 35.33/35.53  fof(c_0_10, negated_conjecture, (l1_pre_topc(esk2_0)&(m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))))&((~v1_tops_2(esk3_0,esk2_0)|~v2_tops_2(k7_setfam_1(u1_struct_0(esk2_0),esk3_0),esk2_0))&(v1_tops_2(esk3_0,esk2_0)|v2_tops_2(k7_setfam_1(u1_struct_0(esk2_0),esk3_0),esk2_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).
% 35.33/35.53  cnf(c_0_11, plain, (v1_tops_2(k7_setfam_1(u1_struct_0(X1),k7_setfam_1(u1_struct_0(X1),X2)),X1)|~v2_tops_2(k7_setfam_1(u1_struct_0(X1),X2),X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))), inference(spm,[status(thm)],[c_0_8, c_0_9])).
% 35.33/35.53  cnf(c_0_12, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 35.33/35.53  cnf(c_0_13, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 35.33/35.53  cnf(c_0_14, plain, (v2_tops_2(X2,X1)|~v1_tops_2(k7_setfam_1(u1_struct_0(X1),X2),X1)|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 35.33/35.53  fof(c_0_15, plain, ![X5, X6, X7, X8]:(((~r2_hidden(X8,X7)|r2_hidden(k3_subset_1(X5,X8),X6)|~m1_subset_1(X8,k1_zfmisc_1(X5))|X7!=k7_setfam_1(X5,X6)|~m1_subset_1(X7,k1_zfmisc_1(k1_zfmisc_1(X5)))|~m1_subset_1(X6,k1_zfmisc_1(k1_zfmisc_1(X5))))&(~r2_hidden(k3_subset_1(X5,X8),X6)|r2_hidden(X8,X7)|~m1_subset_1(X8,k1_zfmisc_1(X5))|X7!=k7_setfam_1(X5,X6)|~m1_subset_1(X7,k1_zfmisc_1(k1_zfmisc_1(X5)))|~m1_subset_1(X6,k1_zfmisc_1(k1_zfmisc_1(X5)))))&((m1_subset_1(esk1_3(X5,X6,X7),k1_zfmisc_1(X5))|X7=k7_setfam_1(X5,X6)|~m1_subset_1(X7,k1_zfmisc_1(k1_zfmisc_1(X5)))|~m1_subset_1(X6,k1_zfmisc_1(k1_zfmisc_1(X5))))&((~r2_hidden(esk1_3(X5,X6,X7),X7)|~r2_hidden(k3_subset_1(X5,esk1_3(X5,X6,X7)),X6)|X7=k7_setfam_1(X5,X6)|~m1_subset_1(X7,k1_zfmisc_1(k1_zfmisc_1(X5)))|~m1_subset_1(X6,k1_zfmisc_1(k1_zfmisc_1(X5))))&(r2_hidden(esk1_3(X5,X6,X7),X7)|r2_hidden(k3_subset_1(X5,esk1_3(X5,X6,X7)),X6)|X7=k7_setfam_1(X5,X6)|~m1_subset_1(X7,k1_zfmisc_1(k1_zfmisc_1(X5)))|~m1_subset_1(X6,k1_zfmisc_1(k1_zfmisc_1(X5))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_setfam_1])])])])])).
% 35.33/35.53  cnf(c_0_16, negated_conjecture, (v1_tops_2(k7_setfam_1(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0)),esk2_0)|~v2_tops_2(k7_setfam_1(u1_struct_0(esk2_0),esk3_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_12]), c_0_13])])).
% 35.33/35.53  cnf(c_0_17, negated_conjecture, (v1_tops_2(esk3_0,esk2_0)|v2_tops_2(k7_setfam_1(u1_struct_0(esk2_0),esk3_0),esk2_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 35.33/35.53  cnf(c_0_18, plain, (v2_tops_2(k7_setfam_1(u1_struct_0(X1),X2),X1)|~v1_tops_2(k7_setfam_1(u1_struct_0(X1),k7_setfam_1(u1_struct_0(X1),X2)),X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))), inference(spm,[status(thm)],[c_0_14, c_0_9])).
% 35.33/35.53  cnf(c_0_19, plain, (m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(X1))|X3=k7_setfam_1(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 35.33/35.53  cnf(c_0_20, plain, (r2_hidden(esk1_3(X1,X2,X3),X3)|r2_hidden(k3_subset_1(X1,esk1_3(X1,X2,X3)),X2)|X3=k7_setfam_1(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 35.33/35.53  cnf(c_0_21, negated_conjecture, (v1_tops_2(k7_setfam_1(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0)),esk2_0)|v1_tops_2(esk3_0,esk2_0)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 35.33/35.53  cnf(c_0_22, plain, (X3=k7_setfam_1(X1,X2)|~r2_hidden(esk1_3(X1,X2,X3),X3)|~r2_hidden(k3_subset_1(X1,esk1_3(X1,X2,X3)),X2)|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 35.33/35.53  cnf(c_0_23, plain, (v2_tops_2(k7_setfam_1(u1_struct_0(X1),X2),X1)|m1_subset_1(esk1_3(u1_struct_0(X1),k7_setfam_1(u1_struct_0(X1),X2),X3),k1_zfmisc_1(u1_struct_0(X1)))|~v1_tops_2(X3,X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_9])).
% 35.33/35.53  cnf(c_0_24, plain, (v2_tops_2(k7_setfam_1(u1_struct_0(X1),X2),X1)|r2_hidden(k3_subset_1(u1_struct_0(X1),esk1_3(u1_struct_0(X1),k7_setfam_1(u1_struct_0(X1),X2),X3)),k7_setfam_1(u1_struct_0(X1),X2))|r2_hidden(esk1_3(u1_struct_0(X1),k7_setfam_1(u1_struct_0(X1),X2),X3),X3)|~v1_tops_2(X3,X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_20]), c_0_9])).
% 35.33/35.53  cnf(c_0_25, negated_conjecture, (v1_tops_2(esk3_0,esk2_0)|v1_tops_2(X1,esk2_0)|~r2_hidden(k3_subset_1(u1_struct_0(esk2_0),esk1_3(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0),X1)),k7_setfam_1(u1_struct_0(esk2_0),esk3_0))|~r2_hidden(esk1_3(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0),X1),X1)|~m1_subset_1(k7_setfam_1(u1_struct_0(esk2_0),esk3_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))))|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))))), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 35.33/35.53  fof(c_0_26, plain, ![X12, X13, X14]:((~r2_hidden(k3_subset_1(X12,X14),k7_setfam_1(X12,X13))|r2_hidden(X14,X13)|~m1_subset_1(X14,k1_zfmisc_1(X12))|~m1_subset_1(X13,k1_zfmisc_1(k1_zfmisc_1(X12))))&(~r2_hidden(X14,X13)|r2_hidden(k3_subset_1(X12,X14),k7_setfam_1(X12,X13))|~m1_subset_1(X14,k1_zfmisc_1(X12))|~m1_subset_1(X13,k1_zfmisc_1(k1_zfmisc_1(X12))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t49_setfam_1])])])])).
% 35.33/35.53  cnf(c_0_27, negated_conjecture, (v1_tops_2(esk3_0,esk2_0)|v1_tops_2(X1,esk2_0)|m1_subset_1(esk1_3(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0),X1),k1_zfmisc_1(u1_struct_0(esk2_0)))|~m1_subset_1(k7_setfam_1(u1_struct_0(esk2_0),esk3_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))))|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))))), inference(spm,[status(thm)],[c_0_21, c_0_19])).
% 35.33/35.53  cnf(c_0_28, negated_conjecture, (v2_tops_2(k7_setfam_1(u1_struct_0(esk2_0),esk3_0),esk2_0)|m1_subset_1(esk1_3(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0),X1),k1_zfmisc_1(u1_struct_0(esk2_0)))|~v1_tops_2(X1,esk2_0)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_12]), c_0_13])])).
% 35.33/35.53  cnf(c_0_29, negated_conjecture, (v2_tops_2(k7_setfam_1(u1_struct_0(esk2_0),esk3_0),esk2_0)|r2_hidden(k3_subset_1(u1_struct_0(esk2_0),esk1_3(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0),X1)),k7_setfam_1(u1_struct_0(esk2_0),esk3_0))|r2_hidden(esk1_3(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0),X1),X1)|~v1_tops_2(X1,esk2_0)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_12]), c_0_13])])).
% 35.33/35.53  cnf(c_0_30, negated_conjecture, (v1_tops_2(esk3_0,esk2_0)|v1_tops_2(X1,esk2_0)|~r2_hidden(k3_subset_1(u1_struct_0(esk2_0),esk1_3(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0),X1)),k7_setfam_1(u1_struct_0(esk2_0),esk3_0))|~r2_hidden(esk1_3(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0),X1),X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_9]), c_0_12])])).
% 35.33/35.53  cnf(c_0_31, plain, (r2_hidden(k3_subset_1(X3,X1),k7_setfam_1(X3,X2))|~r2_hidden(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X3))|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X3)))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 35.33/35.53  cnf(c_0_32, negated_conjecture, (v1_tops_2(esk3_0,esk2_0)|v1_tops_2(X1,esk2_0)|m1_subset_1(esk1_3(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0),X1),k1_zfmisc_1(u1_struct_0(esk2_0)))|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_9]), c_0_12])])).
% 35.33/35.53  cnf(c_0_33, negated_conjecture, (v1_tops_2(k7_setfam_1(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0)),esk2_0)|m1_subset_1(esk1_3(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0),X1),k1_zfmisc_1(u1_struct_0(esk2_0)))|~v1_tops_2(X1,esk2_0)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))))), inference(spm,[status(thm)],[c_0_16, c_0_28])).
% 35.33/35.53  cnf(c_0_34, negated_conjecture, (v1_tops_2(k7_setfam_1(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0)),esk2_0)|r2_hidden(k3_subset_1(u1_struct_0(esk2_0),esk1_3(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0),X1)),k7_setfam_1(u1_struct_0(esk2_0),esk3_0))|r2_hidden(esk1_3(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0),X1),X1)|~v1_tops_2(X1,esk2_0)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))))), inference(spm,[status(thm)],[c_0_16, c_0_29])).
% 35.33/35.53  cnf(c_0_35, negated_conjecture, (v1_tops_2(esk3_0,esk2_0)|v1_tops_2(X1,esk2_0)|r2_hidden(k3_subset_1(u1_struct_0(esk2_0),esk1_3(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0),X1)),k7_setfam_1(u1_struct_0(esk2_0),esk3_0))|r2_hidden(esk1_3(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0),X1),X1)|~m1_subset_1(k7_setfam_1(u1_struct_0(esk2_0),esk3_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))))|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))))), inference(spm,[status(thm)],[c_0_21, c_0_20])).
% 35.33/35.53  cnf(c_0_36, negated_conjecture, (v1_tops_2(esk3_0,esk2_0)|v1_tops_2(X1,esk2_0)|~r2_hidden(esk1_3(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0),X1),esk3_0)|~r2_hidden(esk1_3(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0),X1),X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_12])]), c_0_32])).
% 35.33/35.53  cnf(c_0_37, negated_conjecture, (v1_tops_2(k7_setfam_1(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0)),esk2_0)|m1_subset_1(esk1_3(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0),esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_12]), c_0_21])).
% 35.33/35.53  cnf(c_0_38, negated_conjecture, (v1_tops_2(k7_setfam_1(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0)),esk2_0)|r2_hidden(k3_subset_1(u1_struct_0(esk2_0),esk1_3(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0),esk3_0)),k7_setfam_1(u1_struct_0(esk2_0),esk3_0))|r2_hidden(esk1_3(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0),esk3_0),esk3_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_12]), c_0_21])).
% 35.33/35.53  cnf(c_0_39, negated_conjecture, (v1_tops_2(esk3_0,esk2_0)|v1_tops_2(X1,esk2_0)|r2_hidden(k3_subset_1(u1_struct_0(esk2_0),esk1_3(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0),X1)),k7_setfam_1(u1_struct_0(esk2_0),esk3_0))|r2_hidden(esk1_3(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0),X1),X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_9]), c_0_12])])).
% 35.33/35.53  cnf(c_0_40, negated_conjecture, (v1_tops_2(esk3_0,esk2_0)|~r2_hidden(esk1_3(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0),esk3_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(ef,[status(thm)],[c_0_36]), c_0_12])])).
% 35.33/35.53  cnf(c_0_41, negated_conjecture, (~v1_tops_2(esk3_0,esk2_0)|~v2_tops_2(k7_setfam_1(u1_struct_0(esk2_0),esk3_0),esk2_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 35.33/35.53  cnf(c_0_42, negated_conjecture, (v2_tops_2(k7_setfam_1(u1_struct_0(esk2_0),esk3_0),esk2_0)|m1_subset_1(esk1_3(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0),esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_37]), c_0_13]), c_0_12])])).
% 35.33/35.53  cnf(c_0_43, negated_conjecture, (v2_tops_2(k7_setfam_1(u1_struct_0(esk2_0),esk3_0),esk2_0)|r2_hidden(k3_subset_1(u1_struct_0(esk2_0),esk1_3(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0),esk3_0)),k7_setfam_1(u1_struct_0(esk2_0),esk3_0))|r2_hidden(esk1_3(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0),esk3_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_38]), c_0_13]), c_0_12])])).
% 35.33/35.53  cnf(c_0_44, negated_conjecture, (v1_tops_2(esk3_0,esk2_0)|r2_hidden(k3_subset_1(u1_struct_0(esk2_0),esk1_3(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0),esk3_0)),k7_setfam_1(u1_struct_0(esk2_0),esk3_0))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(ef,[status(thm)],[c_0_39]), c_0_12])]), c_0_40])).
% 35.33/35.53  cnf(c_0_45, negated_conjecture, (m1_subset_1(esk1_3(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0),esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))|~v1_tops_2(esk3_0,esk2_0)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 35.33/35.53  cnf(c_0_46, plain, (r2_hidden(X2,X3)|~r2_hidden(k3_subset_1(X1,X2),k7_setfam_1(X1,X3))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 35.33/35.53  cnf(c_0_47, negated_conjecture, (r2_hidden(k3_subset_1(u1_struct_0(esk2_0),esk1_3(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0),esk3_0)),k7_setfam_1(u1_struct_0(esk2_0),esk3_0))|r2_hidden(esk1_3(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0),esk3_0),esk3_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_43]), c_0_44])).
% 35.33/35.53  cnf(c_0_48, negated_conjecture, (m1_subset_1(esk1_3(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0),esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(ef,[status(thm)],[c_0_32]), c_0_12])]), c_0_45])).
% 35.33/35.53  cnf(c_0_49, negated_conjecture, (r2_hidden(esk1_3(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0),esk3_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_12]), c_0_48])])).
% 35.33/35.53  cnf(c_0_50, negated_conjecture, (v1_tops_2(esk3_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_49])])).
% 35.33/35.53  cnf(c_0_51, plain, (X1=X2|m1_subset_1(esk1_3(X3,X4,X2),k1_zfmisc_1(X3))|m1_subset_1(esk1_3(X3,X4,X1),k1_zfmisc_1(X3))|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X3)))|~m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X3)))|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X3)))), inference(spm,[status(thm)],[c_0_19, c_0_19])).
% 35.33/35.53  cnf(c_0_52, negated_conjecture, (v1_tops_2(X1,esk2_0)|m1_subset_1(esk1_3(X2,X3,esk3_0),k1_zfmisc_1(X2))|m1_subset_1(esk1_3(X2,X3,X1),k1_zfmisc_1(X2))|~m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(X2)))|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 35.33/35.53  cnf(c_0_53, negated_conjecture, (~v2_tops_2(k7_setfam_1(u1_struct_0(esk2_0),esk3_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_50])])).
% 35.33/35.53  cnf(c_0_54, negated_conjecture, (v2_tops_2(k7_setfam_1(u1_struct_0(esk2_0),X1),esk2_0)|m1_subset_1(esk1_3(X2,X3,k7_setfam_1(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),X1))),k1_zfmisc_1(X2))|m1_subset_1(esk1_3(X2,X3,esk3_0),k1_zfmisc_1(X2))|~m1_subset_1(k7_setfam_1(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),X1)),k1_zfmisc_1(k1_zfmisc_1(X2)))|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))))|~m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(X2)))|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_52]), c_0_13])])).
% 35.33/35.53  cnf(c_0_55, negated_conjecture, (m1_subset_1(esk1_3(X1,X2,k7_setfam_1(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0))),k1_zfmisc_1(X1))|m1_subset_1(esk1_3(X1,X2,esk3_0),k1_zfmisc_1(X1))|~m1_subset_1(k7_setfam_1(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0)),k1_zfmisc_1(k1_zfmisc_1(X1)))|~m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(X1)))|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_12])])).
% 35.33/35.53  cnf(c_0_56, negated_conjecture, (m1_subset_1(esk1_3(X1,X2,esk3_0),k1_zfmisc_1(X1))|m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))))|m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(X1))|~m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(X1)))|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(spm,[status(thm)],[c_0_12, c_0_51])).
% 35.33/35.53  cnf(c_0_57, plain, (r2_hidden(X2,X4)|~r2_hidden(k3_subset_1(X1,X2),X3)|~m1_subset_1(X2,k1_zfmisc_1(X1))|X4!=k7_setfam_1(X1,X3)|~m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X1)))|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 35.33/35.53  cnf(c_0_58, negated_conjecture, (m1_subset_1(esk1_3(X1,X2,esk3_0),k1_zfmisc_1(X1))|m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(X1))|~r2_hidden(k3_subset_1(u1_struct_0(esk2_0),esk1_3(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0),X3)),k7_setfam_1(u1_struct_0(esk2_0),esk3_0))|~r2_hidden(esk1_3(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0),X3),X3)|~m1_subset_1(k7_setfam_1(u1_struct_0(esk2_0),esk3_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))))|~m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(X1)))|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_22]), c_0_56])).
% 35.33/35.53  cnf(c_0_59, plain, (X1=X2|m1_subset_1(esk1_3(X3,X4,X1),k1_zfmisc_1(X3))|~r2_hidden(k3_subset_1(X3,esk1_3(X3,X4,X2)),X4)|~r2_hidden(esk1_3(X3,X4,X2),X2)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X3)))|~m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X3)))|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X3)))), inference(spm,[status(thm)],[c_0_19, c_0_22])).
% 35.33/35.53  cnf(c_0_60, plain, (r2_hidden(X1,k7_setfam_1(X2,X3))|~r2_hidden(k3_subset_1(X2,X1),X3)|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_57]), c_0_9])).
% 35.33/35.53  cnf(c_0_61, negated_conjecture, (m1_subset_1(esk1_3(X1,X2,esk3_0),k1_zfmisc_1(X1))|m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(X1))|~r2_hidden(k3_subset_1(u1_struct_0(esk2_0),esk1_3(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0),X3)),k7_setfam_1(u1_struct_0(esk2_0),esk3_0))|~r2_hidden(esk1_3(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0),X3),X3)|~m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(X1)))|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_9]), c_0_12])])).
% 35.33/35.53  cnf(c_0_62, negated_conjecture, (v1_tops_2(X1,esk2_0)|m1_subset_1(esk1_3(X2,X3,X1),k1_zfmisc_1(X2))|~r2_hidden(k3_subset_1(X2,esk1_3(X2,X3,esk3_0)),X3)|~r2_hidden(esk1_3(X2,X3,esk3_0),esk3_0)|~m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(X2)))|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(spm,[status(thm)],[c_0_50, c_0_59])).
% 35.33/35.53  cnf(c_0_63, plain, (r2_hidden(X1,k7_setfam_1(X2,X3))|m1_subset_1(esk1_3(X2,X3,k7_setfam_1(X4,X5)),k1_zfmisc_1(X2))|~r2_hidden(k3_subset_1(X4,X1),X5)|~m1_subset_1(k7_setfam_1(X4,X5),k1_zfmisc_1(k1_zfmisc_1(X2)))|~m1_subset_1(X5,k1_zfmisc_1(k1_zfmisc_1(X4)))|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))|~m1_subset_1(X1,k1_zfmisc_1(X4))), inference(spm,[status(thm)],[c_0_60, c_0_19])).
% 35.33/35.53  cnf(c_0_64, negated_conjecture, (m1_subset_1(esk1_3(X1,X2,esk3_0),k1_zfmisc_1(X1))|~r2_hidden(k3_subset_1(u1_struct_0(esk2_0),esk1_3(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0),esk3_0)),k7_setfam_1(u1_struct_0(esk2_0),esk3_0))|~m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(X1)))|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(ef,[status(thm)],[c_0_61]), c_0_49])])).
% 35.33/35.53  cnf(c_0_65, negated_conjecture, (v2_tops_2(k7_setfam_1(u1_struct_0(esk2_0),X1),esk2_0)|m1_subset_1(esk1_3(X2,X3,k7_setfam_1(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),X1))),k1_zfmisc_1(X2))|~r2_hidden(k3_subset_1(X2,esk1_3(X2,X3,esk3_0)),X3)|~r2_hidden(esk1_3(X2,X3,esk3_0),esk3_0)|~m1_subset_1(k7_setfam_1(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),X1)),k1_zfmisc_1(k1_zfmisc_1(X2)))|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))))|~m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(X2)))|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_62]), c_0_13])])).
% 35.33/35.53  cnf(c_0_66, plain, (r2_hidden(X1,k7_setfam_1(X2,X3))|m1_subset_1(esk1_3(X2,X3,k7_setfam_1(X2,X4)),k1_zfmisc_1(X2))|~r2_hidden(k3_subset_1(X2,X1),X4)|~m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X2)))|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_63, c_0_9])).
% 35.33/35.53  cnf(c_0_67, plain, (X1=X2|~r2_hidden(k3_subset_1(X3,esk1_3(X3,X4,X1)),X4)|~r2_hidden(k3_subset_1(X3,esk1_3(X3,X4,X2)),X4)|~r2_hidden(esk1_3(X3,X4,X1),X1)|~r2_hidden(esk1_3(X3,X4,X2),X2)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X3)))|~m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X3)))|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X3)))), inference(spm,[status(thm)],[c_0_22, c_0_22])).
% 35.33/35.53  cnf(c_0_68, negated_conjecture, (m1_subset_1(esk1_3(X1,X2,esk3_0),k1_zfmisc_1(X1))|~m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(X1)))|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_31]), c_0_49]), c_0_12]), c_0_48])])).
% 35.33/35.53  cnf(c_0_69, negated_conjecture, (m1_subset_1(esk1_3(X1,X2,k7_setfam_1(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0))),k1_zfmisc_1(X1))|~r2_hidden(k3_subset_1(X1,esk1_3(X1,X2,esk3_0)),X2)|~r2_hidden(esk1_3(X1,X2,esk3_0),esk3_0)|~m1_subset_1(k7_setfam_1(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0)),k1_zfmisc_1(k1_zfmisc_1(X1)))|~m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(X1)))|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_65]), c_0_12])])).
% 35.33/35.53  cnf(c_0_70, plain, (r2_hidden(X1,k7_setfam_1(X2,X3))|m1_subset_1(esk1_3(X2,X3,k7_setfam_1(X2,k7_setfam_1(X2,X4))),k1_zfmisc_1(X2))|~r2_hidden(k3_subset_1(X2,X1),k7_setfam_1(X2,X4))|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))|~m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X2)))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_66, c_0_9])).
% 35.33/35.53  cnf(c_0_71, negated_conjecture, (v1_tops_2(X1,esk2_0)|~r2_hidden(k3_subset_1(X2,esk1_3(X2,X3,esk3_0)),X3)|~r2_hidden(k3_subset_1(X2,esk1_3(X2,X3,X1)),X3)|~r2_hidden(esk1_3(X2,X3,esk3_0),esk3_0)|~r2_hidden(esk1_3(X2,X3,X1),X1)|~m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(X2)))|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(spm,[status(thm)],[c_0_50, c_0_67])).
% 35.33/35.53  cnf(c_0_72, negated_conjecture, (m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(X1))|m1_subset_1(esk1_3(X4,X5,X3),k1_zfmisc_1(X4))|~r2_hidden(k3_subset_1(X1,esk1_3(X1,X2,esk3_0)),X2)|~r2_hidden(esk1_3(X1,X2,esk3_0),esk3_0)|~m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(X1)))|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X4)))|~m1_subset_1(X5,k1_zfmisc_1(k1_zfmisc_1(X4)))|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(spm,[status(thm)],[c_0_68, c_0_59])).
% 35.33/35.53  cnf(c_0_73, negated_conjecture, (m1_subset_1(esk1_3(u1_struct_0(esk2_0),X1,k7_setfam_1(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0))),k1_zfmisc_1(u1_struct_0(esk2_0)))|~r2_hidden(k3_subset_1(u1_struct_0(esk2_0),esk1_3(u1_struct_0(esk2_0),X1,esk3_0)),X1)|~r2_hidden(esk1_3(u1_struct_0(esk2_0),X1,esk3_0),esk3_0)|~m1_subset_1(k7_setfam_1(u1_struct_0(esk2_0),esk3_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))))|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_9]), c_0_12])])).
% 35.33/35.53  cnf(c_0_74, plain, (r2_hidden(k3_subset_1(X3,X1),X4)|~r2_hidden(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X3))|X2!=k7_setfam_1(X3,X4)|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X3)))|~m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X3)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 35.33/35.53  cnf(c_0_75, plain, (r2_hidden(X1,k7_setfam_1(X2,X3))|m1_subset_1(esk1_3(X2,X3,k7_setfam_1(X2,k7_setfam_1(X2,X4))),k1_zfmisc_1(X2))|~r2_hidden(X1,X4)|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))|~m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X2)))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_70, c_0_31])).
% 35.33/35.53  cnf(c_0_76, negated_conjecture, (v2_tops_2(k7_setfam_1(u1_struct_0(esk2_0),X1),esk2_0)|~r2_hidden(esk1_3(X2,X3,k7_setfam_1(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),X1))),k7_setfam_1(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),X1)))|~r2_hidden(k3_subset_1(X2,esk1_3(X2,X3,k7_setfam_1(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),X1)))),X3)|~r2_hidden(k3_subset_1(X2,esk1_3(X2,X3,esk3_0)),X3)|~r2_hidden(esk1_3(X2,X3,esk3_0),esk3_0)|~m1_subset_1(k7_setfam_1(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),X1)),k1_zfmisc_1(k1_zfmisc_1(X2)))|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))))|~m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(X2)))|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_71]), c_0_13])])).
% 35.33/35.53  cnf(c_0_77, plain, (r2_hidden(X1,k7_setfam_1(X2,k7_setfam_1(X2,X3)))|~r2_hidden(k3_subset_1(X2,X1),k7_setfam_1(X2,X3))|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_60, c_0_9])).
% 35.33/35.53  cnf(c_0_78, negated_conjecture, (m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(X1))|~r2_hidden(k3_subset_1(X1,esk1_3(X1,X2,esk3_0)),X2)|~r2_hidden(esk1_3(X1,X2,esk3_0),esk3_0)|~m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(X1)))|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(ef,[status(thm)],[c_0_72])).
% 35.33/35.53  cnf(c_0_79, negated_conjecture, (m1_subset_1(esk1_3(u1_struct_0(esk2_0),X1,k7_setfam_1(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0))),k1_zfmisc_1(u1_struct_0(esk2_0)))|~r2_hidden(k3_subset_1(u1_struct_0(esk2_0),esk1_3(u1_struct_0(esk2_0),X1,esk3_0)),X1)|~r2_hidden(esk1_3(u1_struct_0(esk2_0),X1,esk3_0),esk3_0)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_9]), c_0_12])])).
% 35.33/35.53  cnf(c_0_80, plain, (r2_hidden(k3_subset_1(X1,X2),X3)|~r2_hidden(X2,k7_setfam_1(X1,X3))|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_74]), c_0_9])).
% 35.33/35.53  cnf(c_0_81, plain, (r2_hidden(X1,k7_setfam_1(X2,k7_setfam_1(X2,X3)))|m1_subset_1(esk1_3(X2,k7_setfam_1(X2,X3),k7_setfam_1(X2,k7_setfam_1(X2,X4))),k1_zfmisc_1(X2))|~r2_hidden(X1,X4)|~m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X2)))|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_75, c_0_9])).
% 35.33/35.53  cnf(c_0_82, negated_conjecture, (~r2_hidden(esk1_3(X1,X2,k7_setfam_1(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0))),k7_setfam_1(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0)))|~r2_hidden(k3_subset_1(X1,esk1_3(X1,X2,k7_setfam_1(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0)))),X2)|~r2_hidden(k3_subset_1(X1,esk1_3(X1,X2,esk3_0)),X2)|~r2_hidden(esk1_3(X1,X2,esk3_0),esk3_0)|~m1_subset_1(k7_setfam_1(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0)),k1_zfmisc_1(k1_zfmisc_1(X1)))|~m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(X1)))|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_76]), c_0_12])])).
% 35.33/35.53  cnf(c_0_83, plain, (r2_hidden(X1,k7_setfam_1(X2,k7_setfam_1(X2,X3)))|~r2_hidden(X1,X3)|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_77, c_0_31])).
% 35.33/35.53  cnf(c_0_84, negated_conjecture, (m1_subset_1(esk1_3(X1,k7_setfam_1(X1,X2),X3),k1_zfmisc_1(X1))|~r2_hidden(esk1_3(X1,k7_setfam_1(X1,X2),esk3_0),esk3_0)|~r2_hidden(esk1_3(X1,k7_setfam_1(X1,X2),esk3_0),X2)|~m1_subset_1(esk1_3(X1,k7_setfam_1(X1,X2),esk3_0),k1_zfmisc_1(X1))|~m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(X1)))|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_31]), c_0_9])).
% 35.33/35.53  cnf(c_0_85, negated_conjecture, (m1_subset_1(esk1_3(u1_struct_0(esk2_0),X1,k7_setfam_1(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0))),k1_zfmisc_1(u1_struct_0(esk2_0)))|~r2_hidden(esk1_3(u1_struct_0(esk2_0),X1,esk3_0),k7_setfam_1(u1_struct_0(esk2_0),X1))|~r2_hidden(esk1_3(u1_struct_0(esk2_0),X1,esk3_0),esk3_0)|~m1_subset_1(esk1_3(u1_struct_0(esk2_0),X1,esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))))), inference(spm,[status(thm)],[c_0_79, c_0_80])).
% 35.33/35.53  cnf(c_0_86, negated_conjecture, (r2_hidden(X1,k7_setfam_1(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),X2)))|m1_subset_1(esk1_3(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),X2),k7_setfam_1(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0))),k1_zfmisc_1(u1_struct_0(esk2_0)))|~r2_hidden(X1,esk3_0)|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(spm,[status(thm)],[c_0_81, c_0_12])).
% 35.33/35.53  cnf(c_0_87, negated_conjecture, (~r2_hidden(k3_subset_1(X1,esk1_3(X1,X2,k7_setfam_1(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0)))),X2)|~r2_hidden(esk1_3(X1,X2,k7_setfam_1(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0))),esk3_0)|~r2_hidden(k3_subset_1(X1,esk1_3(X1,X2,esk3_0)),X2)|~r2_hidden(esk1_3(X1,X2,esk3_0),esk3_0)|~m1_subset_1(esk1_3(X1,X2,k7_setfam_1(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0))),k1_zfmisc_1(u1_struct_0(esk2_0)))|~m1_subset_1(k7_setfam_1(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0)),k1_zfmisc_1(k1_zfmisc_1(X1)))|~m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(X1)))|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_83]), c_0_12])])).
% 35.33/35.53  cnf(c_0_88, negated_conjecture, (m1_subset_1(esk1_3(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0),X1),k1_zfmisc_1(u1_struct_0(esk2_0)))|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_48]), c_0_49]), c_0_12])])).
% 35.33/35.53  cnf(c_0_89, negated_conjecture, (m1_subset_1(esk1_3(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),X1),k7_setfam_1(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0))),k1_zfmisc_1(u1_struct_0(esk2_0)))|~r2_hidden(esk1_3(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),X1),esk3_0),esk3_0)|~m1_subset_1(esk1_3(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),X1),esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_86]), c_0_9])).
% 35.33/35.53  cnf(c_0_90, negated_conjecture, (~r2_hidden(k3_subset_1(u1_struct_0(esk2_0),esk1_3(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0),k7_setfam_1(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0)))),k7_setfam_1(u1_struct_0(esk2_0),esk3_0))|~r2_hidden(esk1_3(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0),k7_setfam_1(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0))),esk3_0)|~r2_hidden(k3_subset_1(u1_struct_0(esk2_0),esk1_3(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0),esk3_0)),k7_setfam_1(u1_struct_0(esk2_0),esk3_0))|~m1_subset_1(k7_setfam_1(u1_struct_0(esk2_0),esk3_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_88]), c_0_49]), c_0_12])]), c_0_9])).
% 35.33/35.53  cnf(c_0_91, negated_conjecture, (m1_subset_1(esk1_3(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0),k7_setfam_1(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0))),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_48]), c_0_49]), c_0_12])])).
% 35.33/35.53  cnf(c_0_92, negated_conjecture, (~r2_hidden(esk1_3(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0),k7_setfam_1(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0))),esk3_0)|~r2_hidden(k3_subset_1(u1_struct_0(esk2_0),esk1_3(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0),esk3_0)),k7_setfam_1(u1_struct_0(esk2_0),esk3_0))|~m1_subset_1(k7_setfam_1(u1_struct_0(esk2_0),esk3_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_31]), c_0_12]), c_0_91])])).
% 35.33/35.53  cnf(c_0_93, negated_conjecture, (~r2_hidden(k3_subset_1(u1_struct_0(esk2_0),esk1_3(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0),esk3_0)),k7_setfam_1(u1_struct_0(esk2_0),esk3_0))|~r2_hidden(k3_subset_1(u1_struct_0(esk2_0),esk1_3(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0),X1)),k7_setfam_1(u1_struct_0(esk2_0),esk3_0))|~r2_hidden(esk1_3(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0),X1),esk3_0)|~r2_hidden(esk1_3(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0),X1),X1)|~m1_subset_1(k7_setfam_1(u1_struct_0(esk2_0),esk3_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))))|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))))), inference(spm,[status(thm)],[c_0_92, c_0_22])).
% 35.33/35.53  cnf(c_0_94, negated_conjecture, (~r2_hidden(k3_subset_1(u1_struct_0(esk2_0),esk1_3(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0),X1)),k7_setfam_1(u1_struct_0(esk2_0),esk3_0))|~r2_hidden(esk1_3(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0),X1),esk3_0)|~r2_hidden(esk1_3(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0),X1),X1)|~m1_subset_1(k7_setfam_1(u1_struct_0(esk2_0),esk3_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))))|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_31]), c_0_49]), c_0_12]), c_0_48])])).
% 35.33/35.53  cnf(c_0_95, negated_conjecture, (~r2_hidden(k3_subset_1(u1_struct_0(esk2_0),esk1_3(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0),X1)),k7_setfam_1(u1_struct_0(esk2_0),esk3_0))|~r2_hidden(esk1_3(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0),X1),esk3_0)|~r2_hidden(esk1_3(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0),X1),X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_9]), c_0_12])])).
% 35.33/35.53  cnf(c_0_96, negated_conjecture, (~r2_hidden(esk1_3(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0),X1),esk3_0)|~r2_hidden(esk1_3(u1_struct_0(esk2_0),k7_setfam_1(u1_struct_0(esk2_0),esk3_0),X1),X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_31]), c_0_12])]), c_0_88])).
% 35.33/35.53  cnf(c_0_97, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_49]), c_0_49]), c_0_12])]), ['proof']).
% 35.33/35.53  # SZS output end CNFRefutation
% 35.33/35.53  # Proof object total steps             : 98
% 35.33/35.53  # Proof object clause steps            : 87
% 35.33/35.53  # Proof object formula steps           : 11
% 35.33/35.53  # Proof object conjectures             : 64
% 35.33/35.53  # Proof object clause conjectures      : 61
% 35.33/35.53  # Proof object formula conjectures     : 3
% 35.33/35.53  # Proof object initial clauses used    : 14
% 35.33/35.53  # Proof object initial formulas used   : 5
% 35.33/35.53  # Proof object generating inferences   : 69
% 35.33/35.53  # Proof object simplifying inferences  : 99
% 35.33/35.53  # Training examples: 0 positive, 0 negative
% 35.33/35.53  # Parsed axioms                        : 5
% 35.33/35.53  # Removed by relevancy pruning/SinE    : 0
% 35.33/35.53  # Initial clauses                      : 14
% 35.33/35.53  # Removed in clause preprocessing      : 0
% 35.33/35.53  # Initial clauses in saturation        : 14
% 35.33/35.53  # Processed clauses                    : 14301
% 35.33/35.53  # ...of these trivial                  : 66
% 35.33/35.53  # ...subsumed                          : 7565
% 35.33/35.53  # ...remaining for further processing  : 6670
% 35.33/35.53  # Other redundant clauses eliminated   : 2
% 35.33/35.53  # Clauses deleted for lack of memory   : 473630
% 35.33/35.53  # Backward-subsumed                    : 1627
% 35.33/35.53  # Backward-rewritten                   : 362
% 35.33/35.53  # Generated clauses                    : 1863790
% 35.33/35.53  # ...of the previous two non-trivial   : 1800456
% 35.33/35.53  # Contextual simplify-reflections      : 1131
% 35.33/35.53  # Paramodulations                      : 1862654
% 35.33/35.53  # Factorizations                       : 1134
% 35.33/35.53  # Equation resolutions                 : 2
% 35.33/35.53  # Propositional unsat checks           : 0
% 35.33/35.53  #    Propositional check models        : 0
% 35.33/35.53  #    Propositional check unsatisfiable : 0
% 35.33/35.53  #    Propositional clauses             : 0
% 35.33/35.53  #    Propositional clauses after purity: 0
% 35.33/35.53  #    Propositional unsat core size     : 0
% 35.33/35.53  #    Propositional preprocessing time  : 0.000
% 35.33/35.53  #    Propositional encoding time       : 0.000
% 35.33/35.53  #    Propositional solver time         : 0.000
% 35.33/35.53  #    Success case prop preproc time    : 0.000
% 35.33/35.53  #    Success case prop encoding time   : 0.000
% 35.33/35.53  #    Success case prop solver time     : 0.000
% 35.33/35.53  # Current number of processed clauses  : 4665
% 35.33/35.53  #    Positive orientable unit clauses  : 10
% 35.33/35.53  #    Positive unorientable unit clauses: 0
% 35.33/35.53  #    Negative unit clauses             : 1
% 35.33/35.53  #    Non-unit-clauses                  : 4654
% 35.33/35.53  # Current number of unprocessed clauses: 1018977
% 35.33/35.53  # ...number of literals in the above   : 12669842
% 35.33/35.53  # Current number of archived formulas  : 0
% 35.33/35.53  # Current number of archived clauses   : 2003
% 35.33/35.53  # Clause-clause subsumption calls (NU) : 2294818
% 35.33/35.53  # Rec. Clause-clause subsumption calls : 153431
% 35.33/35.53  # Non-unit clause-clause subsumptions  : 9957
% 35.33/35.53  # Unit Clause-clause subsumption calls : 3625
% 35.33/35.53  # Rewrite failures with RHS unbound    : 0
% 35.33/35.53  # BW rewrite match attempts            : 424
% 35.33/35.53  # BW rewrite match successes           : 8
% 35.33/35.53  # Condensation attempts                : 0
% 35.33/35.53  # Condensation successes               : 0
% 35.33/35.53  # Termbank termtop insertions          : 119691655
% 35.40/35.61  
% 35.40/35.61  # -------------------------------------------------
% 35.40/35.61  # User time                : 34.454 s
% 35.40/35.61  # System time              : 0.817 s
% 35.40/35.61  # Total time               : 35.271 s
% 35.40/35.61  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
