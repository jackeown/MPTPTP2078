%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1354+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:10 EST 2020

% Result     : Theorem 1.39s
% Output     : CNFRefutation 1.39s
% Verified   : 
% Statistics : Number of formulae       :   93 (7040 expanded)
%              Number of clauses        :   72 (2810 expanded)
%              Number of leaves         :   10 (1720 expanded)
%              Depth                    :   25
%              Number of atoms          :  312 (28870 expanded)
%              Number of equality atoms :    8 ( 385 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   26 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t79_tops_2,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
         => ( v2_tops_2(X2,X1)
          <=> r1_tarski(X2,k7_setfam_1(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_tops_2)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tops_2)).

fof(t29_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v4_pre_topc(X2,X1)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X1),X2),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tops_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(d5_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_pre_topc(X2,X1)
          <=> r2_hidden(X2,u1_pre_topc(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_pre_topc)).

fof(dt_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

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

fof(dt_k7_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => m1_subset_1(k7_setfam_1(X1,X2),k1_zfmisc_1(k1_zfmisc_1(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_setfam_1)).

fof(dt_u1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
           => ( v2_tops_2(X2,X1)
            <=> r1_tarski(X2,k7_setfam_1(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    inference(assume_negation,[status(cth)],[t79_tops_2])).

fof(c_0_11,plain,(
    ! [X5,X6,X7] :
      ( ( ~ v2_tops_2(X6,X5)
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X5)))
        | ~ r2_hidden(X7,X6)
        | v4_pre_topc(X7,X5)
        | ~ m1_subset_1(X6,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X5))))
        | ~ l1_pre_topc(X5) )
      & ( m1_subset_1(esk1_2(X5,X6),k1_zfmisc_1(u1_struct_0(X5)))
        | v2_tops_2(X6,X5)
        | ~ m1_subset_1(X6,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X5))))
        | ~ l1_pre_topc(X5) )
      & ( r2_hidden(esk1_2(X5,X6),X6)
        | v2_tops_2(X6,X5)
        | ~ m1_subset_1(X6,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X5))))
        | ~ l1_pre_topc(X5) )
      & ( ~ v4_pre_topc(esk1_2(X5,X6),X5)
        | v2_tops_2(X6,X5)
        | ~ m1_subset_1(X6,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X5))))
        | ~ l1_pre_topc(X5) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tops_2])])])])])).

fof(c_0_12,negated_conjecture,
    ( l1_pre_topc(esk4_0)
    & m1_subset_1(esk5_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0))))
    & ( ~ v2_tops_2(esk5_0,esk4_0)
      | ~ r1_tarski(esk5_0,k7_setfam_1(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))) )
    & ( v2_tops_2(esk5_0,esk4_0)
      | r1_tarski(esk5_0,k7_setfam_1(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).

cnf(c_0_13,plain,
    ( v2_tops_2(X2,X1)
    | ~ v4_pre_topc(esk1_2(X1,X2),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_14,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_15,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_16,plain,(
    ! [X27,X28] :
      ( ( ~ v4_pre_topc(X28,X27)
        | v3_pre_topc(k3_subset_1(u1_struct_0(X27),X28),X27)
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))
        | ~ l1_pre_topc(X27) )
      & ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X27),X28),X27)
        | v4_pre_topc(X28,X27)
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))
        | ~ l1_pre_topc(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_tops_1])])])])).

fof(c_0_17,plain,(
    ! [X9,X10,X11,X12,X13] :
      ( ( ~ r1_tarski(X9,X10)
        | ~ r2_hidden(X11,X9)
        | r2_hidden(X11,X10) )
      & ( r2_hidden(esk2_2(X12,X13),X12)
        | r1_tarski(X12,X13) )
      & ( ~ r2_hidden(esk2_2(X12,X13),X13)
        | r1_tarski(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_18,negated_conjecture,
    ( v2_tops_2(esk5_0,esk4_0)
    | ~ v4_pre_topc(esk1_2(esk4_0,esk5_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15])])).

cnf(c_0_19,plain,
    ( v4_pre_topc(X2,X1)
    | ~ v3_pre_topc(k3_subset_1(u1_struct_0(X1),X2),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_20,plain,(
    ! [X15,X16] :
      ( ( ~ v3_pre_topc(X16,X15)
        | r2_hidden(X16,u1_pre_topc(X15))
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
        | ~ l1_pre_topc(X15) )
      & ( ~ r2_hidden(X16,u1_pre_topc(X15))
        | v3_pre_topc(X16,X15)
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
        | ~ l1_pre_topc(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_pre_topc])])])])).

fof(c_0_21,plain,(
    ! [X22,X23] :
      ( ~ m1_subset_1(X23,k1_zfmisc_1(X22))
      | m1_subset_1(k3_subset_1(X22,X23),k1_zfmisc_1(X22)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).

cnf(c_0_22,negated_conjecture,
    ( ~ v2_tops_2(esk5_0,esk4_0)
    | ~ r1_tarski(esk5_0,k7_setfam_1(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_23,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_24,plain,(
    ! [X29,X30,X31] :
      ( ~ r2_hidden(X29,X30)
      | ~ m1_subset_1(X30,k1_zfmisc_1(X31))
      | m1_subset_1(X29,X31) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_25,negated_conjecture,
    ( v2_tops_2(esk5_0,esk4_0)
    | ~ v3_pre_topc(k3_subset_1(u1_struct_0(esk4_0),esk1_2(esk4_0,esk5_0)),esk4_0)
    | ~ m1_subset_1(esk1_2(esk4_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_15])])).

cnf(c_0_26,plain,
    ( v3_pre_topc(X1,X2)
    | ~ r2_hidden(X1,u1_pre_topc(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,plain,
    ( m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(esk2_2(esk5_0,k7_setfam_1(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),esk5_0)
    | ~ v2_tops_2(esk5_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_29,plain,
    ( m1_subset_1(esk1_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_tops_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_30,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,plain,
    ( r2_hidden(esk1_2(X1,X2),X2)
    | v2_tops_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_32,negated_conjecture,
    ( v2_tops_2(esk5_0,esk4_0)
    | ~ r2_hidden(k3_subset_1(u1_struct_0(esk4_0),esk1_2(esk4_0,esk5_0)),u1_pre_topc(esk4_0))
    | ~ m1_subset_1(esk1_2(esk4_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_15])]),c_0_27])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(esk2_2(esk5_0,k7_setfam_1(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),esk5_0)
    | m1_subset_1(esk1_2(esk4_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_14]),c_0_15])])).

fof(c_0_34,plain,(
    ! [X17,X18,X19,X20] :
      ( ( ~ r2_hidden(X20,X19)
        | r2_hidden(k3_subset_1(X17,X20),X18)
        | ~ m1_subset_1(X20,k1_zfmisc_1(X17))
        | X19 != k7_setfam_1(X17,X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(k1_zfmisc_1(X17)))
        | ~ m1_subset_1(X18,k1_zfmisc_1(k1_zfmisc_1(X17))) )
      & ( ~ r2_hidden(k3_subset_1(X17,X20),X18)
        | r2_hidden(X20,X19)
        | ~ m1_subset_1(X20,k1_zfmisc_1(X17))
        | X19 != k7_setfam_1(X17,X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(k1_zfmisc_1(X17)))
        | ~ m1_subset_1(X18,k1_zfmisc_1(k1_zfmisc_1(X17))) )
      & ( m1_subset_1(esk3_3(X17,X18,X19),k1_zfmisc_1(X17))
        | X19 = k7_setfam_1(X17,X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(k1_zfmisc_1(X17)))
        | ~ m1_subset_1(X18,k1_zfmisc_1(k1_zfmisc_1(X17))) )
      & ( ~ r2_hidden(esk3_3(X17,X18,X19),X19)
        | ~ r2_hidden(k3_subset_1(X17,esk3_3(X17,X18,X19)),X18)
        | X19 = k7_setfam_1(X17,X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(k1_zfmisc_1(X17)))
        | ~ m1_subset_1(X18,k1_zfmisc_1(k1_zfmisc_1(X17))) )
      & ( r2_hidden(esk3_3(X17,X18,X19),X19)
        | r2_hidden(k3_subset_1(X17,esk3_3(X17,X18,X19)),X18)
        | X19 = k7_setfam_1(X17,X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(k1_zfmisc_1(X17)))
        | ~ m1_subset_1(X18,k1_zfmisc_1(k1_zfmisc_1(X17))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_setfam_1])])])])])).

fof(c_0_35,plain,(
    ! [X24,X25] :
      ( ~ m1_subset_1(X25,k1_zfmisc_1(k1_zfmisc_1(X24)))
      | m1_subset_1(k7_setfam_1(X24,X25),k1_zfmisc_1(k1_zfmisc_1(X24))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_setfam_1])])).

fof(c_0_36,plain,(
    ! [X26] :
      ( ~ l1_pre_topc(X26)
      | m1_subset_1(u1_pre_topc(X26),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X26)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).

cnf(c_0_37,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_38,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_14])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(esk2_2(esk5_0,k7_setfam_1(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),esk5_0)
    | r2_hidden(esk1_2(esk4_0,esk5_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_31]),c_0_14]),c_0_15])])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(esk2_2(esk5_0,k7_setfam_1(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),esk5_0)
    | ~ r2_hidden(k3_subset_1(u1_struct_0(esk4_0),esk1_2(esk4_0,esk5_0)),u1_pre_topc(esk4_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_32]),c_0_33])).

cnf(c_0_41,plain,
    ( r2_hidden(k3_subset_1(X3,X1),X4)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3))
    | X2 != k7_setfam_1(X3,X4)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_42,plain,
    ( m1_subset_1(k7_setfam_1(X2,X1),k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_43,plain,
    ( m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_44,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r2_hidden(X3,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(spm,[status(thm)],[c_0_37,c_0_23])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(esk1_2(esk4_0,esk5_0),esk5_0)
    | m1_subset_1(esk2_2(esk5_0,k7_setfam_1(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_46,negated_conjecture,
    ( m1_subset_1(esk2_2(esk5_0,k7_setfam_1(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ r2_hidden(k3_subset_1(u1_struct_0(esk4_0),esk1_2(esk4_0,esk5_0)),u1_pre_topc(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_40])).

cnf(c_0_47,plain,
    ( r2_hidden(k3_subset_1(X1,X2),X3)
    | ~ r2_hidden(X2,k7_setfam_1(X1,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_41,c_0_30])]),c_0_42])).

cnf(c_0_48,negated_conjecture,
    ( m1_subset_1(u1_pre_topc(esk4_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0)))) ),
    inference(spm,[status(thm)],[c_0_43,c_0_15])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(esk1_2(esk4_0,esk5_0),X1)
    | r2_hidden(esk2_2(esk5_0,X1),esk5_0)
    | m1_subset_1(esk2_2(esk5_0,k7_setfam_1(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_50,negated_conjecture,
    ( m1_subset_1(esk2_2(esk5_0,k7_setfam_1(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ r2_hidden(esk1_2(esk4_0,esk5_0),k7_setfam_1(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_48])])).

cnf(c_0_51,negated_conjecture,
    ( r2_hidden(esk1_2(esk4_0,esk5_0),X1)
    | m1_subset_1(esk2_2(esk5_0,k7_setfam_1(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),k1_zfmisc_1(u1_struct_0(esk4_0)))
    | m1_subset_1(esk2_2(esk5_0,X1),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_38,c_0_49])).

cnf(c_0_52,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(X2),X1),X2)
    | ~ v4_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_53,negated_conjecture,
    ( m1_subset_1(esk2_2(esk5_0,k7_setfam_1(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_54,plain,
    ( v4_pre_topc(X3,X2)
    | ~ v2_tops_2(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r2_hidden(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_55,plain,
    ( r2_hidden(X1,u1_pre_topc(X2))
    | ~ v3_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_56,negated_conjecture,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(esk4_0),esk2_2(esk5_0,k7_setfam_1(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))),esk4_0)
    | ~ v4_pre_topc(esk2_2(esk5_0,k7_setfam_1(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_15])])).

cnf(c_0_57,plain,
    ( v4_pre_topc(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ v2_tops_2(X3,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[c_0_54,c_0_30])).

cnf(c_0_58,plain,
    ( r2_hidden(k3_subset_1(u1_struct_0(X1),X2),u1_pre_topc(X1))
    | ~ v3_pre_topc(k3_subset_1(u1_struct_0(X1),X2),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_55,c_0_27])).

cnf(c_0_59,negated_conjecture,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(esk4_0),esk2_2(esk5_0,k7_setfam_1(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))),esk4_0)
    | ~ r2_hidden(esk2_2(esk5_0,k7_setfam_1(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),X1)
    | ~ v2_tops_2(X1,esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_15])])).

cnf(c_0_60,plain,
    ( r2_hidden(X2,X4)
    | ~ r2_hidden(k3_subset_1(X1,X2),X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | X4 != k7_setfam_1(X1,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_61,negated_conjecture,
    ( r2_hidden(k3_subset_1(u1_struct_0(esk4_0),esk2_2(esk5_0,k7_setfam_1(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))),u1_pre_topc(esk4_0))
    | ~ r2_hidden(esk2_2(esk5_0,k7_setfam_1(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),X1)
    | ~ v2_tops_2(X1,esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_53]),c_0_15])])).

cnf(c_0_62,plain,
    ( r2_hidden(X1,k7_setfam_1(X2,X3))
    | ~ r2_hidden(k3_subset_1(X2,X1),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_60]),c_0_42])).

cnf(c_0_63,negated_conjecture,
    ( r2_hidden(k3_subset_1(u1_struct_0(esk4_0),esk2_2(esk5_0,k7_setfam_1(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))),u1_pre_topc(esk4_0))
    | r2_hidden(esk1_2(esk4_0,esk5_0),esk5_0)
    | ~ v2_tops_2(esk5_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_39]),c_0_14])])).

cnf(c_0_64,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk2_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_65,negated_conjecture,
    ( r2_hidden(X1,k7_setfam_1(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))
    | ~ r2_hidden(k3_subset_1(u1_struct_0(esk4_0),X1),u1_pre_topc(esk4_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_62,c_0_48])).

cnf(c_0_66,negated_conjecture,
    ( r2_hidden(k3_subset_1(u1_struct_0(esk4_0),esk2_2(esk5_0,k7_setfam_1(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))),u1_pre_topc(esk4_0))
    | r2_hidden(esk1_2(esk4_0,esk5_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_31]),c_0_14]),c_0_15])])).

cnf(c_0_67,negated_conjecture,
    ( r2_hidden(k3_subset_1(u1_struct_0(esk4_0),esk2_2(esk5_0,k7_setfam_1(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))),u1_pre_topc(esk4_0))
    | m1_subset_1(esk1_2(esk4_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ v2_tops_2(esk5_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_33]),c_0_14])])).

cnf(c_0_68,negated_conjecture,
    ( ~ r2_hidden(esk2_2(esk5_0,k7_setfam_1(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),k7_setfam_1(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))
    | ~ v2_tops_2(esk5_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_64])).

cnf(c_0_69,negated_conjecture,
    ( r2_hidden(esk2_2(esk5_0,k7_setfam_1(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),k7_setfam_1(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))
    | r2_hidden(esk1_2(esk4_0,esk5_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_53])])).

cnf(c_0_70,negated_conjecture,
    ( r2_hidden(k3_subset_1(u1_struct_0(esk4_0),esk2_2(esk5_0,k7_setfam_1(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))),u1_pre_topc(esk4_0))
    | m1_subset_1(esk1_2(esk4_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_29]),c_0_14]),c_0_15])])).

cnf(c_0_71,negated_conjecture,
    ( r2_hidden(esk1_2(esk4_0,esk5_0),esk5_0)
    | ~ v2_tops_2(esk5_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_72,negated_conjecture,
    ( r2_hidden(esk2_2(esk5_0,k7_setfam_1(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),k7_setfam_1(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))
    | m1_subset_1(esk1_2(esk4_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_70]),c_0_53])])).

cnf(c_0_73,negated_conjecture,
    ( r2_hidden(esk1_2(esk4_0,esk5_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_31]),c_0_14]),c_0_15])])).

cnf(c_0_74,negated_conjecture,
    ( r2_hidden(k3_subset_1(u1_struct_0(esk4_0),esk2_2(esk5_0,k7_setfam_1(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))),u1_pre_topc(esk4_0))
    | ~ r2_hidden(k3_subset_1(u1_struct_0(esk4_0),esk1_2(esk4_0,esk5_0)),u1_pre_topc(esk4_0))
    | ~ v2_tops_2(esk5_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_40]),c_0_14])])).

cnf(c_0_75,negated_conjecture,
    ( m1_subset_1(esk1_2(esk4_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ v2_tops_2(esk5_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_68,c_0_72])).

cnf(c_0_76,negated_conjecture,
    ( r2_hidden(esk1_2(esk4_0,esk5_0),X1)
    | r2_hidden(esk2_2(esk5_0,X1),esk5_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_73])).

cnf(c_0_77,negated_conjecture,
    ( r2_hidden(k3_subset_1(u1_struct_0(esk4_0),esk2_2(esk5_0,k7_setfam_1(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))),u1_pre_topc(esk4_0))
    | ~ r2_hidden(esk1_2(esk4_0,esk5_0),k7_setfam_1(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))
    | ~ v2_tops_2(esk5_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_47]),c_0_48])])).

cnf(c_0_78,negated_conjecture,
    ( m1_subset_1(esk1_2(esk4_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_29]),c_0_14]),c_0_15])])).

cnf(c_0_79,negated_conjecture,
    ( r2_hidden(k3_subset_1(u1_struct_0(esk4_0),esk2_2(esk5_0,k7_setfam_1(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))),u1_pre_topc(esk4_0))
    | ~ v2_tops_2(esk5_0,esk4_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_76]),c_0_14])]),c_0_77])).

cnf(c_0_80,negated_conjecture,
    ( v2_tops_2(esk5_0,esk4_0)
    | ~ r2_hidden(k3_subset_1(u1_struct_0(esk4_0),esk1_2(esk4_0,esk5_0)),u1_pre_topc(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_78])])).

cnf(c_0_81,negated_conjecture,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(esk4_0),esk1_2(esk4_0,esk5_0)),esk4_0)
    | ~ v4_pre_topc(esk1_2(esk4_0,esk5_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_78]),c_0_15])])).

cnf(c_0_82,negated_conjecture,
    ( r2_hidden(k3_subset_1(u1_struct_0(esk4_0),esk2_2(esk5_0,k7_setfam_1(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))),u1_pre_topc(esk4_0))
    | ~ r2_hidden(k3_subset_1(u1_struct_0(esk4_0),esk1_2(esk4_0,esk5_0)),u1_pre_topc(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_79,c_0_80])).

cnf(c_0_83,negated_conjecture,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(esk4_0),esk1_2(esk4_0,esk5_0)),esk4_0)
    | ~ r2_hidden(esk1_2(esk4_0,esk5_0),X1)
    | ~ v2_tops_2(X1,esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_57]),c_0_15])])).

cnf(c_0_84,negated_conjecture,
    ( r2_hidden(esk2_2(esk5_0,k7_setfam_1(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),k7_setfam_1(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))
    | ~ r2_hidden(k3_subset_1(u1_struct_0(esk4_0),esk1_2(esk4_0,esk5_0)),u1_pre_topc(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_82]),c_0_53])])).

cnf(c_0_85,negated_conjecture,
    ( r2_hidden(k3_subset_1(u1_struct_0(esk4_0),esk1_2(esk4_0,esk5_0)),u1_pre_topc(esk4_0))
    | ~ r2_hidden(esk1_2(esk4_0,esk5_0),X1)
    | ~ v2_tops_2(X1,esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_83]),c_0_78]),c_0_15])])).

cnf(c_0_86,negated_conjecture,
    ( v2_tops_2(esk5_0,esk4_0)
    | r1_tarski(esk5_0,k7_setfam_1(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_87,negated_conjecture,
    ( ~ r2_hidden(k3_subset_1(u1_struct_0(esk4_0),esk1_2(esk4_0,esk5_0)),u1_pre_topc(esk4_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_84]),c_0_80])).

cnf(c_0_88,negated_conjecture,
    ( r2_hidden(k3_subset_1(u1_struct_0(esk4_0),esk1_2(esk4_0,esk5_0)),u1_pre_topc(esk4_0))
    | ~ v2_tops_2(esk5_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_14]),c_0_73])])).

cnf(c_0_89,negated_conjecture,
    ( r2_hidden(X1,k7_setfam_1(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))
    | v2_tops_2(esk5_0,esk4_0)
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_86])).

cnf(c_0_90,negated_conjecture,
    ( ~ r2_hidden(esk1_2(esk4_0,esk5_0),k7_setfam_1(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_47]),c_0_48])])).

cnf(c_0_91,negated_conjecture,
    ( r2_hidden(X1,k7_setfam_1(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))
    | ~ r2_hidden(X1,esk5_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_89]),c_0_87])).

cnf(c_0_92,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_91]),c_0_73])]),
    [proof]).

%------------------------------------------------------------------------------
