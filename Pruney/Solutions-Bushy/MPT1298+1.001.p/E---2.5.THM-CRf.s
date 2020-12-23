%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1298+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:04 EST 2020

% Result     : Theorem 15.54s
% Output     : CNFRefutation 15.54s
% Verified   : 
% Statistics : Number of formulae       :   81 (1874 expanded)
%              Number of clauses        :   62 ( 728 expanded)
%              Number of leaves         :    9 ( 479 expanded)
%              Depth                    :   21
%              Number of atoms          :  320 (8117 expanded)
%              Number of equality atoms :   14 ( 355 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   26 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(t16_tops_2,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
         => ( v2_tops_2(X2,X1)
          <=> v1_tops_2(k7_setfam_1(u1_struct_0(X1),X2),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_tops_2)).

fof(involutiveness_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,k3_subset_1(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(dt_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(involutiveness_k7_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => k7_setfam_1(X1,k7_setfam_1(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).

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

fof(t30_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_pre_topc(X2,X1)
          <=> v4_pre_topc(k3_subset_1(u1_struct_0(X1),X2),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_tops_1)).

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

fof(c_0_9,plain,(
    ! [X13,X14,X15,X16] :
      ( ( ~ r2_hidden(X16,X15)
        | r2_hidden(k3_subset_1(X13,X16),X14)
        | ~ m1_subset_1(X16,k1_zfmisc_1(X13))
        | X15 != k7_setfam_1(X13,X14)
        | ~ m1_subset_1(X15,k1_zfmisc_1(k1_zfmisc_1(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(k1_zfmisc_1(X13))) )
      & ( ~ r2_hidden(k3_subset_1(X13,X16),X14)
        | r2_hidden(X16,X15)
        | ~ m1_subset_1(X16,k1_zfmisc_1(X13))
        | X15 != k7_setfam_1(X13,X14)
        | ~ m1_subset_1(X15,k1_zfmisc_1(k1_zfmisc_1(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(k1_zfmisc_1(X13))) )
      & ( m1_subset_1(esk3_3(X13,X14,X15),k1_zfmisc_1(X13))
        | X15 = k7_setfam_1(X13,X14)
        | ~ m1_subset_1(X15,k1_zfmisc_1(k1_zfmisc_1(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(k1_zfmisc_1(X13))) )
      & ( ~ r2_hidden(esk3_3(X13,X14,X15),X15)
        | ~ r2_hidden(k3_subset_1(X13,esk3_3(X13,X14,X15)),X14)
        | X15 = k7_setfam_1(X13,X14)
        | ~ m1_subset_1(X15,k1_zfmisc_1(k1_zfmisc_1(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(k1_zfmisc_1(X13))) )
      & ( r2_hidden(esk3_3(X13,X14,X15),X15)
        | r2_hidden(k3_subset_1(X13,esk3_3(X13,X14,X15)),X14)
        | X15 = k7_setfam_1(X13,X14)
        | ~ m1_subset_1(X15,k1_zfmisc_1(k1_zfmisc_1(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(k1_zfmisc_1(X13))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_setfam_1])])])])])).

fof(c_0_10,plain,(
    ! [X20,X21] :
      ( ~ m1_subset_1(X21,k1_zfmisc_1(k1_zfmisc_1(X20)))
      | m1_subset_1(k7_setfam_1(X20,X21),k1_zfmisc_1(k1_zfmisc_1(X20))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_setfam_1])])).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
           => ( v2_tops_2(X2,X1)
            <=> v1_tops_2(k7_setfam_1(u1_struct_0(X1),X2),X1) ) ) ) ),
    inference(assume_negation,[status(cth)],[t16_tops_2])).

cnf(c_0_12,plain,
    ( r2_hidden(X2,X4)
    | ~ r2_hidden(k3_subset_1(X1,X2),X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | X4 != k7_setfam_1(X1,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,plain,
    ( m1_subset_1(k7_setfam_1(X2,X1),k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_14,negated_conjecture,
    ( l1_pre_topc(esk4_0)
    & m1_subset_1(esk5_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0))))
    & ( ~ v2_tops_2(esk5_0,esk4_0)
      | ~ v1_tops_2(k7_setfam_1(u1_struct_0(esk4_0),esk5_0),esk4_0) )
    & ( v2_tops_2(esk5_0,esk4_0)
      | v1_tops_2(k7_setfam_1(u1_struct_0(esk4_0),esk5_0),esk4_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).

cnf(c_0_15,plain,
    ( r2_hidden(X1,k7_setfam_1(X2,X3))
    | ~ r2_hidden(k3_subset_1(X2,X1),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_12]),c_0_13])).

cnf(c_0_16,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_17,plain,(
    ! [X22,X23] :
      ( ~ m1_subset_1(X23,k1_zfmisc_1(X22))
      | k3_subset_1(X22,k3_subset_1(X22,X23)) = X23 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).

fof(c_0_18,plain,(
    ! [X18,X19] :
      ( ~ m1_subset_1(X19,k1_zfmisc_1(X18))
      | m1_subset_1(k3_subset_1(X18,X19),k1_zfmisc_1(X18)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).

cnf(c_0_19,negated_conjecture,
    ( r2_hidden(X1,k7_setfam_1(u1_struct_0(esk4_0),esk5_0))
    | ~ r2_hidden(k3_subset_1(u1_struct_0(esk4_0),X1),esk5_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_20,plain,
    ( k3_subset_1(X2,k3_subset_1(X2,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_21,plain,
    ( m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_22,plain,(
    ! [X24,X25] :
      ( ~ m1_subset_1(X25,k1_zfmisc_1(k1_zfmisc_1(X24)))
      | k7_setfam_1(X24,k7_setfam_1(X24,X25)) = X25 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k7_setfam_1])])).

cnf(c_0_23,plain,
    ( r2_hidden(X1,k7_setfam_1(X2,k7_setfam_1(X2,X3)))
    | ~ r2_hidden(k3_subset_1(X2,X1),k7_setfam_1(X2,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_15,c_0_13])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(k3_subset_1(u1_struct_0(esk4_0),X1),k7_setfam_1(u1_struct_0(esk4_0),esk5_0))
    | ~ r2_hidden(X1,esk5_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21])).

cnf(c_0_25,plain,
    ( k7_setfam_1(X2,k7_setfam_1(X2,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(X1,k7_setfam_1(u1_struct_0(esk4_0),k7_setfam_1(u1_struct_0(esk4_0),esk5_0)))
    | ~ r2_hidden(X1,esk5_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_16])])).

fof(c_0_27,plain,(
    ! [X5,X6,X7] :
      ( ( ~ v1_tops_2(X6,X5)
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X5)))
        | ~ r2_hidden(X7,X6)
        | v3_pre_topc(X7,X5)
        | ~ m1_subset_1(X6,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X5))))
        | ~ l1_pre_topc(X5) )
      & ( m1_subset_1(esk1_2(X5,X6),k1_zfmisc_1(u1_struct_0(X5)))
        | v1_tops_2(X6,X5)
        | ~ m1_subset_1(X6,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X5))))
        | ~ l1_pre_topc(X5) )
      & ( r2_hidden(esk1_2(X5,X6),X6)
        | v1_tops_2(X6,X5)
        | ~ m1_subset_1(X6,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X5))))
        | ~ l1_pre_topc(X5) )
      & ( ~ v3_pre_topc(esk1_2(X5,X6),X5)
        | v1_tops_2(X6,X5)
        | ~ m1_subset_1(X6,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X5))))
        | ~ l1_pre_topc(X5) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tops_2])])])])])).

fof(c_0_28,plain,(
    ! [X26,X27] :
      ( ( ~ v3_pre_topc(X27,X26)
        | v4_pre_topc(k3_subset_1(u1_struct_0(X26),X27),X26)
        | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))
        | ~ l1_pre_topc(X26) )
      & ( ~ v4_pre_topc(k3_subset_1(u1_struct_0(X26),X27),X26)
        | v3_pre_topc(X27,X26)
        | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))
        | ~ l1_pre_topc(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t30_tops_1])])])])).

fof(c_0_29,plain,(
    ! [X9,X10,X11] :
      ( ( ~ v2_tops_2(X10,X9)
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X9)))
        | ~ r2_hidden(X11,X10)
        | v4_pre_topc(X11,X9)
        | ~ m1_subset_1(X10,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X9))))
        | ~ l1_pre_topc(X9) )
      & ( m1_subset_1(esk2_2(X9,X10),k1_zfmisc_1(u1_struct_0(X9)))
        | v2_tops_2(X10,X9)
        | ~ m1_subset_1(X10,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X9))))
        | ~ l1_pre_topc(X9) )
      & ( r2_hidden(esk2_2(X9,X10),X10)
        | v2_tops_2(X10,X9)
        | ~ m1_subset_1(X10,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X9))))
        | ~ l1_pre_topc(X9) )
      & ( ~ v4_pre_topc(esk2_2(X9,X10),X9)
        | v2_tops_2(X10,X9)
        | ~ m1_subset_1(X10,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X9))))
        | ~ l1_pre_topc(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tops_2])])])])])).

cnf(c_0_30,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k3_subset_1(X3,X1),k7_setfam_1(X3,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_25])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(X1,k7_setfam_1(u1_struct_0(esk4_0),k7_setfam_1(u1_struct_0(esk4_0),k7_setfam_1(u1_struct_0(esk4_0),esk5_0))))
    | ~ r2_hidden(k3_subset_1(u1_struct_0(esk4_0),X1),esk5_0)
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0(esk4_0),esk5_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_26]),c_0_21])).

cnf(c_0_32,plain,
    ( v1_tops_2(X2,X1)
    | ~ v3_pre_topc(esk1_2(X1,X2),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_33,plain,
    ( v3_pre_topc(X2,X1)
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0(X1),X2),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_34,plain,
    ( v4_pre_topc(X3,X2)
    | ~ v2_tops_2(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r2_hidden(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_35,negated_conjecture,
    ( ~ v2_tops_2(esk5_0,esk4_0)
    | ~ v1_tops_2(k7_setfam_1(u1_struct_0(esk4_0),esk5_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_36,plain,
    ( m1_subset_1(esk1_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | v1_tops_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_37,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(X1,k7_setfam_1(u1_struct_0(esk4_0),k7_setfam_1(u1_struct_0(esk4_0),esk5_0)))
    | ~ r2_hidden(k3_subset_1(u1_struct_0(esk4_0),k3_subset_1(u1_struct_0(esk4_0),X1)),esk5_0)
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0(esk4_0),esk5_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_21]),c_0_13])).

cnf(c_0_39,plain,
    ( v1_tops_2(k7_setfam_1(u1_struct_0(X1),X2),X1)
    | ~ v3_pre_topc(esk1_2(X1,k7_setfam_1(u1_struct_0(X1),X2)),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_32,c_0_13])).

cnf(c_0_40,plain,
    ( v3_pre_topc(X1,X2)
    | ~ v2_tops_2(X3,X2)
    | ~ r2_hidden(k3_subset_1(u1_struct_0(X2),X1),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_21])).

cnf(c_0_41,negated_conjecture,
    ( m1_subset_1(esk1_2(esk4_0,k7_setfam_1(u1_struct_0(esk4_0),esk5_0)),k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ v2_tops_2(esk5_0,esk4_0)
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0(esk4_0),esk5_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37])])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(X1,k7_setfam_1(u1_struct_0(esk4_0),k7_setfam_1(u1_struct_0(esk4_0),esk5_0)))
    | ~ r2_hidden(k3_subset_1(u1_struct_0(esk4_0),k3_subset_1(u1_struct_0(esk4_0),X1)),esk5_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_13]),c_0_16])])).

cnf(c_0_43,plain,
    ( r2_hidden(k3_subset_1(X3,X1),X4)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3))
    | X2 != k7_setfam_1(X3,X4)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_44,plain,
    ( r2_hidden(esk1_2(X1,X2),X2)
    | v1_tops_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_45,plain,
    ( v1_tops_2(k7_setfam_1(u1_struct_0(X1),X2),X1)
    | ~ v2_tops_2(X3,X1)
    | ~ r2_hidden(k3_subset_1(u1_struct_0(X1),esk1_2(X1,k7_setfam_1(u1_struct_0(X1),X2))),X3)
    | ~ m1_subset_1(esk1_2(X1,k7_setfam_1(u1_struct_0(X1),X2)),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_46,negated_conjecture,
    ( m1_subset_1(esk1_2(esk4_0,k7_setfam_1(u1_struct_0(esk4_0),esk5_0)),k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ v2_tops_2(esk5_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_13]),c_0_16])])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(X1,esk5_0)
    | ~ r2_hidden(k3_subset_1(u1_struct_0(esk4_0),k3_subset_1(u1_struct_0(esk4_0),X1)),esk5_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_25]),c_0_16])])).

cnf(c_0_48,plain,
    ( r2_hidden(k3_subset_1(X1,X2),X3)
    | ~ r2_hidden(X2,k7_setfam_1(X1,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_43]),c_0_13])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(esk1_2(esk4_0,k7_setfam_1(u1_struct_0(esk4_0),esk5_0)),k7_setfam_1(u1_struct_0(esk4_0),esk5_0))
    | ~ v2_tops_2(esk5_0,esk4_0)
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0(esk4_0),esk5_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_44]),c_0_37])])).

cnf(c_0_50,plain,
    ( v2_tops_2(X2,X1)
    | ~ v4_pre_topc(esk2_2(X1,X2),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_51,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(X2),X1),X2)
    | ~ v3_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_52,negated_conjecture,
    ( ~ v2_tops_2(esk5_0,esk4_0)
    | ~ v2_tops_2(X1,esk4_0)
    | ~ r2_hidden(k3_subset_1(u1_struct_0(esk4_0),esk1_2(esk4_0,k7_setfam_1(u1_struct_0(esk4_0),esk5_0))),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0)))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_45]),c_0_16]),c_0_37])]),c_0_46])).

cnf(c_0_53,plain,
    ( m1_subset_1(esk2_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_tops_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(X1,esk5_0)
    | ~ r2_hidden(k3_subset_1(u1_struct_0(esk4_0),X1),k7_setfam_1(u1_struct_0(esk4_0),esk5_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_16])]),c_0_21])).

cnf(c_0_55,negated_conjecture,
    ( r2_hidden(esk1_2(esk4_0,k7_setfam_1(u1_struct_0(esk4_0),esk5_0)),k7_setfam_1(u1_struct_0(esk4_0),esk5_0))
    | ~ v2_tops_2(esk5_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_13]),c_0_16])])).

cnf(c_0_56,negated_conjecture,
    ( v2_tops_2(esk5_0,esk4_0)
    | ~ v4_pre_topc(esk2_2(esk4_0,esk5_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_16]),c_0_37])])).

cnf(c_0_57,plain,
    ( v4_pre_topc(X1,X2)
    | ~ v3_pre_topc(k3_subset_1(u1_struct_0(X2),X1),X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_20]),c_0_21])).

cnf(c_0_58,negated_conjecture,
    ( m1_subset_1(esk2_2(esk4_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ v2_tops_2(X1,esk4_0)
    | ~ r2_hidden(k3_subset_1(u1_struct_0(esk4_0),esk1_2(esk4_0,k7_setfam_1(u1_struct_0(esk4_0),esk5_0))),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_16]),c_0_37])])).

cnf(c_0_59,negated_conjecture,
    ( r2_hidden(k3_subset_1(u1_struct_0(esk4_0),X1),esk5_0)
    | ~ r2_hidden(X1,k7_setfam_1(u1_struct_0(esk4_0),esk5_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_20]),c_0_21])).

cnf(c_0_60,negated_conjecture,
    ( m1_subset_1(esk1_2(esk4_0,k7_setfam_1(u1_struct_0(esk4_0),esk5_0)),k1_zfmisc_1(u1_struct_0(esk4_0)))
    | m1_subset_1(esk2_2(esk4_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_53]),c_0_16]),c_0_37])])).

cnf(c_0_61,negated_conjecture,
    ( r2_hidden(esk1_2(esk4_0,k7_setfam_1(u1_struct_0(esk4_0),esk5_0)),k7_setfam_1(u1_struct_0(esk4_0),esk5_0))
    | m1_subset_1(esk2_2(esk4_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_53]),c_0_16]),c_0_37])])).

cnf(c_0_62,plain,
    ( r2_hidden(esk2_2(X1,X2),X2)
    | v2_tops_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_63,negated_conjecture,
    ( v2_tops_2(esk5_0,esk4_0)
    | ~ v3_pre_topc(k3_subset_1(u1_struct_0(esk4_0),esk2_2(esk4_0,esk5_0)),esk4_0)
    | ~ m1_subset_1(esk2_2(esk4_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_37])])).

cnf(c_0_64,plain,
    ( v3_pre_topc(X3,X2)
    | ~ v1_tops_2(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r2_hidden(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_65,negated_conjecture,
    ( m1_subset_1(esk2_2(esk4_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ v2_tops_2(esk5_0,esk4_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_16])]),c_0_60]),c_0_61])).

cnf(c_0_66,negated_conjecture,
    ( r2_hidden(esk2_2(esk4_0,esk5_0),esk5_0)
    | ~ v2_tops_2(X1,esk4_0)
    | ~ r2_hidden(k3_subset_1(u1_struct_0(esk4_0),esk1_2(esk4_0,k7_setfam_1(u1_struct_0(esk4_0),esk5_0))),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_62]),c_0_16]),c_0_37])])).

cnf(c_0_67,negated_conjecture,
    ( r2_hidden(esk2_2(esk4_0,esk5_0),esk5_0)
    | m1_subset_1(esk1_2(esk4_0,k7_setfam_1(u1_struct_0(esk4_0),esk5_0)),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_62]),c_0_16]),c_0_37])])).

cnf(c_0_68,negated_conjecture,
    ( r2_hidden(esk1_2(esk4_0,k7_setfam_1(u1_struct_0(esk4_0),esk5_0)),k7_setfam_1(u1_struct_0(esk4_0),esk5_0))
    | r2_hidden(esk2_2(esk4_0,esk5_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_62]),c_0_16]),c_0_37])])).

cnf(c_0_69,negated_conjecture,
    ( v2_tops_2(esk5_0,esk4_0)
    | ~ r2_hidden(k3_subset_1(u1_struct_0(esk4_0),esk2_2(esk4_0,esk5_0)),X1)
    | ~ v1_tops_2(X1,esk4_0)
    | ~ m1_subset_1(esk2_2(esk4_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0)))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_37])]),c_0_21])).

cnf(c_0_70,negated_conjecture,
    ( m1_subset_1(esk2_2(esk4_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_53]),c_0_16]),c_0_37])])).

cnf(c_0_71,negated_conjecture,
    ( r2_hidden(esk2_2(esk4_0,esk5_0),esk5_0)
    | ~ v2_tops_2(esk5_0,esk4_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_59]),c_0_16])]),c_0_67]),c_0_68])).

cnf(c_0_72,negated_conjecture,
    ( v2_tops_2(esk5_0,esk4_0)
    | ~ r2_hidden(k3_subset_1(u1_struct_0(esk4_0),esk2_2(esk4_0,esk5_0)),X1)
    | ~ v1_tops_2(X1,esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_69,c_0_70])])).

cnf(c_0_73,negated_conjecture,
    ( r2_hidden(esk2_2(esk4_0,esk5_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_62]),c_0_16]),c_0_37])])).

cnf(c_0_74,negated_conjecture,
    ( v2_tops_2(esk5_0,esk4_0)
    | v1_tops_2(k7_setfam_1(u1_struct_0(esk4_0),esk5_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_75,negated_conjecture,
    ( v2_tops_2(esk5_0,esk4_0)
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0(esk4_0),esk5_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0)))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_24]),c_0_73]),c_0_70])]),c_0_74])).

cnf(c_0_76,negated_conjecture,
    ( ~ v2_tops_2(X1,esk4_0)
    | ~ r2_hidden(k3_subset_1(u1_struct_0(esk4_0),esk1_2(esk4_0,k7_setfam_1(u1_struct_0(esk4_0),esk5_0))),X1)
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0(esk4_0),esk5_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0)))) ),
    inference(spm,[status(thm)],[c_0_52,c_0_75])).

cnf(c_0_77,negated_conjecture,
    ( ~ v2_tops_2(X1,esk4_0)
    | ~ r2_hidden(k3_subset_1(u1_struct_0(esk4_0),esk1_2(esk4_0,k7_setfam_1(u1_struct_0(esk4_0),esk5_0))),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_13]),c_0_16])])).

cnf(c_0_78,negated_conjecture,
    ( ~ v2_tops_2(esk5_0,esk4_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_59]),c_0_16])]),c_0_46]),c_0_55])).

cnf(c_0_79,negated_conjecture,
    ( ~ m1_subset_1(k7_setfam_1(u1_struct_0(esk4_0),esk5_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0)))) ),
    inference(spm,[status(thm)],[c_0_78,c_0_75])).

cnf(c_0_80,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_13]),c_0_16])]),
    [proof]).

%------------------------------------------------------------------------------
