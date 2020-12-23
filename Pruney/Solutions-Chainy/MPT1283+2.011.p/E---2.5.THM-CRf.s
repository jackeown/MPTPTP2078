%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:12:38 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 444 expanded)
%              Number of clauses        :   33 ( 155 expanded)
%              Number of leaves         :    8 ( 109 expanded)
%              Depth                    :   11
%              Number of atoms          :  166 (2131 expanded)
%              Number of equality atoms :   39 ( 145 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    9 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t105_tops_1,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( ( v3_pre_topc(X2,X1)
              & v4_pre_topc(X2,X1) )
           => ( v5_tops_1(X2,X1)
            <=> v6_tops_1(X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_tops_1)).

fof(t30_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_pre_topc(X2,X1)
          <=> v4_pre_topc(k3_subset_1(u1_struct_0(X1),X2),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_tops_1)).

fof(t52_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( ( v4_pre_topc(X2,X1)
             => k2_pre_topc(X1,X2) = X2 )
            & ( ( v2_pre_topc(X1)
                & k2_pre_topc(X1,X2) = X2 )
             => v4_pre_topc(X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).

fof(t101_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v6_tops_1(X2,X1)
          <=> v5_tops_1(k3_subset_1(u1_struct_0(X1),X2),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t101_tops_1)).

fof(d8_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v6_tops_1(X2,X1)
          <=> X2 = k1_tops_1(X1,k2_pre_topc(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_tops_1)).

fof(involutiveness_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,k3_subset_1(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(dt_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(d7_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v5_tops_1(X2,X1)
          <=> X2 = k2_pre_topc(X1,k1_tops_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tops_1)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( ( v3_pre_topc(X2,X1)
                & v4_pre_topc(X2,X1) )
             => ( v5_tops_1(X2,X1)
              <=> v6_tops_1(X2,X1) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t105_tops_1])).

fof(c_0_9,plain,(
    ! [X15,X16] :
      ( ( ~ v3_pre_topc(X16,X15)
        | v4_pre_topc(k3_subset_1(u1_struct_0(X15),X16),X15)
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
        | ~ l1_pre_topc(X15) )
      & ( ~ v4_pre_topc(k3_subset_1(u1_struct_0(X15),X16),X15)
        | v3_pre_topc(X16,X15)
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
        | ~ l1_pre_topc(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t30_tops_1])])])])).

fof(c_0_10,negated_conjecture,
    ( l1_pre_topc(esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & v3_pre_topc(esk2_0,esk1_0)
    & v4_pre_topc(esk2_0,esk1_0)
    & ( ~ v5_tops_1(esk2_0,esk1_0)
      | ~ v6_tops_1(esk2_0,esk1_0) )
    & ( v5_tops_1(esk2_0,esk1_0)
      | v6_tops_1(esk2_0,esk1_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).

fof(c_0_11,plain,(
    ! [X7,X8] :
      ( ( ~ v4_pre_topc(X8,X7)
        | k2_pre_topc(X7,X8) = X8
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X7)))
        | ~ l1_pre_topc(X7) )
      & ( ~ v2_pre_topc(X7)
        | k2_pre_topc(X7,X8) != X8
        | v4_pre_topc(X8,X7)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X7)))
        | ~ l1_pre_topc(X7) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t52_pre_topc])])])])).

cnf(c_0_12,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(X2),X1),X2)
    | ~ v3_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,negated_conjecture,
    ( v3_pre_topc(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_16,plain,(
    ! [X13,X14] :
      ( ( ~ v6_tops_1(X14,X13)
        | v5_tops_1(k3_subset_1(u1_struct_0(X13),X14),X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ l1_pre_topc(X13) )
      & ( ~ v5_tops_1(k3_subset_1(u1_struct_0(X13),X14),X13)
        | v6_tops_1(X14,X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ l1_pre_topc(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t101_tops_1])])])])).

fof(c_0_17,plain,(
    ! [X11,X12] :
      ( ( ~ v6_tops_1(X12,X11)
        | X12 = k1_tops_1(X11,k2_pre_topc(X11,X12))
        | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X11)))
        | ~ l1_pre_topc(X11) )
      & ( X12 != k1_tops_1(X11,k2_pre_topc(X11,X12))
        | v6_tops_1(X12,X11)
        | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X11)))
        | ~ l1_pre_topc(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_tops_1])])])])).

fof(c_0_18,plain,(
    ! [X5,X6] :
      ( ~ m1_subset_1(X6,k1_zfmisc_1(X5))
      | k3_subset_1(X5,k3_subset_1(X5,X6)) = X6 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).

cnf(c_0_19,plain,
    ( k2_pre_topc(X2,X1) = X1
    | ~ v4_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_20,negated_conjecture,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(esk1_0),esk2_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_14]),c_0_15])])).

fof(c_0_21,plain,(
    ! [X3,X4] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(X3))
      | m1_subset_1(k3_subset_1(X3,X4),k1_zfmisc_1(X3)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).

cnf(c_0_22,negated_conjecture,
    ( ~ v5_tops_1(esk2_0,esk1_0)
    | ~ v6_tops_1(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_23,plain,
    ( v6_tops_1(X2,X1)
    | ~ v5_tops_1(k3_subset_1(u1_struct_0(X1),X2),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_24,plain,(
    ! [X9,X10] :
      ( ( ~ v5_tops_1(X10,X9)
        | X10 = k2_pre_topc(X9,k1_tops_1(X9,X10))
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9)))
        | ~ l1_pre_topc(X9) )
      & ( X10 != k2_pre_topc(X9,k1_tops_1(X9,X10))
        | v5_tops_1(X10,X9)
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9)))
        | ~ l1_pre_topc(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_tops_1])])])])).

cnf(c_0_25,negated_conjecture,
    ( v4_pre_topc(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_26,plain,
    ( X1 = k1_tops_1(X2,k2_pre_topc(X2,X1))
    | ~ v6_tops_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_27,plain,
    ( k3_subset_1(X2,k3_subset_1(X2,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_28,negated_conjecture,
    ( k2_pre_topc(esk1_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0)) = k3_subset_1(u1_struct_0(esk1_0),esk2_0)
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_14])])).

cnf(c_0_29,plain,
    ( m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_30,negated_conjecture,
    ( ~ v5_tops_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),esk1_0)
    | ~ v5_tops_1(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_14]),c_0_15])])).

cnf(c_0_31,plain,
    ( v5_tops_1(X1,X2)
    | X1 != k2_pre_topc(X2,k1_tops_1(X2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_32,negated_conjecture,
    ( v5_tops_1(esk2_0,esk1_0)
    | v6_tops_1(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_33,negated_conjecture,
    ( k2_pre_topc(esk1_0,esk2_0) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_25]),c_0_14]),c_0_15])])).

cnf(c_0_34,plain,
    ( k1_tops_1(X1,k2_pre_topc(X1,X2)) = X2
    | ~ v5_tops_1(k3_subset_1(u1_struct_0(X1),X2),X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_26,c_0_23])).

cnf(c_0_35,negated_conjecture,
    ( k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)) = esk2_0 ),
    inference(spm,[status(thm)],[c_0_27,c_0_15])).

cnf(c_0_36,negated_conjecture,
    ( k2_pre_topc(esk1_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0)) = k3_subset_1(u1_struct_0(esk1_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_15])])).

cnf(c_0_37,plain,
    ( v6_tops_1(X1,X2)
    | X1 != k1_tops_1(X2,k2_pre_topc(X2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_38,negated_conjecture,
    ( k2_pre_topc(esk1_0,k1_tops_1(esk1_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0))) != k3_subset_1(u1_struct_0(esk1_0),esk2_0)
    | ~ v5_tops_1(esk2_0,esk1_0)
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_14])])).

cnf(c_0_39,negated_conjecture,
    ( k1_tops_1(esk1_0,esk2_0) = esk2_0
    | v5_tops_1(esk2_0,esk1_0) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_32]),c_0_14]),c_0_15])]),c_0_33])).

cnf(c_0_40,negated_conjecture,
    ( k1_tops_1(esk1_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0)) = k3_subset_1(u1_struct_0(esk1_0),esk2_0)
    | ~ v5_tops_1(esk2_0,esk1_0)
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36]),c_0_14])])).

cnf(c_0_41,negated_conjecture,
    ( k1_tops_1(esk1_0,k2_pre_topc(esk1_0,esk2_0)) != esk2_0
    | ~ v5_tops_1(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_37]),c_0_14]),c_0_15])])).

cnf(c_0_42,negated_conjecture,
    ( k1_tops_1(esk1_0,esk2_0) = esk2_0
    | k2_pre_topc(esk1_0,k1_tops_1(esk1_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0))) != k3_subset_1(u1_struct_0(esk1_0),esk2_0)
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_43,negated_conjecture,
    ( k1_tops_1(esk1_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0)) = k3_subset_1(u1_struct_0(esk1_0),esk2_0)
    | k1_tops_1(esk1_0,esk2_0) = esk2_0
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_40,c_0_39])).

cnf(c_0_44,negated_conjecture,
    ( k1_tops_1(esk1_0,k2_pre_topc(esk1_0,esk2_0)) != esk2_0
    | k2_pre_topc(esk1_0,k1_tops_1(esk1_0,esk2_0)) != esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_31]),c_0_14]),c_0_15])])).

cnf(c_0_45,negated_conjecture,
    ( k1_tops_1(esk1_0,esk2_0) = esk2_0
    | k2_pre_topc(esk1_0,k1_tops_1(esk1_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0))) != k3_subset_1(u1_struct_0(esk1_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_29]),c_0_15])])).

cnf(c_0_46,negated_conjecture,
    ( k1_tops_1(esk1_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0)) = k3_subset_1(u1_struct_0(esk1_0),esk2_0)
    | k1_tops_1(esk1_0,esk2_0) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_29]),c_0_15])])).

cnf(c_0_47,negated_conjecture,
    ( k2_pre_topc(esk1_0,k1_tops_1(esk1_0,esk2_0)) != esk2_0
    | k1_tops_1(esk1_0,esk2_0) != esk2_0 ),
    inference(rw,[status(thm)],[c_0_44,c_0_33])).

cnf(c_0_48,negated_conjecture,
    ( k1_tops_1(esk1_0,esk2_0) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_36])])).

cnf(c_0_49,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_48]),c_0_33]),c_0_48])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:55:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.37  # AutoSched0-Mode selected heuristic G_E___107_B42_F1_PI_SE_Q4_CS_SP_PS_S0Y
% 0.19/0.37  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.19/0.37  #
% 0.19/0.37  # Preprocessing time       : 0.028 s
% 0.19/0.37  # Presaturation interreduction done
% 0.19/0.37  
% 0.19/0.37  # Proof found!
% 0.19/0.37  # SZS status Theorem
% 0.19/0.37  # SZS output start CNFRefutation
% 0.19/0.37  fof(t105_tops_1, conjecture, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>((v3_pre_topc(X2,X1)&v4_pre_topc(X2,X1))=>(v5_tops_1(X2,X1)<=>v6_tops_1(X2,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t105_tops_1)).
% 0.19/0.37  fof(t30_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>v4_pre_topc(k3_subset_1(u1_struct_0(X1),X2),X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_tops_1)).
% 0.19/0.37  fof(t52_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>((v4_pre_topc(X2,X1)=>k2_pre_topc(X1,X2)=X2)&((v2_pre_topc(X1)&k2_pre_topc(X1,X2)=X2)=>v4_pre_topc(X2,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 0.19/0.37  fof(t101_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v6_tops_1(X2,X1)<=>v5_tops_1(k3_subset_1(u1_struct_0(X1),X2),X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t101_tops_1)).
% 0.19/0.37  fof(d8_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v6_tops_1(X2,X1)<=>X2=k1_tops_1(X1,k2_pre_topc(X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_tops_1)).
% 0.19/0.37  fof(involutiveness_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,k3_subset_1(X1,X2))=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 0.19/0.37  fof(dt_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 0.19/0.37  fof(d7_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v5_tops_1(X2,X1)<=>X2=k2_pre_topc(X1,k1_tops_1(X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_tops_1)).
% 0.19/0.37  fof(c_0_8, negated_conjecture, ~(![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>((v3_pre_topc(X2,X1)&v4_pre_topc(X2,X1))=>(v5_tops_1(X2,X1)<=>v6_tops_1(X2,X1)))))), inference(assume_negation,[status(cth)],[t105_tops_1])).
% 0.19/0.37  fof(c_0_9, plain, ![X15, X16]:((~v3_pre_topc(X16,X15)|v4_pre_topc(k3_subset_1(u1_struct_0(X15),X16),X15)|~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))|~l1_pre_topc(X15))&(~v4_pre_topc(k3_subset_1(u1_struct_0(X15),X16),X15)|v3_pre_topc(X16,X15)|~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))|~l1_pre_topc(X15))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t30_tops_1])])])])).
% 0.19/0.37  fof(c_0_10, negated_conjecture, (l1_pre_topc(esk1_0)&(m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&((v3_pre_topc(esk2_0,esk1_0)&v4_pre_topc(esk2_0,esk1_0))&((~v5_tops_1(esk2_0,esk1_0)|~v6_tops_1(esk2_0,esk1_0))&(v5_tops_1(esk2_0,esk1_0)|v6_tops_1(esk2_0,esk1_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).
% 0.19/0.37  fof(c_0_11, plain, ![X7, X8]:((~v4_pre_topc(X8,X7)|k2_pre_topc(X7,X8)=X8|~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X7)))|~l1_pre_topc(X7))&(~v2_pre_topc(X7)|k2_pre_topc(X7,X8)!=X8|v4_pre_topc(X8,X7)|~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X7)))|~l1_pre_topc(X7))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t52_pre_topc])])])])).
% 0.19/0.37  cnf(c_0_12, plain, (v4_pre_topc(k3_subset_1(u1_struct_0(X2),X1),X2)|~v3_pre_topc(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.37  cnf(c_0_13, negated_conjecture, (v3_pre_topc(esk2_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.37  cnf(c_0_14, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.37  cnf(c_0_15, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.37  fof(c_0_16, plain, ![X13, X14]:((~v6_tops_1(X14,X13)|v5_tops_1(k3_subset_1(u1_struct_0(X13),X14),X13)|~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))|~l1_pre_topc(X13))&(~v5_tops_1(k3_subset_1(u1_struct_0(X13),X14),X13)|v6_tops_1(X14,X13)|~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))|~l1_pre_topc(X13))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t101_tops_1])])])])).
% 0.19/0.37  fof(c_0_17, plain, ![X11, X12]:((~v6_tops_1(X12,X11)|X12=k1_tops_1(X11,k2_pre_topc(X11,X12))|~m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X11)))|~l1_pre_topc(X11))&(X12!=k1_tops_1(X11,k2_pre_topc(X11,X12))|v6_tops_1(X12,X11)|~m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X11)))|~l1_pre_topc(X11))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_tops_1])])])])).
% 0.19/0.37  fof(c_0_18, plain, ![X5, X6]:(~m1_subset_1(X6,k1_zfmisc_1(X5))|k3_subset_1(X5,k3_subset_1(X5,X6))=X6), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).
% 0.19/0.37  cnf(c_0_19, plain, (k2_pre_topc(X2,X1)=X1|~v4_pre_topc(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.37  cnf(c_0_20, negated_conjecture, (v4_pre_topc(k3_subset_1(u1_struct_0(esk1_0),esk2_0),esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_13]), c_0_14]), c_0_15])])).
% 0.19/0.37  fof(c_0_21, plain, ![X3, X4]:(~m1_subset_1(X4,k1_zfmisc_1(X3))|m1_subset_1(k3_subset_1(X3,X4),k1_zfmisc_1(X3))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).
% 0.19/0.37  cnf(c_0_22, negated_conjecture, (~v5_tops_1(esk2_0,esk1_0)|~v6_tops_1(esk2_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.37  cnf(c_0_23, plain, (v6_tops_1(X2,X1)|~v5_tops_1(k3_subset_1(u1_struct_0(X1),X2),X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.37  fof(c_0_24, plain, ![X9, X10]:((~v5_tops_1(X10,X9)|X10=k2_pre_topc(X9,k1_tops_1(X9,X10))|~m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9)))|~l1_pre_topc(X9))&(X10!=k2_pre_topc(X9,k1_tops_1(X9,X10))|v5_tops_1(X10,X9)|~m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9)))|~l1_pre_topc(X9))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_tops_1])])])])).
% 0.19/0.37  cnf(c_0_25, negated_conjecture, (v4_pre_topc(esk2_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.37  cnf(c_0_26, plain, (X1=k1_tops_1(X2,k2_pre_topc(X2,X1))|~v6_tops_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.37  cnf(c_0_27, plain, (k3_subset_1(X2,k3_subset_1(X2,X1))=X1|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.37  cnf(c_0_28, negated_conjecture, (k2_pre_topc(esk1_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0))=k3_subset_1(u1_struct_0(esk1_0),esk2_0)|~m1_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_14])])).
% 0.19/0.37  cnf(c_0_29, plain, (m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.37  cnf(c_0_30, negated_conjecture, (~v5_tops_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),esk1_0)|~v5_tops_1(esk2_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_14]), c_0_15])])).
% 0.19/0.37  cnf(c_0_31, plain, (v5_tops_1(X1,X2)|X1!=k2_pre_topc(X2,k1_tops_1(X2,X1))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.37  cnf(c_0_32, negated_conjecture, (v5_tops_1(esk2_0,esk1_0)|v6_tops_1(esk2_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.37  cnf(c_0_33, negated_conjecture, (k2_pre_topc(esk1_0,esk2_0)=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_25]), c_0_14]), c_0_15])])).
% 0.19/0.37  cnf(c_0_34, plain, (k1_tops_1(X1,k2_pre_topc(X1,X2))=X2|~v5_tops_1(k3_subset_1(u1_struct_0(X1),X2),X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_26, c_0_23])).
% 0.19/0.37  cnf(c_0_35, negated_conjecture, (k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0))=esk2_0), inference(spm,[status(thm)],[c_0_27, c_0_15])).
% 0.19/0.37  cnf(c_0_36, negated_conjecture, (k2_pre_topc(esk1_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0))=k3_subset_1(u1_struct_0(esk1_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_15])])).
% 0.19/0.37  cnf(c_0_37, plain, (v6_tops_1(X1,X2)|X1!=k1_tops_1(X2,k2_pre_topc(X2,X1))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.37  cnf(c_0_38, negated_conjecture, (k2_pre_topc(esk1_0,k1_tops_1(esk1_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0)))!=k3_subset_1(u1_struct_0(esk1_0),esk2_0)|~v5_tops_1(esk2_0,esk1_0)|~m1_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_14])])).
% 0.19/0.37  cnf(c_0_39, negated_conjecture, (k1_tops_1(esk1_0,esk2_0)=esk2_0|v5_tops_1(esk2_0,esk1_0)), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_32]), c_0_14]), c_0_15])]), c_0_33])).
% 0.19/0.37  cnf(c_0_40, negated_conjecture, (k1_tops_1(esk1_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0))=k3_subset_1(u1_struct_0(esk1_0),esk2_0)|~v5_tops_1(esk2_0,esk1_0)|~m1_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_36]), c_0_14])])).
% 0.19/0.37  cnf(c_0_41, negated_conjecture, (k1_tops_1(esk1_0,k2_pre_topc(esk1_0,esk2_0))!=esk2_0|~v5_tops_1(esk2_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_37]), c_0_14]), c_0_15])])).
% 0.19/0.37  cnf(c_0_42, negated_conjecture, (k1_tops_1(esk1_0,esk2_0)=esk2_0|k2_pre_topc(esk1_0,k1_tops_1(esk1_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0)))!=k3_subset_1(u1_struct_0(esk1_0),esk2_0)|~m1_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.19/0.37  cnf(c_0_43, negated_conjecture, (k1_tops_1(esk1_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0))=k3_subset_1(u1_struct_0(esk1_0),esk2_0)|k1_tops_1(esk1_0,esk2_0)=esk2_0|~m1_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_40, c_0_39])).
% 0.19/0.37  cnf(c_0_44, negated_conjecture, (k1_tops_1(esk1_0,k2_pre_topc(esk1_0,esk2_0))!=esk2_0|k2_pre_topc(esk1_0,k1_tops_1(esk1_0,esk2_0))!=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_31]), c_0_14]), c_0_15])])).
% 0.19/0.37  cnf(c_0_45, negated_conjecture, (k1_tops_1(esk1_0,esk2_0)=esk2_0|k2_pre_topc(esk1_0,k1_tops_1(esk1_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0)))!=k3_subset_1(u1_struct_0(esk1_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_29]), c_0_15])])).
% 0.19/0.37  cnf(c_0_46, negated_conjecture, (k1_tops_1(esk1_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0))=k3_subset_1(u1_struct_0(esk1_0),esk2_0)|k1_tops_1(esk1_0,esk2_0)=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_29]), c_0_15])])).
% 0.19/0.37  cnf(c_0_47, negated_conjecture, (k2_pre_topc(esk1_0,k1_tops_1(esk1_0,esk2_0))!=esk2_0|k1_tops_1(esk1_0,esk2_0)!=esk2_0), inference(rw,[status(thm)],[c_0_44, c_0_33])).
% 0.19/0.37  cnf(c_0_48, negated_conjecture, (k1_tops_1(esk1_0,esk2_0)=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_36])])).
% 0.19/0.37  cnf(c_0_49, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47, c_0_48]), c_0_33]), c_0_48])]), ['proof']).
% 0.19/0.37  # SZS output end CNFRefutation
% 0.19/0.37  # Proof object total steps             : 50
% 0.19/0.37  # Proof object clause steps            : 33
% 0.19/0.37  # Proof object formula steps           : 17
% 0.19/0.37  # Proof object conjectures             : 27
% 0.19/0.37  # Proof object clause conjectures      : 24
% 0.19/0.37  # Proof object formula conjectures     : 3
% 0.19/0.37  # Proof object initial clauses used    : 14
% 0.19/0.37  # Proof object initial formulas used   : 8
% 0.19/0.37  # Proof object generating inferences   : 17
% 0.19/0.37  # Proof object simplifying inferences  : 39
% 0.19/0.37  # Training examples: 0 positive, 0 negative
% 0.19/0.37  # Parsed axioms                        : 8
% 0.19/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.37  # Initial clauses                      : 18
% 0.19/0.37  # Removed in clause preprocessing      : 0
% 0.19/0.37  # Initial clauses in saturation        : 18
% 0.19/0.37  # Processed clauses                    : 71
% 0.19/0.37  # ...of these trivial                  : 0
% 0.19/0.37  # ...subsumed                          : 4
% 0.19/0.37  # ...remaining for further processing  : 67
% 0.19/0.37  # Other redundant clauses eliminated   : 0
% 0.19/0.37  # Clauses deleted for lack of memory   : 0
% 0.19/0.37  # Backward-subsumed                    : 4
% 0.19/0.37  # Backward-rewritten                   : 11
% 0.19/0.37  # Generated clauses                    : 61
% 0.19/0.37  # ...of the previous two non-trivial   : 47
% 0.19/0.37  # Contextual simplify-reflections      : 0
% 0.19/0.37  # Paramodulations                      : 61
% 0.19/0.37  # Factorizations                       : 0
% 0.19/0.37  # Equation resolutions                 : 0
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
% 0.19/0.37  # Current number of processed clauses  : 34
% 0.19/0.37  #    Positive orientable unit clauses  : 9
% 0.19/0.37  #    Positive unorientable unit clauses: 0
% 0.19/0.37  #    Negative unit clauses             : 0
% 0.19/0.37  #    Non-unit-clauses                  : 25
% 0.19/0.37  # Current number of unprocessed clauses: 10
% 0.19/0.37  # ...number of literals in the above   : 32
% 0.19/0.37  # Current number of archived formulas  : 0
% 0.19/0.37  # Current number of archived clauses   : 33
% 0.19/0.37  # Clause-clause subsumption calls (NU) : 152
% 0.19/0.37  # Rec. Clause-clause subsumption calls : 90
% 0.19/0.37  # Non-unit clause-clause subsumptions  : 8
% 0.19/0.37  # Unit Clause-clause subsumption calls : 4
% 0.19/0.37  # Rewrite failures with RHS unbound    : 0
% 0.19/0.37  # BW rewrite match attempts            : 3
% 0.19/0.37  # BW rewrite match successes           : 3
% 0.19/0.37  # Condensation attempts                : 0
% 0.19/0.37  # Condensation successes               : 0
% 0.19/0.37  # Termbank termtop insertions          : 2867
% 0.19/0.37  
% 0.19/0.37  # -------------------------------------------------
% 0.19/0.37  # User time                : 0.031 s
% 0.19/0.37  # System time              : 0.004 s
% 0.19/0.37  # Total time               : 0.035 s
% 0.19/0.37  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
