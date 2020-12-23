%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1279+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:02 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   44 ( 198 expanded)
%              Number of clauses        :   27 (  81 expanded)
%              Number of leaves         :    8 (  54 expanded)
%              Depth                    :    9
%              Number of atoms          :  144 ( 635 expanded)
%              Number of equality atoms :   21 (  97 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal clause size      :    8 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d1_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k1_tops_1(X1,X2) = k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).

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

fof(dt_k2_pre_topc,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(d8_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v6_tops_1(X2,X1)
          <=> X2 = k1_tops_1(X1,k2_pre_topc(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_tops_1)).

fof(dt_k1_tops_1,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_1)).

fof(t101_tops_1,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v6_tops_1(X2,X1)
          <=> v5_tops_1(k3_subset_1(u1_struct_0(X1),X2),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t101_tops_1)).

fof(c_0_8,plain,(
    ! [X3,X4] :
      ( ~ l1_pre_topc(X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
      | k1_tops_1(X3,X4) = k3_subset_1(u1_struct_0(X3),k2_pre_topc(X3,k3_subset_1(u1_struct_0(X3),X4))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tops_1])])])).

fof(c_0_9,plain,(
    ! [X15,X16] :
      ( ~ m1_subset_1(X16,k1_zfmisc_1(X15))
      | k3_subset_1(X15,k3_subset_1(X15,X16)) = X16 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).

fof(c_0_10,plain,(
    ! [X13,X14] :
      ( ~ m1_subset_1(X14,k1_zfmisc_1(X13))
      | m1_subset_1(k3_subset_1(X13,X14),k1_zfmisc_1(X13)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).

fof(c_0_11,plain,(
    ! [X5,X6] :
      ( ( ~ v5_tops_1(X6,X5)
        | X6 = k2_pre_topc(X5,k1_tops_1(X5,X6))
        | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5)))
        | ~ l1_pre_topc(X5) )
      & ( X6 != k2_pre_topc(X5,k1_tops_1(X5,X6))
        | v5_tops_1(X6,X5)
        | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5)))
        | ~ l1_pre_topc(X5) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_tops_1])])])])).

cnf(c_0_12,plain,
    ( k1_tops_1(X1,X2) = k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( k3_subset_1(X2,k3_subset_1(X2,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_15,plain,(
    ! [X11,X12] :
      ( ~ l1_pre_topc(X11)
      | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X11)))
      | m1_subset_1(k2_pre_topc(X11,X12),k1_zfmisc_1(u1_struct_0(X11))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).

fof(c_0_16,plain,(
    ! [X7,X8] :
      ( ( ~ v6_tops_1(X8,X7)
        | X8 = k1_tops_1(X7,k2_pre_topc(X7,X8))
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X7)))
        | ~ l1_pre_topc(X7) )
      & ( X8 != k1_tops_1(X7,k2_pre_topc(X7,X8))
        | v6_tops_1(X8,X7)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X7)))
        | ~ l1_pre_topc(X7) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_tops_1])])])])).

fof(c_0_17,plain,(
    ! [X9,X10] :
      ( ~ l1_pre_topc(X9)
      | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9)))
      | m1_subset_1(k1_tops_1(X9,X10),k1_zfmisc_1(u1_struct_0(X9))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_tops_1])])).

cnf(c_0_18,plain,
    ( v5_tops_1(X1,X2)
    | X1 != k2_pre_topc(X2,k1_tops_1(X2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,plain,
    ( k1_tops_1(X1,k3_subset_1(u1_struct_0(X1),X2)) = k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_14])).

cnf(c_0_20,plain,
    ( k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2)) = k3_subset_1(u1_struct_0(X1),k1_tops_1(X1,X2))
    | ~ m1_subset_1(k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2)),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_13,c_0_12])).

cnf(c_0_21,plain,
    ( m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( v6_tops_1(X1,X2)
    | X1 != k1_tops_1(X2,k2_pre_topc(X2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( X1 = k2_pre_topc(X2,k1_tops_1(X2,X1))
    | ~ v5_tops_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_24,plain,
    ( m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,plain,
    ( v5_tops_1(k3_subset_1(u1_struct_0(X1),X2),X1)
    | k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2))) != k3_subset_1(u1_struct_0(X1),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_14])).

cnf(c_0_26,plain,
    ( k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2)) = k3_subset_1(u1_struct_0(X1),k1_tops_1(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_14])).

fof(c_0_27,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( v6_tops_1(X2,X1)
            <=> v5_tops_1(k3_subset_1(u1_struct_0(X1),X2),X1) ) ) ) ),
    inference(assume_negation,[status(cth)],[t101_tops_1])).

cnf(c_0_28,plain,
    ( v6_tops_1(k1_tops_1(X1,X2),X1)
    | ~ v5_tops_1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24])).

cnf(c_0_29,plain,
    ( v5_tops_1(k3_subset_1(u1_struct_0(X1),X2),X1)
    | k3_subset_1(u1_struct_0(X1),k1_tops_1(X1,k2_pre_topc(X1,X2))) != k3_subset_1(u1_struct_0(X1),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_21])).

fof(c_0_30,negated_conjecture,
    ( l1_pre_topc(esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & ( ~ v6_tops_1(esk2_0,esk1_0)
      | ~ v5_tops_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),esk1_0) )
    & ( v6_tops_1(esk2_0,esk1_0)
      | v5_tops_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),esk1_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_27])])])).

cnf(c_0_31,plain,
    ( X1 = k1_tops_1(X2,k2_pre_topc(X2,X1))
    | ~ v6_tops_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_32,plain,
    ( v6_tops_1(k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2)),X1)
    | ~ v5_tops_1(k3_subset_1(u1_struct_0(X1),X2),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_19]),c_0_14])).

cnf(c_0_33,plain,
    ( v5_tops_1(k3_subset_1(u1_struct_0(X1),k1_tops_1(X1,X2)),X1)
    | ~ v5_tops_1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_23]),c_0_24])).

cnf(c_0_34,negated_conjecture,
    ( ~ v6_tops_1(esk2_0,esk1_0)
    | ~ v5_tops_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_35,plain,
    ( v5_tops_1(k3_subset_1(u1_struct_0(X1),X2),X1)
    | ~ v6_tops_1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_31])).

cnf(c_0_36,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_37,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_38,plain,
    ( v6_tops_1(k3_subset_1(u1_struct_0(X1),X2),X1)
    | ~ v5_tops_1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_23]),c_0_24]),c_0_33])).

cnf(c_0_39,negated_conjecture,
    ( v6_tops_1(esk2_0,esk1_0)
    | v5_tops_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_40,negated_conjecture,
    ( ~ v6_tops_1(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36]),c_0_37])])).

cnf(c_0_41,plain,
    ( v6_tops_1(X1,X2)
    | ~ v5_tops_1(k3_subset_1(u1_struct_0(X2),X1),X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_13]),c_0_14])).

cnf(c_0_42,negated_conjecture,
    ( v5_tops_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),esk1_0) ),
    inference(sr,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_43,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_36]),c_0_37])]),c_0_40]),
    [proof]).

%------------------------------------------------------------------------------
