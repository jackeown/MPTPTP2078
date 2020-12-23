%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1280+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:02 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 182 expanded)
%              Number of clauses        :   32 (  70 expanded)
%              Number of leaves         :    9 (  43 expanded)
%              Depth                    :   10
%              Number of atoms          :  121 ( 540 expanded)
%              Number of equality atoms :   35 ( 133 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t102_tops_1,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v5_tops_1(X2,X1)
           => k2_tops_1(X1,k1_tops_1(X1,X2)) = k2_tops_1(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t102_tops_1)).

fof(d1_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k1_tops_1(X1,X2) = k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).

fof(dt_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(dt_k2_pre_topc,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(projectivity_k2_pre_topc,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => k2_pre_topc(X1,k2_pre_topc(X1,X2)) = k2_pre_topc(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',projectivity_k2_pre_topc)).

fof(dt_k1_tops_1,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_1)).

fof(d2_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k2_tops_1(X1,X2) = k9_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tops_1)).

fof(d7_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v5_tops_1(X2,X1)
          <=> X2 = k2_pre_topc(X1,k1_tops_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tops_1)).

fof(involutiveness_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,k3_subset_1(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( v5_tops_1(X2,X1)
             => k2_tops_1(X1,k1_tops_1(X1,X2)) = k2_tops_1(X1,X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t102_tops_1])).

fof(c_0_10,plain,(
    ! [X3,X4] :
      ( ~ l1_pre_topc(X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
      | k1_tops_1(X3,X4) = k3_subset_1(u1_struct_0(X3),k2_pre_topc(X3,k3_subset_1(u1_struct_0(X3),X4))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tops_1])])])).

fof(c_0_11,negated_conjecture,
    ( l1_pre_topc(esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & v5_tops_1(esk2_0,esk1_0)
    & k2_tops_1(esk1_0,k1_tops_1(esk1_0,esk2_0)) != k2_tops_1(esk1_0,esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).

cnf(c_0_12,plain,
    ( k1_tops_1(X1,X2) = k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_13,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_14,plain,(
    ! [X13,X14] :
      ( ~ m1_subset_1(X14,k1_zfmisc_1(X13))
      | m1_subset_1(k3_subset_1(X13,X14),k1_zfmisc_1(X13)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).

cnf(c_0_15,negated_conjecture,
    ( k3_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,k3_subset_1(u1_struct_0(esk1_0),X1))) = k1_tops_1(esk1_0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_16,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_17,plain,(
    ! [X11,X12] :
      ( ~ l1_pre_topc(X11)
      | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X11)))
      | m1_subset_1(k2_pre_topc(X11,X12),k1_zfmisc_1(u1_struct_0(X11))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).

fof(c_0_18,plain,(
    ! [X17,X18] :
      ( ~ l1_pre_topc(X17)
      | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))
      | k2_pre_topc(X17,k2_pre_topc(X17,X18)) = k2_pre_topc(X17,X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[projectivity_k2_pre_topc])])).

fof(c_0_19,plain,(
    ! [X9,X10] :
      ( ~ l1_pre_topc(X9)
      | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9)))
      | m1_subset_1(k1_tops_1(X9,X10),k1_zfmisc_1(u1_struct_0(X9))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_tops_1])])).

fof(c_0_20,plain,(
    ! [X5,X6] :
      ( ~ l1_pre_topc(X5)
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5)))
      | k2_tops_1(X5,X6) = k9_subset_1(u1_struct_0(X5),k2_pre_topc(X5,X6),k2_pre_topc(X5,k3_subset_1(u1_struct_0(X5),X6))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tops_1])])])).

cnf(c_0_21,plain,
    ( m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,negated_conjecture,
    ( k3_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0))) = k1_tops_1(esk1_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_23,plain,
    ( m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_24,plain,(
    ! [X7,X8] :
      ( ( ~ v5_tops_1(X8,X7)
        | X8 = k2_pre_topc(X7,k1_tops_1(X7,X8))
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X7)))
        | ~ l1_pre_topc(X7) )
      & ( X8 != k2_pre_topc(X7,k1_tops_1(X7,X8))
        | v5_tops_1(X8,X7)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X7)))
        | ~ l1_pre_topc(X7) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_tops_1])])])])).

fof(c_0_25,plain,(
    ! [X15,X16] :
      ( ~ m1_subset_1(X16,k1_zfmisc_1(X15))
      | k3_subset_1(X15,k3_subset_1(X15,X16)) = X16 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).

cnf(c_0_26,plain,
    ( k2_pre_topc(X1,k2_pre_topc(X1,X2)) = k2_pre_topc(X1,X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,plain,
    ( m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_28,plain,
    ( k2_tops_1(X1,X2) = k9_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,negated_conjecture,
    ( m1_subset_1(k1_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(k2_pre_topc(esk1_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0)),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_30,negated_conjecture,
    ( m1_subset_1(k2_pre_topc(esk1_0,X1),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_23,c_0_13])).

cnf(c_0_31,plain,
    ( X1 = k2_pre_topc(X2,k1_tops_1(X2,X1))
    | ~ v5_tops_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_32,negated_conjecture,
    ( v5_tops_1(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_33,plain,
    ( k3_subset_1(X2,k3_subset_1(X2,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_34,negated_conjecture,
    ( k2_pre_topc(esk1_0,k2_pre_topc(esk1_0,X1)) = k2_pre_topc(esk1_0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_26,c_0_13])).

cnf(c_0_35,negated_conjecture,
    ( m1_subset_1(k1_tops_1(esk1_0,X1),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_27,c_0_13])).

cnf(c_0_36,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,X1),k2_pre_topc(esk1_0,k3_subset_1(u1_struct_0(esk1_0),X1))) = k2_tops_1(esk1_0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_28,c_0_13])).

cnf(c_0_37,negated_conjecture,
    ( m1_subset_1(k1_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_38,negated_conjecture,
    ( k2_pre_topc(esk1_0,k1_tops_1(esk1_0,esk2_0)) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_16]),c_0_13])])).

cnf(c_0_39,negated_conjecture,
    ( k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,X1))) = k2_pre_topc(esk1_0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_33,c_0_30])).

cnf(c_0_40,negated_conjecture,
    ( k2_pre_topc(esk1_0,k2_pre_topc(esk1_0,k1_tops_1(esk1_0,X1))) = k2_pre_topc(esk1_0,k1_tops_1(esk1_0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_41,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk1_0),esk2_0,k2_pre_topc(esk1_0,k3_subset_1(u1_struct_0(esk1_0),k1_tops_1(esk1_0,esk2_0)))) = k2_tops_1(esk1_0,k1_tops_1(esk1_0,esk2_0))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_38])).

cnf(c_0_42,negated_conjecture,
    ( k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,k3_subset_1(u1_struct_0(esk1_0),X1)))) = k2_pre_topc(esk1_0,k3_subset_1(u1_struct_0(esk1_0),X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_39,c_0_21])).

cnf(c_0_43,negated_conjecture,
    ( k2_pre_topc(esk1_0,k2_pre_topc(esk1_0,k3_subset_1(u1_struct_0(esk1_0),X1))) = k2_pre_topc(esk1_0,k3_subset_1(u1_struct_0(esk1_0),X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_34,c_0_21])).

cnf(c_0_44,negated_conjecture,
    ( k2_pre_topc(esk1_0,esk2_0) = esk2_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_16]),c_0_38]),c_0_38])).

cnf(c_0_45,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk1_0),esk2_0,k2_pre_topc(esk1_0,k3_subset_1(u1_struct_0(esk1_0),k1_tops_1(esk1_0,esk2_0)))) = k2_tops_1(esk1_0,k1_tops_1(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_21]),c_0_16])])).

cnf(c_0_46,negated_conjecture,
    ( k3_subset_1(u1_struct_0(esk1_0),k1_tops_1(esk1_0,esk2_0)) = k2_pre_topc(esk1_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_16]),c_0_22])).

cnf(c_0_47,negated_conjecture,
    ( k2_pre_topc(esk1_0,k2_pre_topc(esk1_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0))) = k2_pre_topc(esk1_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_16])).

cnf(c_0_48,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk1_0),esk2_0,k2_pre_topc(esk1_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0))) = k2_tops_1(esk1_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_16]),c_0_44])).

cnf(c_0_49,negated_conjecture,
    ( k2_tops_1(esk1_0,k1_tops_1(esk1_0,esk2_0)) != k2_tops_1(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_50,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_46]),c_0_47]),c_0_48]),c_0_49]),
    [proof]).

%------------------------------------------------------------------------------
