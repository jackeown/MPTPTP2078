%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:08:44 EST 2020

% Result     : CounterSatisfiable 0.19s
% Output     : Saturation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 727 expanded)
%              Number of clauses        :   53 ( 342 expanded)
%              Number of leaves         :   10 ( 184 expanded)
%              Depth                    :    9
%              Number of atoms          :  207 (1770 expanded)
%              Number of equality atoms :   84 ( 794 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   10 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(redefinition_k7_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k7_subset_1(X1,X2,X3) = k4_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(t22_pre_topc,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2)) = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_pre_topc)).

fof(t46_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(t23_pre_topc,conjecture,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( ~ ( X2 != k2_struct_0(X1)
                & k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2) = k1_xboole_0 )
            & ~ ( k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2) != k1_xboole_0
                & X2 = k2_struct_0(X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_pre_topc)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(t5_boole,axiom,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(c_0_10,plain,(
    ! [X13,X14,X15] :
      ( ~ m1_subset_1(X14,k1_zfmisc_1(X13))
      | k7_subset_1(X13,X14,X15) = k4_xboole_0(X14,X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).

fof(c_0_11,plain,(
    ! [X6,X7] : k4_xboole_0(X6,X7) = k5_xboole_0(X6,k3_xboole_0(X6,X7)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_12,plain,
    ( k7_subset_1(X2,X1,X3) = k4_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_13,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_14,plain,(
    ! [X16,X17] :
      ( ( ~ m1_subset_1(X16,k1_zfmisc_1(X17))
        | r1_tarski(X16,X17) )
      & ( ~ r1_tarski(X16,X17)
        | m1_subset_1(X16,k1_zfmisc_1(X17)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_15,plain,
    ( k7_subset_1(X2,X1,X3) = k5_xboole_0(X1,k3_xboole_0(X1,X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_12,c_0_13]),
    [final]).

cnf(c_0_16,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14]),
    [final]).

fof(c_0_17,plain,(
    ! [X18,X19] :
      ( ~ l1_struct_0(X18)
      | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))
      | k7_subset_1(u1_struct_0(X18),k2_struct_0(X18),k7_subset_1(u1_struct_0(X18),k2_struct_0(X18),X19)) = X19 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t22_pre_topc])])])).

cnf(c_0_18,plain,
    ( k7_subset_1(X1,X2,X3) = k5_xboole_0(X2,k3_xboole_0(X2,X3))
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16]),
    [final]).

fof(c_0_19,plain,(
    ! [X10,X11] : k4_xboole_0(X10,k2_xboole_0(X10,X11)) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t46_xboole_1])).

fof(c_0_20,negated_conjecture,(
    ~ ! [X1] :
        ( l1_struct_0(X1)
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( ~ ( X2 != k2_struct_0(X1)
                  & k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2) = k1_xboole_0 )
              & ~ ( k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2) != k1_xboole_0
                  & X2 = k2_struct_0(X1) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t23_pre_topc])).

cnf(c_0_21,plain,
    ( k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2)) = X2
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_17]),
    [final]).

cnf(c_0_22,plain,
    ( k7_subset_1(X1,X2,X3) = k7_subset_1(X4,X2,X3)
    | ~ r1_tarski(X2,X1)
    | ~ r1_tarski(X2,X4) ),
    inference(spm,[status(thm)],[c_0_18,c_0_18]),
    [final]).

cnf(c_0_23,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_24,negated_conjecture,
    ( l1_struct_0(esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & ( k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0) != k1_xboole_0
      | esk2_0 != k2_struct_0(esk1_0) )
    & ( esk2_0 = k2_struct_0(esk1_0)
      | esk2_0 != k2_struct_0(esk1_0) )
    & ( k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0) != k1_xboole_0
      | k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0) = k1_xboole_0 )
    & ( esk2_0 = k2_struct_0(esk1_0)
      | k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0) = k1_xboole_0 ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_20])])])])).

fof(c_0_25,plain,(
    ! [X9] : k3_xboole_0(X9,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

fof(c_0_26,plain,(
    ! [X12] : k5_xboole_0(X12,k1_xboole_0) = X12 ),
    inference(variable_rename,[status(thm)],[t5_boole])).

cnf(c_0_27,plain,
    ( k7_subset_1(X1,k2_struct_0(X2),k7_subset_1(u1_struct_0(X2),k2_struct_0(X2),X3)) = X3
    | ~ l1_struct_0(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r1_tarski(k2_struct_0(X2),u1_struct_0(X2))
    | ~ r1_tarski(k2_struct_0(X2),X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22]),
    [final]).

cnf(c_0_28,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k2_xboole_0(X1,X2))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_23,c_0_13]),
    [final]).

cnf(c_0_29,negated_conjecture,
    ( esk2_0 = k2_struct_0(esk1_0)
    | k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_24]),
    [final]).

cnf(c_0_30,negated_conjecture,
    ( l1_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24]),
    [final]).

cnf(c_0_31,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_24]),
    [final]).

cnf(c_0_32,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_25]),
    [final]).

cnf(c_0_33,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_26]),
    [final]).

fof(c_0_34,plain,(
    ! [X8] : k2_xboole_0(X8,k1_xboole_0) = X8 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

cnf(c_0_35,plain,
    ( k7_subset_1(X1,k2_struct_0(X2),k7_subset_1(X3,k2_struct_0(X2),X4)) = X4
    | ~ l1_struct_0(X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r1_tarski(k2_struct_0(X2),u1_struct_0(X2))
    | ~ r1_tarski(k2_struct_0(X2),X1)
    | ~ r1_tarski(k2_struct_0(X2),X3) ),
    inference(spm,[status(thm)],[c_0_27,c_0_22]),
    [final]).

cnf(c_0_36,plain,
    ( k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(X2,k2_struct_0(X1),X3)) = X3
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(k2_struct_0(X1),u1_struct_0(X1))
    | ~ r1_tarski(k2_struct_0(X1),X2) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22]),
    [final]).

cnf(c_0_37,plain,
    ( k7_subset_1(X1,X2,k2_xboole_0(X2,X3)) = k1_xboole_0
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_18]),
    [final]).

cnf(c_0_38,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),k1_xboole_0) = esk2_0
    | k2_struct_0(esk1_0) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_29]),c_0_30]),c_0_31])]),
    [final]).

cnf(c_0_39,plain,
    ( k7_subset_1(X1,X2,k1_xboole_0) = X2
    | ~ r1_tarski(X2,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_32]),c_0_33]),
    [final]).

cnf(c_0_40,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_34]),
    [final]).

fof(c_0_41,plain,(
    ! [X4,X5] :
      ( ( r1_tarski(X4,X5)
        | X4 != X5 )
      & ( r1_tarski(X5,X4)
        | X4 != X5 )
      & ( ~ r1_tarski(X4,X5)
        | ~ r1_tarski(X5,X4)
        | X4 = X5 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_42,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_14]),
    [final]).

cnf(c_0_43,plain,
    ( k7_subset_1(X1,k2_struct_0(X2),k5_xboole_0(k2_struct_0(X2),k3_xboole_0(k2_struct_0(X2),X3))) = X3
    | ~ l1_struct_0(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r1_tarski(k2_struct_0(X2),u1_struct_0(X2))
    | ~ r1_tarski(k2_struct_0(X2),X1)
    | ~ r1_tarski(k2_struct_0(X2),X4) ),
    inference(spm,[status(thm)],[c_0_35,c_0_18]),
    [final]).

cnf(c_0_44,plain,
    ( k5_xboole_0(k2_struct_0(X1),k3_xboole_0(k2_struct_0(X1),k7_subset_1(X2,k2_struct_0(X1),X3))) = X3
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(k2_struct_0(X1),u1_struct_0(X1))
    | ~ r1_tarski(k2_struct_0(X1),X4)
    | ~ r1_tarski(k2_struct_0(X1),X2) ),
    inference(spm,[status(thm)],[c_0_18,c_0_35]),
    [final]).

cnf(c_0_45,plain,
    ( k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k5_xboole_0(k2_struct_0(X1),k3_xboole_0(k2_struct_0(X1),X2))) = X2
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(k2_struct_0(X1),u1_struct_0(X1))
    | ~ r1_tarski(k2_struct_0(X1),X3) ),
    inference(spm,[status(thm)],[c_0_36,c_0_18]),
    [final]).

cnf(c_0_46,plain,
    ( k5_xboole_0(k2_struct_0(X1),k3_xboole_0(k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2))) = X2
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(k2_struct_0(X1),u1_struct_0(X1))
    | ~ r1_tarski(k2_struct_0(X1),X3) ),
    inference(spm,[status(thm)],[c_0_18,c_0_27]),
    [final]).

cnf(c_0_47,plain,
    ( k7_subset_1(X1,k2_struct_0(X2),k1_xboole_0) = k2_xboole_0(k2_struct_0(X2),X3)
    | ~ l1_struct_0(X2)
    | ~ m1_subset_1(k2_xboole_0(k2_struct_0(X2),X3),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r1_tarski(k2_struct_0(X2),u1_struct_0(X2))
    | ~ r1_tarski(k2_struct_0(X2),X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_37]),
    [final]).

cnf(c_0_48,plain,
    ( k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k1_xboole_0) = k2_xboole_0(k2_struct_0(X1),X2)
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(k2_xboole_0(k2_struct_0(X1),X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(k2_struct_0(X1),u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_37]),
    [final]).

cnf(c_0_49,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0) != k1_xboole_0
    | esk2_0 != k2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24]),
    [final]).

cnf(c_0_50,negated_conjecture,
    ( k2_struct_0(esk1_0) = esk2_0
    | ~ r1_tarski(k2_struct_0(esk1_0),u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39]),
    [final]).

cnf(c_0_51,negated_conjecture,
    ( k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,X1)) = k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_15,c_0_31]),
    [final]).

cnf(c_0_52,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X1)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_28,c_0_40]),
    [final]).

cnf(c_0_53,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41]),
    [final]).

cnf(c_0_54,negated_conjecture,
    ( r1_tarski(esk2_0,u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_31]),
    [final]).

cnf(c_0_55,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_56,plain,
    ( k7_subset_1(X1,k2_struct_0(X2),k5_xboole_0(k2_struct_0(X2),k3_xboole_0(k2_struct_0(X2),X3))) = X3
    | ~ l1_struct_0(X2)
    | ~ r1_tarski(k2_struct_0(X2),u1_struct_0(X2))
    | ~ r1_tarski(k2_struct_0(X2),X1)
    | ~ r1_tarski(k2_struct_0(X2),X4)
    | ~ r1_tarski(X3,u1_struct_0(X2)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_16]),
    [final]).

cnf(c_0_57,plain,
    ( k5_xboole_0(k2_struct_0(X1),k3_xboole_0(k2_struct_0(X1),k7_subset_1(X2,k2_struct_0(X1),X3))) = X3
    | ~ l1_struct_0(X1)
    | ~ r1_tarski(k2_struct_0(X1),u1_struct_0(X1))
    | ~ r1_tarski(k2_struct_0(X1),X4)
    | ~ r1_tarski(k2_struct_0(X1),X2)
    | ~ r1_tarski(X3,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_16]),
    [final]).

cnf(c_0_58,negated_conjecture,
    ( k7_subset_1(X1,k2_struct_0(esk1_0),k5_xboole_0(k2_struct_0(esk1_0),k3_xboole_0(k2_struct_0(esk1_0),esk2_0))) = esk2_0
    | ~ r1_tarski(k2_struct_0(esk1_0),u1_struct_0(esk1_0))
    | ~ r1_tarski(k2_struct_0(esk1_0),X1)
    | ~ r1_tarski(k2_struct_0(esk1_0),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_31]),c_0_30])]),
    [final]).

cnf(c_0_59,negated_conjecture,
    ( k5_xboole_0(k2_struct_0(esk1_0),k3_xboole_0(k2_struct_0(esk1_0),k7_subset_1(X1,k2_struct_0(esk1_0),esk2_0))) = esk2_0
    | ~ r1_tarski(k2_struct_0(esk1_0),u1_struct_0(esk1_0))
    | ~ r1_tarski(k2_struct_0(esk1_0),X2)
    | ~ r1_tarski(k2_struct_0(esk1_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_31]),c_0_30])]),
    [final]).

cnf(c_0_60,plain,
    ( k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k5_xboole_0(k2_struct_0(X1),k3_xboole_0(k2_struct_0(X1),X2))) = X2
    | ~ l1_struct_0(X1)
    | ~ r1_tarski(k2_struct_0(X1),u1_struct_0(X1))
    | ~ r1_tarski(k2_struct_0(X1),X3)
    | ~ r1_tarski(X2,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_16]),
    [final]).

cnf(c_0_61,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),k5_xboole_0(k2_struct_0(esk1_0),k3_xboole_0(k2_struct_0(esk1_0),esk2_0))) = esk2_0
    | ~ r1_tarski(k2_struct_0(esk1_0),u1_struct_0(esk1_0))
    | ~ r1_tarski(k2_struct_0(esk1_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_31]),c_0_30])]),
    [final]).

cnf(c_0_62,plain,
    ( k5_xboole_0(k2_struct_0(X1),k3_xboole_0(k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2))) = X2
    | ~ l1_struct_0(X1)
    | ~ r1_tarski(k2_struct_0(X1),u1_struct_0(X1))
    | ~ r1_tarski(k2_struct_0(X1),X3)
    | ~ r1_tarski(X2,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_16]),
    [final]).

cnf(c_0_63,plain,
    ( k7_subset_1(X1,k2_struct_0(X2),k1_xboole_0) = k2_xboole_0(k2_struct_0(X2),X3)
    | ~ l1_struct_0(X2)
    | ~ r1_tarski(k2_xboole_0(k2_struct_0(X2),X3),u1_struct_0(X2))
    | ~ r1_tarski(k2_struct_0(X2),u1_struct_0(X2))
    | ~ r1_tarski(k2_struct_0(X2),X1) ),
    inference(spm,[status(thm)],[c_0_47,c_0_16]),
    [final]).

cnf(c_0_64,negated_conjecture,
    ( k5_xboole_0(k2_struct_0(esk1_0),k3_xboole_0(k2_struct_0(esk1_0),k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0))) = esk2_0
    | ~ r1_tarski(k2_struct_0(esk1_0),u1_struct_0(esk1_0))
    | ~ r1_tarski(k2_struct_0(esk1_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_31]),c_0_30])]),
    [final]).

cnf(c_0_65,plain,
    ( k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k1_xboole_0) = k2_xboole_0(k2_struct_0(X1),X2)
    | ~ l1_struct_0(X1)
    | ~ r1_tarski(k2_xboole_0(k2_struct_0(X1),X2),u1_struct_0(X1))
    | ~ r1_tarski(k2_struct_0(X1),u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_16]),
    [final]).

cnf(c_0_66,negated_conjecture,
    ( k7_subset_1(X1,k2_struct_0(esk1_0),esk2_0) != k1_xboole_0
    | ~ r1_tarski(k2_struct_0(esk1_0),u1_struct_0(esk1_0))
    | ~ r1_tarski(k2_struct_0(esk1_0),X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_22]),c_0_50]),
    [final]).

cnf(c_0_67,negated_conjecture,
    ( k7_subset_1(X1,esk2_0,X2) = k7_subset_1(u1_struct_0(esk1_0),esk2_0,X2)
    | ~ r1_tarski(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_51,c_0_18]),
    [final]).

cnf(c_0_68,plain,
    ( k7_subset_1(X1,X2,X2) = k1_xboole_0
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_52,c_0_18]),
    [final]).

cnf(c_0_69,negated_conjecture,
    ( u1_struct_0(esk1_0) = esk2_0
    | ~ r1_tarski(u1_struct_0(esk1_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54]),
    [final]).

cnf(c_0_70,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),esk2_0,k2_xboole_0(esk2_0,X1)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_28,c_0_51]),
    [final]).

cnf(c_0_71,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),esk2_0,k1_xboole_0) = esk2_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_32]),c_0_33]),
    [final]).

cnf(c_0_72,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),esk2_0,esk2_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_52,c_0_51]),
    [final]).

cnf(c_0_73,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_55]),
    [final]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:41:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.19/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.38  #
% 0.19/0.38  # Preprocessing time       : 0.027 s
% 0.19/0.38  # Presaturation interreduction done
% 0.19/0.38  
% 0.19/0.38  # No proof found!
% 0.19/0.38  # SZS status CounterSatisfiable
% 0.19/0.38  # SZS output start Saturation
% 0.19/0.38  fof(redefinition_k7_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k7_subset_1(X1,X2,X3)=k4_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 0.19/0.38  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.19/0.38  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.19/0.38  fof(t22_pre_topc, axiom, ![X1]:(l1_struct_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2))=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_pre_topc)).
% 0.19/0.38  fof(t46_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 0.19/0.38  fof(t23_pre_topc, conjecture, ![X1]:(l1_struct_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(~((X2!=k2_struct_0(X1)&k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2)=k1_xboole_0))&~((k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2)!=k1_xboole_0&X2=k2_struct_0(X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_pre_topc)).
% 0.19/0.38  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 0.19/0.38  fof(t5_boole, axiom, ![X1]:k5_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 0.19/0.38  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 0.19/0.38  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.19/0.38  fof(c_0_10, plain, ![X13, X14, X15]:(~m1_subset_1(X14,k1_zfmisc_1(X13))|k7_subset_1(X13,X14,X15)=k4_xboole_0(X14,X15)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).
% 0.19/0.38  fof(c_0_11, plain, ![X6, X7]:k4_xboole_0(X6,X7)=k5_xboole_0(X6,k3_xboole_0(X6,X7)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.19/0.38  cnf(c_0_12, plain, (k7_subset_1(X2,X1,X3)=k4_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.38  cnf(c_0_13, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.38  fof(c_0_14, plain, ![X16, X17]:((~m1_subset_1(X16,k1_zfmisc_1(X17))|r1_tarski(X16,X17))&(~r1_tarski(X16,X17)|m1_subset_1(X16,k1_zfmisc_1(X17)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.19/0.38  cnf(c_0_15, plain, (k7_subset_1(X2,X1,X3)=k5_xboole_0(X1,k3_xboole_0(X1,X3))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_12, c_0_13]), ['final']).
% 0.19/0.38  cnf(c_0_16, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14]), ['final']).
% 0.19/0.38  fof(c_0_17, plain, ![X18, X19]:(~l1_struct_0(X18)|(~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))|k7_subset_1(u1_struct_0(X18),k2_struct_0(X18),k7_subset_1(u1_struct_0(X18),k2_struct_0(X18),X19))=X19)), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t22_pre_topc])])])).
% 0.19/0.38  cnf(c_0_18, plain, (k7_subset_1(X1,X2,X3)=k5_xboole_0(X2,k3_xboole_0(X2,X3))|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_15, c_0_16]), ['final']).
% 0.19/0.38  fof(c_0_19, plain, ![X10, X11]:k4_xboole_0(X10,k2_xboole_0(X10,X11))=k1_xboole_0, inference(variable_rename,[status(thm)],[t46_xboole_1])).
% 0.19/0.38  fof(c_0_20, negated_conjecture, ~(![X1]:(l1_struct_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(~((X2!=k2_struct_0(X1)&k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2)=k1_xboole_0))&~((k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2)!=k1_xboole_0&X2=k2_struct_0(X1))))))), inference(assume_negation,[status(cth)],[t23_pre_topc])).
% 0.19/0.38  cnf(c_0_21, plain, (k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2))=X2|~l1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_17]), ['final']).
% 0.19/0.38  cnf(c_0_22, plain, (k7_subset_1(X1,X2,X3)=k7_subset_1(X4,X2,X3)|~r1_tarski(X2,X1)|~r1_tarski(X2,X4)), inference(spm,[status(thm)],[c_0_18, c_0_18]), ['final']).
% 0.19/0.38  cnf(c_0_23, plain, (k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.38  fof(c_0_24, negated_conjecture, (l1_struct_0(esk1_0)&(m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&(((k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)!=k1_xboole_0|esk2_0!=k2_struct_0(esk1_0))&(esk2_0=k2_struct_0(esk1_0)|esk2_0!=k2_struct_0(esk1_0)))&((k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)!=k1_xboole_0|k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)=k1_xboole_0)&(esk2_0=k2_struct_0(esk1_0)|k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)=k1_xboole_0))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_20])])])])).
% 0.19/0.38  fof(c_0_25, plain, ![X9]:k3_xboole_0(X9,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 0.19/0.38  fof(c_0_26, plain, ![X12]:k5_xboole_0(X12,k1_xboole_0)=X12, inference(variable_rename,[status(thm)],[t5_boole])).
% 0.19/0.38  cnf(c_0_27, plain, (k7_subset_1(X1,k2_struct_0(X2),k7_subset_1(u1_struct_0(X2),k2_struct_0(X2),X3))=X3|~l1_struct_0(X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~r1_tarski(k2_struct_0(X2),u1_struct_0(X2))|~r1_tarski(k2_struct_0(X2),X1)), inference(spm,[status(thm)],[c_0_21, c_0_22]), ['final']).
% 0.19/0.38  cnf(c_0_28, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k2_xboole_0(X1,X2)))=k1_xboole_0), inference(rw,[status(thm)],[c_0_23, c_0_13]), ['final']).
% 0.19/0.38  cnf(c_0_29, negated_conjecture, (esk2_0=k2_struct_0(esk1_0)|k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_24]), ['final']).
% 0.19/0.38  cnf(c_0_30, negated_conjecture, (l1_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_24]), ['final']).
% 0.19/0.38  cnf(c_0_31, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_24]), ['final']).
% 0.19/0.38  cnf(c_0_32, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_25]), ['final']).
% 0.19/0.38  cnf(c_0_33, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_26]), ['final']).
% 0.19/0.38  fof(c_0_34, plain, ![X8]:k2_xboole_0(X8,k1_xboole_0)=X8, inference(variable_rename,[status(thm)],[t1_boole])).
% 0.19/0.38  cnf(c_0_35, plain, (k7_subset_1(X1,k2_struct_0(X2),k7_subset_1(X3,k2_struct_0(X2),X4))=X4|~l1_struct_0(X2)|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))|~r1_tarski(k2_struct_0(X2),u1_struct_0(X2))|~r1_tarski(k2_struct_0(X2),X1)|~r1_tarski(k2_struct_0(X2),X3)), inference(spm,[status(thm)],[c_0_27, c_0_22]), ['final']).
% 0.19/0.38  cnf(c_0_36, plain, (k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(X2,k2_struct_0(X1),X3))=X3|~l1_struct_0(X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(k2_struct_0(X1),u1_struct_0(X1))|~r1_tarski(k2_struct_0(X1),X2)), inference(spm,[status(thm)],[c_0_21, c_0_22]), ['final']).
% 0.19/0.38  cnf(c_0_37, plain, (k7_subset_1(X1,X2,k2_xboole_0(X2,X3))=k1_xboole_0|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_28, c_0_18]), ['final']).
% 0.19/0.38  cnf(c_0_38, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),k1_xboole_0)=esk2_0|k2_struct_0(esk1_0)=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_29]), c_0_30]), c_0_31])]), ['final']).
% 0.19/0.38  cnf(c_0_39, plain, (k7_subset_1(X1,X2,k1_xboole_0)=X2|~r1_tarski(X2,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_32]), c_0_33]), ['final']).
% 0.19/0.38  cnf(c_0_40, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_34]), ['final']).
% 0.19/0.38  fof(c_0_41, plain, ![X4, X5]:(((r1_tarski(X4,X5)|X4!=X5)&(r1_tarski(X5,X4)|X4!=X5))&(~r1_tarski(X4,X5)|~r1_tarski(X5,X4)|X4=X5)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.19/0.38  cnf(c_0_42, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_14]), ['final']).
% 0.19/0.38  cnf(c_0_43, plain, (k7_subset_1(X1,k2_struct_0(X2),k5_xboole_0(k2_struct_0(X2),k3_xboole_0(k2_struct_0(X2),X3)))=X3|~l1_struct_0(X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~r1_tarski(k2_struct_0(X2),u1_struct_0(X2))|~r1_tarski(k2_struct_0(X2),X1)|~r1_tarski(k2_struct_0(X2),X4)), inference(spm,[status(thm)],[c_0_35, c_0_18]), ['final']).
% 0.19/0.38  cnf(c_0_44, plain, (k5_xboole_0(k2_struct_0(X1),k3_xboole_0(k2_struct_0(X1),k7_subset_1(X2,k2_struct_0(X1),X3)))=X3|~l1_struct_0(X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(k2_struct_0(X1),u1_struct_0(X1))|~r1_tarski(k2_struct_0(X1),X4)|~r1_tarski(k2_struct_0(X1),X2)), inference(spm,[status(thm)],[c_0_18, c_0_35]), ['final']).
% 0.19/0.38  cnf(c_0_45, plain, (k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k5_xboole_0(k2_struct_0(X1),k3_xboole_0(k2_struct_0(X1),X2)))=X2|~l1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(k2_struct_0(X1),u1_struct_0(X1))|~r1_tarski(k2_struct_0(X1),X3)), inference(spm,[status(thm)],[c_0_36, c_0_18]), ['final']).
% 0.19/0.38  cnf(c_0_46, plain, (k5_xboole_0(k2_struct_0(X1),k3_xboole_0(k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2)))=X2|~l1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(k2_struct_0(X1),u1_struct_0(X1))|~r1_tarski(k2_struct_0(X1),X3)), inference(spm,[status(thm)],[c_0_18, c_0_27]), ['final']).
% 0.19/0.38  cnf(c_0_47, plain, (k7_subset_1(X1,k2_struct_0(X2),k1_xboole_0)=k2_xboole_0(k2_struct_0(X2),X3)|~l1_struct_0(X2)|~m1_subset_1(k2_xboole_0(k2_struct_0(X2),X3),k1_zfmisc_1(u1_struct_0(X2)))|~r1_tarski(k2_struct_0(X2),u1_struct_0(X2))|~r1_tarski(k2_struct_0(X2),X1)), inference(spm,[status(thm)],[c_0_27, c_0_37]), ['final']).
% 0.19/0.38  cnf(c_0_48, plain, (k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k1_xboole_0)=k2_xboole_0(k2_struct_0(X1),X2)|~l1_struct_0(X1)|~m1_subset_1(k2_xboole_0(k2_struct_0(X1),X2),k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(k2_struct_0(X1),u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_21, c_0_37]), ['final']).
% 0.19/0.38  cnf(c_0_49, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)!=k1_xboole_0|esk2_0!=k2_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_24]), ['final']).
% 0.19/0.38  cnf(c_0_50, negated_conjecture, (k2_struct_0(esk1_0)=esk2_0|~r1_tarski(k2_struct_0(esk1_0),u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_38, c_0_39]), ['final']).
% 0.19/0.38  cnf(c_0_51, negated_conjecture, (k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,X1))=k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1)), inference(spm,[status(thm)],[c_0_15, c_0_31]), ['final']).
% 0.19/0.38  cnf(c_0_52, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X1))=k1_xboole_0), inference(spm,[status(thm)],[c_0_28, c_0_40]), ['final']).
% 0.19/0.38  cnf(c_0_53, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_41]), ['final']).
% 0.19/0.38  cnf(c_0_54, negated_conjecture, (r1_tarski(esk2_0,u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_42, c_0_31]), ['final']).
% 0.19/0.38  cnf(c_0_55, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.19/0.38  cnf(c_0_56, plain, (k7_subset_1(X1,k2_struct_0(X2),k5_xboole_0(k2_struct_0(X2),k3_xboole_0(k2_struct_0(X2),X3)))=X3|~l1_struct_0(X2)|~r1_tarski(k2_struct_0(X2),u1_struct_0(X2))|~r1_tarski(k2_struct_0(X2),X1)|~r1_tarski(k2_struct_0(X2),X4)|~r1_tarski(X3,u1_struct_0(X2))), inference(spm,[status(thm)],[c_0_43, c_0_16]), ['final']).
% 0.19/0.38  cnf(c_0_57, plain, (k5_xboole_0(k2_struct_0(X1),k3_xboole_0(k2_struct_0(X1),k7_subset_1(X2,k2_struct_0(X1),X3)))=X3|~l1_struct_0(X1)|~r1_tarski(k2_struct_0(X1),u1_struct_0(X1))|~r1_tarski(k2_struct_0(X1),X4)|~r1_tarski(k2_struct_0(X1),X2)|~r1_tarski(X3,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_44, c_0_16]), ['final']).
% 0.19/0.38  cnf(c_0_58, negated_conjecture, (k7_subset_1(X1,k2_struct_0(esk1_0),k5_xboole_0(k2_struct_0(esk1_0),k3_xboole_0(k2_struct_0(esk1_0),esk2_0)))=esk2_0|~r1_tarski(k2_struct_0(esk1_0),u1_struct_0(esk1_0))|~r1_tarski(k2_struct_0(esk1_0),X1)|~r1_tarski(k2_struct_0(esk1_0),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_31]), c_0_30])]), ['final']).
% 0.19/0.38  cnf(c_0_59, negated_conjecture, (k5_xboole_0(k2_struct_0(esk1_0),k3_xboole_0(k2_struct_0(esk1_0),k7_subset_1(X1,k2_struct_0(esk1_0),esk2_0)))=esk2_0|~r1_tarski(k2_struct_0(esk1_0),u1_struct_0(esk1_0))|~r1_tarski(k2_struct_0(esk1_0),X2)|~r1_tarski(k2_struct_0(esk1_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_31]), c_0_30])]), ['final']).
% 0.19/0.38  cnf(c_0_60, plain, (k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k5_xboole_0(k2_struct_0(X1),k3_xboole_0(k2_struct_0(X1),X2)))=X2|~l1_struct_0(X1)|~r1_tarski(k2_struct_0(X1),u1_struct_0(X1))|~r1_tarski(k2_struct_0(X1),X3)|~r1_tarski(X2,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_45, c_0_16]), ['final']).
% 0.19/0.38  cnf(c_0_61, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),k5_xboole_0(k2_struct_0(esk1_0),k3_xboole_0(k2_struct_0(esk1_0),esk2_0)))=esk2_0|~r1_tarski(k2_struct_0(esk1_0),u1_struct_0(esk1_0))|~r1_tarski(k2_struct_0(esk1_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_31]), c_0_30])]), ['final']).
% 0.19/0.38  cnf(c_0_62, plain, (k5_xboole_0(k2_struct_0(X1),k3_xboole_0(k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2)))=X2|~l1_struct_0(X1)|~r1_tarski(k2_struct_0(X1),u1_struct_0(X1))|~r1_tarski(k2_struct_0(X1),X3)|~r1_tarski(X2,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_46, c_0_16]), ['final']).
% 0.19/0.38  cnf(c_0_63, plain, (k7_subset_1(X1,k2_struct_0(X2),k1_xboole_0)=k2_xboole_0(k2_struct_0(X2),X3)|~l1_struct_0(X2)|~r1_tarski(k2_xboole_0(k2_struct_0(X2),X3),u1_struct_0(X2))|~r1_tarski(k2_struct_0(X2),u1_struct_0(X2))|~r1_tarski(k2_struct_0(X2),X1)), inference(spm,[status(thm)],[c_0_47, c_0_16]), ['final']).
% 0.19/0.38  cnf(c_0_64, negated_conjecture, (k5_xboole_0(k2_struct_0(esk1_0),k3_xboole_0(k2_struct_0(esk1_0),k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)))=esk2_0|~r1_tarski(k2_struct_0(esk1_0),u1_struct_0(esk1_0))|~r1_tarski(k2_struct_0(esk1_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_31]), c_0_30])]), ['final']).
% 0.19/0.38  cnf(c_0_65, plain, (k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k1_xboole_0)=k2_xboole_0(k2_struct_0(X1),X2)|~l1_struct_0(X1)|~r1_tarski(k2_xboole_0(k2_struct_0(X1),X2),u1_struct_0(X1))|~r1_tarski(k2_struct_0(X1),u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_48, c_0_16]), ['final']).
% 0.19/0.38  cnf(c_0_66, negated_conjecture, (k7_subset_1(X1,k2_struct_0(esk1_0),esk2_0)!=k1_xboole_0|~r1_tarski(k2_struct_0(esk1_0),u1_struct_0(esk1_0))|~r1_tarski(k2_struct_0(esk1_0),X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_22]), c_0_50]), ['final']).
% 0.19/0.38  cnf(c_0_67, negated_conjecture, (k7_subset_1(X1,esk2_0,X2)=k7_subset_1(u1_struct_0(esk1_0),esk2_0,X2)|~r1_tarski(esk2_0,X1)), inference(spm,[status(thm)],[c_0_51, c_0_18]), ['final']).
% 0.19/0.38  cnf(c_0_68, plain, (k7_subset_1(X1,X2,X2)=k1_xboole_0|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_52, c_0_18]), ['final']).
% 0.19/0.38  cnf(c_0_69, negated_conjecture, (u1_struct_0(esk1_0)=esk2_0|~r1_tarski(u1_struct_0(esk1_0),esk2_0)), inference(spm,[status(thm)],[c_0_53, c_0_54]), ['final']).
% 0.19/0.38  cnf(c_0_70, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),esk2_0,k2_xboole_0(esk2_0,X1))=k1_xboole_0), inference(spm,[status(thm)],[c_0_28, c_0_51]), ['final']).
% 0.19/0.38  cnf(c_0_71, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),esk2_0,k1_xboole_0)=esk2_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_32]), c_0_33]), ['final']).
% 0.19/0.38  cnf(c_0_72, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),esk2_0,esk2_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_52, c_0_51]), ['final']).
% 0.19/0.38  cnf(c_0_73, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_55]), ['final']).
% 0.19/0.38  # SZS output end Saturation
% 0.19/0.38  # Proof object total steps             : 74
% 0.19/0.38  # Proof object clause steps            : 53
% 0.19/0.38  # Proof object formula steps           : 21
% 0.19/0.38  # Proof object conjectures             : 21
% 0.19/0.38  # Proof object clause conjectures      : 18
% 0.19/0.38  # Proof object formula conjectures     : 3
% 0.19/0.38  # Proof object initial clauses used    : 15
% 0.19/0.38  # Proof object initial formulas used   : 10
% 0.19/0.38  # Proof object generating inferences   : 35
% 0.19/0.38  # Proof object simplifying inferences  : 17
% 0.19/0.38  # Parsed axioms                        : 10
% 0.19/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.38  # Initial clauses                      : 18
% 0.19/0.38  # Removed in clause preprocessing      : 3
% 0.19/0.38  # Initial clauses in saturation        : 15
% 0.19/0.38  # Processed clauses                    : 148
% 0.19/0.38  # ...of these trivial                  : 0
% 0.19/0.38  # ...subsumed                          : 83
% 0.19/0.38  # ...remaining for further processing  : 65
% 0.19/0.38  # Other redundant clauses eliminated   : 2
% 0.19/0.38  # Clauses deleted for lack of memory   : 0
% 0.19/0.38  # Backward-subsumed                    : 0
% 0.19/0.38  # Backward-rewritten                   : 0
% 0.19/0.38  # Generated clauses                    : 134
% 0.19/0.38  # ...of the previous two non-trivial   : 119
% 0.19/0.38  # Contextual simplify-reflections      : 1
% 0.19/0.38  # Paramodulations                      : 132
% 0.19/0.38  # Factorizations                       : 0
% 0.19/0.38  # Equation resolutions                 : 2
% 0.19/0.38  # Propositional unsat checks           : 0
% 0.19/0.38  #    Propositional check models        : 0
% 0.19/0.38  #    Propositional check unsatisfiable : 0
% 0.19/0.38  #    Propositional clauses             : 0
% 0.19/0.38  #    Propositional clauses after purity: 0
% 0.19/0.38  #    Propositional unsat core size     : 0
% 0.19/0.38  #    Propositional preprocessing time  : 0.000
% 0.19/0.38  #    Propositional encoding time       : 0.000
% 0.19/0.38  #    Propositional solver time         : 0.000
% 0.19/0.38  #    Success case prop preproc time    : 0.000
% 0.19/0.38  #    Success case prop encoding time   : 0.000
% 0.19/0.38  #    Success case prop solver time     : 0.000
% 0.19/0.38  # Current number of processed clauses  : 49
% 0.19/0.38  #    Positive orientable unit clauses  : 13
% 0.19/0.38  #    Positive unorientable unit clauses: 0
% 0.19/0.38  #    Negative unit clauses             : 0
% 0.19/0.38  #    Non-unit-clauses                  : 36
% 0.19/0.38  # Current number of unprocessed clauses: 0
% 0.19/0.38  # ...number of literals in the above   : 0
% 0.19/0.38  # Current number of archived formulas  : 0
% 0.19/0.38  # Current number of archived clauses   : 15
% 0.19/0.38  # Clause-clause subsumption calls (NU) : 715
% 0.19/0.38  # Rec. Clause-clause subsumption calls : 377
% 0.19/0.38  # Non-unit clause-clause subsumptions  : 84
% 0.19/0.38  # Unit Clause-clause subsumption calls : 7
% 0.19/0.38  # Rewrite failures with RHS unbound    : 0
% 0.19/0.38  # BW rewrite match attempts            : 7
% 0.19/0.38  # BW rewrite match successes           : 0
% 0.19/0.38  # Condensation attempts                : 0
% 0.19/0.38  # Condensation successes               : 0
% 0.19/0.38  # Termbank termtop insertions          : 3932
% 0.19/0.38  
% 0.19/0.38  # -------------------------------------------------
% 0.19/0.38  # User time                : 0.033 s
% 0.19/0.38  # System time              : 0.004 s
% 0.19/0.38  # Total time               : 0.037 s
% 0.19/0.38  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
