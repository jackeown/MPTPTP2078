%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:08:43 EST 2020

% Result     : CounterSatisfiable 0.12s
% Output     : Saturation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 743 expanded)
%              Number of clauses        :   55 ( 350 expanded)
%              Number of leaves         :   10 ( 188 expanded)
%              Depth                    :    9
%              Number of atoms          :  209 (1786 expanded)
%              Number of equality atoms :   86 ( 810 expanded)
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

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

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
    ! [X10] : k4_xboole_0(X10,k1_xboole_0) = X10 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

fof(c_0_18,plain,(
    ! [X18,X19] :
      ( ~ l1_struct_0(X18)
      | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))
      | k7_subset_1(u1_struct_0(X18),k2_struct_0(X18),k7_subset_1(u1_struct_0(X18),k2_struct_0(X18),X19)) = X19 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t22_pre_topc])])])).

cnf(c_0_19,plain,
    ( k7_subset_1(X1,X2,X3) = k5_xboole_0(X2,k3_xboole_0(X2,X3))
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16]),
    [final]).

fof(c_0_20,plain,(
    ! [X11,X12] : k4_xboole_0(X11,k2_xboole_0(X11,X12)) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t46_xboole_1])).

fof(c_0_21,negated_conjecture,(
    ~ ! [X1] :
        ( l1_struct_0(X1)
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( ~ ( X2 != k2_struct_0(X1)
                  & k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2) = k1_xboole_0 )
              & ~ ( k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2) != k1_xboole_0
                  & X2 = k2_struct_0(X1) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t23_pre_topc])).

cnf(c_0_22,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_23,plain,(
    ! [X9] : k3_xboole_0(X9,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

cnf(c_0_24,plain,
    ( k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2)) = X2
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_18]),
    [final]).

cnf(c_0_25,plain,
    ( k7_subset_1(X1,X2,X3) = k7_subset_1(X4,X2,X3)
    | ~ r1_tarski(X2,X1)
    | ~ r1_tarski(X2,X4) ),
    inference(spm,[status(thm)],[c_0_19,c_0_19]),
    [final]).

cnf(c_0_26,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_27,negated_conjecture,
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
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_21])])])])).

cnf(c_0_28,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0)) = X1 ),
    inference(rw,[status(thm)],[c_0_22,c_0_13])).

cnf(c_0_29,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_23]),
    [final]).

cnf(c_0_30,plain,
    ( k7_subset_1(X1,k2_struct_0(X2),k7_subset_1(u1_struct_0(X2),k2_struct_0(X2),X3)) = X3
    | ~ l1_struct_0(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r1_tarski(k2_struct_0(X2),u1_struct_0(X2))
    | ~ r1_tarski(k2_struct_0(X2),X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25]),
    [final]).

cnf(c_0_31,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k2_xboole_0(X1,X2))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_26,c_0_13]),
    [final]).

cnf(c_0_32,negated_conjecture,
    ( esk2_0 = k2_struct_0(esk1_0)
    | k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_27]),
    [final]).

cnf(c_0_33,negated_conjecture,
    ( l1_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27]),
    [final]).

cnf(c_0_34,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_27]),
    [final]).

cnf(c_0_35,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[c_0_28,c_0_29]),
    [final]).

fof(c_0_36,plain,(
    ! [X8] : k2_xboole_0(X8,k1_xboole_0) = X8 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

cnf(c_0_37,plain,
    ( k7_subset_1(X1,k2_struct_0(X2),k7_subset_1(X3,k2_struct_0(X2),X4)) = X4
    | ~ l1_struct_0(X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r1_tarski(k2_struct_0(X2),u1_struct_0(X2))
    | ~ r1_tarski(k2_struct_0(X2),X1)
    | ~ r1_tarski(k2_struct_0(X2),X3) ),
    inference(spm,[status(thm)],[c_0_30,c_0_25]),
    [final]).

cnf(c_0_38,plain,
    ( k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(X2,k2_struct_0(X1),X3)) = X3
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(k2_struct_0(X1),u1_struct_0(X1))
    | ~ r1_tarski(k2_struct_0(X1),X2) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25]),
    [final]).

cnf(c_0_39,plain,
    ( k7_subset_1(X1,X2,k2_xboole_0(X2,X3)) = k1_xboole_0
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_19]),
    [final]).

cnf(c_0_40,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),k1_xboole_0) = esk2_0
    | k2_struct_0(esk1_0) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_32]),c_0_33]),c_0_34])]),
    [final]).

cnf(c_0_41,plain,
    ( k7_subset_1(X1,X2,k1_xboole_0) = X2
    | ~ r1_tarski(X2,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_29]),c_0_35]),
    [final]).

cnf(c_0_42,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_36]),
    [final]).

fof(c_0_43,plain,(
    ! [X4,X5] :
      ( ( r1_tarski(X4,X5)
        | X4 != X5 )
      & ( r1_tarski(X5,X4)
        | X4 != X5 )
      & ( ~ r1_tarski(X4,X5)
        | ~ r1_tarski(X5,X4)
        | X4 = X5 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_44,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_14]),
    [final]).

cnf(c_0_45,plain,
    ( k7_subset_1(X1,k2_struct_0(X2),k5_xboole_0(k2_struct_0(X2),k3_xboole_0(k2_struct_0(X2),X3))) = X3
    | ~ l1_struct_0(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r1_tarski(k2_struct_0(X2),u1_struct_0(X2))
    | ~ r1_tarski(k2_struct_0(X2),X1)
    | ~ r1_tarski(k2_struct_0(X2),X4) ),
    inference(spm,[status(thm)],[c_0_37,c_0_19]),
    [final]).

cnf(c_0_46,plain,
    ( k5_xboole_0(k2_struct_0(X1),k3_xboole_0(k2_struct_0(X1),k7_subset_1(X2,k2_struct_0(X1),X3))) = X3
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(k2_struct_0(X1),u1_struct_0(X1))
    | ~ r1_tarski(k2_struct_0(X1),X4)
    | ~ r1_tarski(k2_struct_0(X1),X2) ),
    inference(spm,[status(thm)],[c_0_19,c_0_37]),
    [final]).

cnf(c_0_47,plain,
    ( k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k5_xboole_0(k2_struct_0(X1),k3_xboole_0(k2_struct_0(X1),X2))) = X2
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(k2_struct_0(X1),u1_struct_0(X1))
    | ~ r1_tarski(k2_struct_0(X1),X3) ),
    inference(spm,[status(thm)],[c_0_38,c_0_19]),
    [final]).

cnf(c_0_48,plain,
    ( k5_xboole_0(k2_struct_0(X1),k3_xboole_0(k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2))) = X2
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(k2_struct_0(X1),u1_struct_0(X1))
    | ~ r1_tarski(k2_struct_0(X1),X3) ),
    inference(spm,[status(thm)],[c_0_19,c_0_30]),
    [final]).

cnf(c_0_49,plain,
    ( k7_subset_1(X1,k2_struct_0(X2),k1_xboole_0) = k2_xboole_0(k2_struct_0(X2),X3)
    | ~ l1_struct_0(X2)
    | ~ m1_subset_1(k2_xboole_0(k2_struct_0(X2),X3),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r1_tarski(k2_struct_0(X2),u1_struct_0(X2))
    | ~ r1_tarski(k2_struct_0(X2),X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_39]),
    [final]).

cnf(c_0_50,plain,
    ( k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k1_xboole_0) = k2_xboole_0(k2_struct_0(X1),X2)
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(k2_xboole_0(k2_struct_0(X1),X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(k2_struct_0(X1),u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_39]),
    [final]).

cnf(c_0_51,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0) != k1_xboole_0
    | esk2_0 != k2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27]),
    [final]).

cnf(c_0_52,negated_conjecture,
    ( k2_struct_0(esk1_0) = esk2_0
    | ~ r1_tarski(k2_struct_0(esk1_0),u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41]),
    [final]).

cnf(c_0_53,negated_conjecture,
    ( k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,X1)) = k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_15,c_0_34]),
    [final]).

cnf(c_0_54,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X1)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_31,c_0_42]),
    [final]).

cnf(c_0_55,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43]),
    [final]).

cnf(c_0_56,negated_conjecture,
    ( r1_tarski(esk2_0,u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_34]),
    [final]).

cnf(c_0_57,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_58,plain,
    ( k7_subset_1(X1,k2_struct_0(X2),k5_xboole_0(k2_struct_0(X2),k3_xboole_0(k2_struct_0(X2),X3))) = X3
    | ~ l1_struct_0(X2)
    | ~ r1_tarski(k2_struct_0(X2),u1_struct_0(X2))
    | ~ r1_tarski(k2_struct_0(X2),X1)
    | ~ r1_tarski(k2_struct_0(X2),X4)
    | ~ r1_tarski(X3,u1_struct_0(X2)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_16]),
    [final]).

cnf(c_0_59,plain,
    ( k5_xboole_0(k2_struct_0(X1),k3_xboole_0(k2_struct_0(X1),k7_subset_1(X2,k2_struct_0(X1),X3))) = X3
    | ~ l1_struct_0(X1)
    | ~ r1_tarski(k2_struct_0(X1),u1_struct_0(X1))
    | ~ r1_tarski(k2_struct_0(X1),X4)
    | ~ r1_tarski(k2_struct_0(X1),X2)
    | ~ r1_tarski(X3,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_16]),
    [final]).

cnf(c_0_60,negated_conjecture,
    ( k7_subset_1(X1,k2_struct_0(esk1_0),k5_xboole_0(k2_struct_0(esk1_0),k3_xboole_0(k2_struct_0(esk1_0),esk2_0))) = esk2_0
    | ~ r1_tarski(k2_struct_0(esk1_0),u1_struct_0(esk1_0))
    | ~ r1_tarski(k2_struct_0(esk1_0),X1)
    | ~ r1_tarski(k2_struct_0(esk1_0),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_34]),c_0_33])]),
    [final]).

cnf(c_0_61,negated_conjecture,
    ( k5_xboole_0(k2_struct_0(esk1_0),k3_xboole_0(k2_struct_0(esk1_0),k7_subset_1(X1,k2_struct_0(esk1_0),esk2_0))) = esk2_0
    | ~ r1_tarski(k2_struct_0(esk1_0),u1_struct_0(esk1_0))
    | ~ r1_tarski(k2_struct_0(esk1_0),X2)
    | ~ r1_tarski(k2_struct_0(esk1_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_34]),c_0_33])]),
    [final]).

cnf(c_0_62,plain,
    ( k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k5_xboole_0(k2_struct_0(X1),k3_xboole_0(k2_struct_0(X1),X2))) = X2
    | ~ l1_struct_0(X1)
    | ~ r1_tarski(k2_struct_0(X1),u1_struct_0(X1))
    | ~ r1_tarski(k2_struct_0(X1),X3)
    | ~ r1_tarski(X2,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_16]),
    [final]).

cnf(c_0_63,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),k5_xboole_0(k2_struct_0(esk1_0),k3_xboole_0(k2_struct_0(esk1_0),esk2_0))) = esk2_0
    | ~ r1_tarski(k2_struct_0(esk1_0),u1_struct_0(esk1_0))
    | ~ r1_tarski(k2_struct_0(esk1_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_34]),c_0_33])]),
    [final]).

cnf(c_0_64,plain,
    ( k5_xboole_0(k2_struct_0(X1),k3_xboole_0(k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2))) = X2
    | ~ l1_struct_0(X1)
    | ~ r1_tarski(k2_struct_0(X1),u1_struct_0(X1))
    | ~ r1_tarski(k2_struct_0(X1),X3)
    | ~ r1_tarski(X2,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_16]),
    [final]).

cnf(c_0_65,plain,
    ( k7_subset_1(X1,k2_struct_0(X2),k1_xboole_0) = k2_xboole_0(k2_struct_0(X2),X3)
    | ~ l1_struct_0(X2)
    | ~ r1_tarski(k2_xboole_0(k2_struct_0(X2),X3),u1_struct_0(X2))
    | ~ r1_tarski(k2_struct_0(X2),u1_struct_0(X2))
    | ~ r1_tarski(k2_struct_0(X2),X1) ),
    inference(spm,[status(thm)],[c_0_49,c_0_16]),
    [final]).

cnf(c_0_66,negated_conjecture,
    ( k5_xboole_0(k2_struct_0(esk1_0),k3_xboole_0(k2_struct_0(esk1_0),k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0))) = esk2_0
    | ~ r1_tarski(k2_struct_0(esk1_0),u1_struct_0(esk1_0))
    | ~ r1_tarski(k2_struct_0(esk1_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_34]),c_0_33])]),
    [final]).

cnf(c_0_67,plain,
    ( k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k1_xboole_0) = k2_xboole_0(k2_struct_0(X1),X2)
    | ~ l1_struct_0(X1)
    | ~ r1_tarski(k2_xboole_0(k2_struct_0(X1),X2),u1_struct_0(X1))
    | ~ r1_tarski(k2_struct_0(X1),u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_16]),
    [final]).

cnf(c_0_68,negated_conjecture,
    ( k7_subset_1(X1,k2_struct_0(esk1_0),esk2_0) != k1_xboole_0
    | ~ r1_tarski(k2_struct_0(esk1_0),u1_struct_0(esk1_0))
    | ~ r1_tarski(k2_struct_0(esk1_0),X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_25]),c_0_52]),
    [final]).

cnf(c_0_69,negated_conjecture,
    ( k7_subset_1(X1,esk2_0,X2) = k7_subset_1(u1_struct_0(esk1_0),esk2_0,X2)
    | ~ r1_tarski(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_53,c_0_19]),
    [final]).

cnf(c_0_70,plain,
    ( k7_subset_1(X1,X2,X2) = k1_xboole_0
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_54,c_0_19]),
    [final]).

cnf(c_0_71,negated_conjecture,
    ( u1_struct_0(esk1_0) = esk2_0
    | ~ r1_tarski(u1_struct_0(esk1_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56]),
    [final]).

cnf(c_0_72,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),esk2_0,k2_xboole_0(esk2_0,X1)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_31,c_0_53]),
    [final]).

cnf(c_0_73,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),esk2_0,k1_xboole_0) = esk2_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_29]),c_0_35]),
    [final]).

cnf(c_0_74,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),esk2_0,esk2_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_54,c_0_53]),
    [final]).

cnf(c_0_75,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_57]),
    [final]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:50:39 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.12/0.37  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.12/0.37  #
% 0.12/0.37  # Preprocessing time       : 0.027 s
% 0.12/0.37  # Presaturation interreduction done
% 0.12/0.37  
% 0.12/0.37  # No proof found!
% 0.12/0.37  # SZS status CounterSatisfiable
% 0.12/0.37  # SZS output start Saturation
% 0.12/0.37  fof(redefinition_k7_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k7_subset_1(X1,X2,X3)=k4_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 0.12/0.37  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.12/0.37  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.12/0.37  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 0.12/0.37  fof(t22_pre_topc, axiom, ![X1]:(l1_struct_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2))=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_pre_topc)).
% 0.12/0.37  fof(t46_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 0.12/0.37  fof(t23_pre_topc, conjecture, ![X1]:(l1_struct_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(~((X2!=k2_struct_0(X1)&k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2)=k1_xboole_0))&~((k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2)!=k1_xboole_0&X2=k2_struct_0(X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_pre_topc)).
% 0.12/0.37  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 0.12/0.37  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 0.12/0.37  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.12/0.37  fof(c_0_10, plain, ![X13, X14, X15]:(~m1_subset_1(X14,k1_zfmisc_1(X13))|k7_subset_1(X13,X14,X15)=k4_xboole_0(X14,X15)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).
% 0.12/0.37  fof(c_0_11, plain, ![X6, X7]:k4_xboole_0(X6,X7)=k5_xboole_0(X6,k3_xboole_0(X6,X7)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.12/0.37  cnf(c_0_12, plain, (k7_subset_1(X2,X1,X3)=k4_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.37  cnf(c_0_13, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.37  fof(c_0_14, plain, ![X16, X17]:((~m1_subset_1(X16,k1_zfmisc_1(X17))|r1_tarski(X16,X17))&(~r1_tarski(X16,X17)|m1_subset_1(X16,k1_zfmisc_1(X17)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.12/0.37  cnf(c_0_15, plain, (k7_subset_1(X2,X1,X3)=k5_xboole_0(X1,k3_xboole_0(X1,X3))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_12, c_0_13]), ['final']).
% 0.12/0.37  cnf(c_0_16, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14]), ['final']).
% 0.12/0.37  fof(c_0_17, plain, ![X10]:k4_xboole_0(X10,k1_xboole_0)=X10, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.12/0.37  fof(c_0_18, plain, ![X18, X19]:(~l1_struct_0(X18)|(~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))|k7_subset_1(u1_struct_0(X18),k2_struct_0(X18),k7_subset_1(u1_struct_0(X18),k2_struct_0(X18),X19))=X19)), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t22_pre_topc])])])).
% 0.12/0.37  cnf(c_0_19, plain, (k7_subset_1(X1,X2,X3)=k5_xboole_0(X2,k3_xboole_0(X2,X3))|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_15, c_0_16]), ['final']).
% 0.12/0.37  fof(c_0_20, plain, ![X11, X12]:k4_xboole_0(X11,k2_xboole_0(X11,X12))=k1_xboole_0, inference(variable_rename,[status(thm)],[t46_xboole_1])).
% 0.12/0.37  fof(c_0_21, negated_conjecture, ~(![X1]:(l1_struct_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(~((X2!=k2_struct_0(X1)&k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2)=k1_xboole_0))&~((k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2)!=k1_xboole_0&X2=k2_struct_0(X1))))))), inference(assume_negation,[status(cth)],[t23_pre_topc])).
% 0.12/0.37  cnf(c_0_22, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.12/0.37  fof(c_0_23, plain, ![X9]:k3_xboole_0(X9,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 0.12/0.37  cnf(c_0_24, plain, (k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2))=X2|~l1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_18]), ['final']).
% 0.12/0.37  cnf(c_0_25, plain, (k7_subset_1(X1,X2,X3)=k7_subset_1(X4,X2,X3)|~r1_tarski(X2,X1)|~r1_tarski(X2,X4)), inference(spm,[status(thm)],[c_0_19, c_0_19]), ['final']).
% 0.12/0.37  cnf(c_0_26, plain, (k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.12/0.37  fof(c_0_27, negated_conjecture, (l1_struct_0(esk1_0)&(m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&(((k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)!=k1_xboole_0|esk2_0!=k2_struct_0(esk1_0))&(esk2_0=k2_struct_0(esk1_0)|esk2_0!=k2_struct_0(esk1_0)))&((k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)!=k1_xboole_0|k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)=k1_xboole_0)&(esk2_0=k2_struct_0(esk1_0)|k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)=k1_xboole_0))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_21])])])])).
% 0.12/0.37  cnf(c_0_28, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0))=X1), inference(rw,[status(thm)],[c_0_22, c_0_13])).
% 0.12/0.37  cnf(c_0_29, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_23]), ['final']).
% 0.12/0.37  cnf(c_0_30, plain, (k7_subset_1(X1,k2_struct_0(X2),k7_subset_1(u1_struct_0(X2),k2_struct_0(X2),X3))=X3|~l1_struct_0(X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~r1_tarski(k2_struct_0(X2),u1_struct_0(X2))|~r1_tarski(k2_struct_0(X2),X1)), inference(spm,[status(thm)],[c_0_24, c_0_25]), ['final']).
% 0.12/0.37  cnf(c_0_31, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k2_xboole_0(X1,X2)))=k1_xboole_0), inference(rw,[status(thm)],[c_0_26, c_0_13]), ['final']).
% 0.12/0.37  cnf(c_0_32, negated_conjecture, (esk2_0=k2_struct_0(esk1_0)|k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_27]), ['final']).
% 0.12/0.37  cnf(c_0_33, negated_conjecture, (l1_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_27]), ['final']).
% 0.12/0.37  cnf(c_0_34, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_27]), ['final']).
% 0.12/0.37  cnf(c_0_35, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[c_0_28, c_0_29]), ['final']).
% 0.12/0.37  fof(c_0_36, plain, ![X8]:k2_xboole_0(X8,k1_xboole_0)=X8, inference(variable_rename,[status(thm)],[t1_boole])).
% 0.12/0.37  cnf(c_0_37, plain, (k7_subset_1(X1,k2_struct_0(X2),k7_subset_1(X3,k2_struct_0(X2),X4))=X4|~l1_struct_0(X2)|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))|~r1_tarski(k2_struct_0(X2),u1_struct_0(X2))|~r1_tarski(k2_struct_0(X2),X1)|~r1_tarski(k2_struct_0(X2),X3)), inference(spm,[status(thm)],[c_0_30, c_0_25]), ['final']).
% 0.12/0.37  cnf(c_0_38, plain, (k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(X2,k2_struct_0(X1),X3))=X3|~l1_struct_0(X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(k2_struct_0(X1),u1_struct_0(X1))|~r1_tarski(k2_struct_0(X1),X2)), inference(spm,[status(thm)],[c_0_24, c_0_25]), ['final']).
% 0.12/0.37  cnf(c_0_39, plain, (k7_subset_1(X1,X2,k2_xboole_0(X2,X3))=k1_xboole_0|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_31, c_0_19]), ['final']).
% 0.12/0.37  cnf(c_0_40, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),k1_xboole_0)=esk2_0|k2_struct_0(esk1_0)=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_32]), c_0_33]), c_0_34])]), ['final']).
% 0.12/0.37  cnf(c_0_41, plain, (k7_subset_1(X1,X2,k1_xboole_0)=X2|~r1_tarski(X2,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_29]), c_0_35]), ['final']).
% 0.12/0.37  cnf(c_0_42, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_36]), ['final']).
% 0.12/0.37  fof(c_0_43, plain, ![X4, X5]:(((r1_tarski(X4,X5)|X4!=X5)&(r1_tarski(X5,X4)|X4!=X5))&(~r1_tarski(X4,X5)|~r1_tarski(X5,X4)|X4=X5)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.12/0.37  cnf(c_0_44, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_14]), ['final']).
% 0.12/0.37  cnf(c_0_45, plain, (k7_subset_1(X1,k2_struct_0(X2),k5_xboole_0(k2_struct_0(X2),k3_xboole_0(k2_struct_0(X2),X3)))=X3|~l1_struct_0(X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~r1_tarski(k2_struct_0(X2),u1_struct_0(X2))|~r1_tarski(k2_struct_0(X2),X1)|~r1_tarski(k2_struct_0(X2),X4)), inference(spm,[status(thm)],[c_0_37, c_0_19]), ['final']).
% 0.12/0.37  cnf(c_0_46, plain, (k5_xboole_0(k2_struct_0(X1),k3_xboole_0(k2_struct_0(X1),k7_subset_1(X2,k2_struct_0(X1),X3)))=X3|~l1_struct_0(X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(k2_struct_0(X1),u1_struct_0(X1))|~r1_tarski(k2_struct_0(X1),X4)|~r1_tarski(k2_struct_0(X1),X2)), inference(spm,[status(thm)],[c_0_19, c_0_37]), ['final']).
% 0.12/0.37  cnf(c_0_47, plain, (k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k5_xboole_0(k2_struct_0(X1),k3_xboole_0(k2_struct_0(X1),X2)))=X2|~l1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(k2_struct_0(X1),u1_struct_0(X1))|~r1_tarski(k2_struct_0(X1),X3)), inference(spm,[status(thm)],[c_0_38, c_0_19]), ['final']).
% 0.12/0.37  cnf(c_0_48, plain, (k5_xboole_0(k2_struct_0(X1),k3_xboole_0(k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2)))=X2|~l1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(k2_struct_0(X1),u1_struct_0(X1))|~r1_tarski(k2_struct_0(X1),X3)), inference(spm,[status(thm)],[c_0_19, c_0_30]), ['final']).
% 0.12/0.37  cnf(c_0_49, plain, (k7_subset_1(X1,k2_struct_0(X2),k1_xboole_0)=k2_xboole_0(k2_struct_0(X2),X3)|~l1_struct_0(X2)|~m1_subset_1(k2_xboole_0(k2_struct_0(X2),X3),k1_zfmisc_1(u1_struct_0(X2)))|~r1_tarski(k2_struct_0(X2),u1_struct_0(X2))|~r1_tarski(k2_struct_0(X2),X1)), inference(spm,[status(thm)],[c_0_30, c_0_39]), ['final']).
% 0.12/0.37  cnf(c_0_50, plain, (k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k1_xboole_0)=k2_xboole_0(k2_struct_0(X1),X2)|~l1_struct_0(X1)|~m1_subset_1(k2_xboole_0(k2_struct_0(X1),X2),k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(k2_struct_0(X1),u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_24, c_0_39]), ['final']).
% 0.12/0.37  cnf(c_0_51, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)!=k1_xboole_0|esk2_0!=k2_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_27]), ['final']).
% 0.12/0.37  cnf(c_0_52, negated_conjecture, (k2_struct_0(esk1_0)=esk2_0|~r1_tarski(k2_struct_0(esk1_0),u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_40, c_0_41]), ['final']).
% 0.12/0.37  cnf(c_0_53, negated_conjecture, (k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,X1))=k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1)), inference(spm,[status(thm)],[c_0_15, c_0_34]), ['final']).
% 0.12/0.37  cnf(c_0_54, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X1))=k1_xboole_0), inference(spm,[status(thm)],[c_0_31, c_0_42]), ['final']).
% 0.12/0.37  cnf(c_0_55, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_43]), ['final']).
% 0.12/0.37  cnf(c_0_56, negated_conjecture, (r1_tarski(esk2_0,u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_44, c_0_34]), ['final']).
% 0.12/0.37  cnf(c_0_57, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.12/0.37  cnf(c_0_58, plain, (k7_subset_1(X1,k2_struct_0(X2),k5_xboole_0(k2_struct_0(X2),k3_xboole_0(k2_struct_0(X2),X3)))=X3|~l1_struct_0(X2)|~r1_tarski(k2_struct_0(X2),u1_struct_0(X2))|~r1_tarski(k2_struct_0(X2),X1)|~r1_tarski(k2_struct_0(X2),X4)|~r1_tarski(X3,u1_struct_0(X2))), inference(spm,[status(thm)],[c_0_45, c_0_16]), ['final']).
% 0.12/0.37  cnf(c_0_59, plain, (k5_xboole_0(k2_struct_0(X1),k3_xboole_0(k2_struct_0(X1),k7_subset_1(X2,k2_struct_0(X1),X3)))=X3|~l1_struct_0(X1)|~r1_tarski(k2_struct_0(X1),u1_struct_0(X1))|~r1_tarski(k2_struct_0(X1),X4)|~r1_tarski(k2_struct_0(X1),X2)|~r1_tarski(X3,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_46, c_0_16]), ['final']).
% 0.12/0.37  cnf(c_0_60, negated_conjecture, (k7_subset_1(X1,k2_struct_0(esk1_0),k5_xboole_0(k2_struct_0(esk1_0),k3_xboole_0(k2_struct_0(esk1_0),esk2_0)))=esk2_0|~r1_tarski(k2_struct_0(esk1_0),u1_struct_0(esk1_0))|~r1_tarski(k2_struct_0(esk1_0),X1)|~r1_tarski(k2_struct_0(esk1_0),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_34]), c_0_33])]), ['final']).
% 0.12/0.37  cnf(c_0_61, negated_conjecture, (k5_xboole_0(k2_struct_0(esk1_0),k3_xboole_0(k2_struct_0(esk1_0),k7_subset_1(X1,k2_struct_0(esk1_0),esk2_0)))=esk2_0|~r1_tarski(k2_struct_0(esk1_0),u1_struct_0(esk1_0))|~r1_tarski(k2_struct_0(esk1_0),X2)|~r1_tarski(k2_struct_0(esk1_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_34]), c_0_33])]), ['final']).
% 0.12/0.37  cnf(c_0_62, plain, (k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k5_xboole_0(k2_struct_0(X1),k3_xboole_0(k2_struct_0(X1),X2)))=X2|~l1_struct_0(X1)|~r1_tarski(k2_struct_0(X1),u1_struct_0(X1))|~r1_tarski(k2_struct_0(X1),X3)|~r1_tarski(X2,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_47, c_0_16]), ['final']).
% 0.12/0.37  cnf(c_0_63, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),k5_xboole_0(k2_struct_0(esk1_0),k3_xboole_0(k2_struct_0(esk1_0),esk2_0)))=esk2_0|~r1_tarski(k2_struct_0(esk1_0),u1_struct_0(esk1_0))|~r1_tarski(k2_struct_0(esk1_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_34]), c_0_33])]), ['final']).
% 0.12/0.37  cnf(c_0_64, plain, (k5_xboole_0(k2_struct_0(X1),k3_xboole_0(k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2)))=X2|~l1_struct_0(X1)|~r1_tarski(k2_struct_0(X1),u1_struct_0(X1))|~r1_tarski(k2_struct_0(X1),X3)|~r1_tarski(X2,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_48, c_0_16]), ['final']).
% 0.12/0.37  cnf(c_0_65, plain, (k7_subset_1(X1,k2_struct_0(X2),k1_xboole_0)=k2_xboole_0(k2_struct_0(X2),X3)|~l1_struct_0(X2)|~r1_tarski(k2_xboole_0(k2_struct_0(X2),X3),u1_struct_0(X2))|~r1_tarski(k2_struct_0(X2),u1_struct_0(X2))|~r1_tarski(k2_struct_0(X2),X1)), inference(spm,[status(thm)],[c_0_49, c_0_16]), ['final']).
% 0.12/0.37  cnf(c_0_66, negated_conjecture, (k5_xboole_0(k2_struct_0(esk1_0),k3_xboole_0(k2_struct_0(esk1_0),k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)))=esk2_0|~r1_tarski(k2_struct_0(esk1_0),u1_struct_0(esk1_0))|~r1_tarski(k2_struct_0(esk1_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_34]), c_0_33])]), ['final']).
% 0.12/0.37  cnf(c_0_67, plain, (k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k1_xboole_0)=k2_xboole_0(k2_struct_0(X1),X2)|~l1_struct_0(X1)|~r1_tarski(k2_xboole_0(k2_struct_0(X1),X2),u1_struct_0(X1))|~r1_tarski(k2_struct_0(X1),u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_50, c_0_16]), ['final']).
% 0.12/0.37  cnf(c_0_68, negated_conjecture, (k7_subset_1(X1,k2_struct_0(esk1_0),esk2_0)!=k1_xboole_0|~r1_tarski(k2_struct_0(esk1_0),u1_struct_0(esk1_0))|~r1_tarski(k2_struct_0(esk1_0),X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_25]), c_0_52]), ['final']).
% 0.12/0.37  cnf(c_0_69, negated_conjecture, (k7_subset_1(X1,esk2_0,X2)=k7_subset_1(u1_struct_0(esk1_0),esk2_0,X2)|~r1_tarski(esk2_0,X1)), inference(spm,[status(thm)],[c_0_53, c_0_19]), ['final']).
% 0.12/0.37  cnf(c_0_70, plain, (k7_subset_1(X1,X2,X2)=k1_xboole_0|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_54, c_0_19]), ['final']).
% 0.12/0.37  cnf(c_0_71, negated_conjecture, (u1_struct_0(esk1_0)=esk2_0|~r1_tarski(u1_struct_0(esk1_0),esk2_0)), inference(spm,[status(thm)],[c_0_55, c_0_56]), ['final']).
% 0.12/0.37  cnf(c_0_72, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),esk2_0,k2_xboole_0(esk2_0,X1))=k1_xboole_0), inference(spm,[status(thm)],[c_0_31, c_0_53]), ['final']).
% 0.12/0.37  cnf(c_0_73, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),esk2_0,k1_xboole_0)=esk2_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_29]), c_0_35]), ['final']).
% 0.12/0.37  cnf(c_0_74, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),esk2_0,esk2_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_54, c_0_53]), ['final']).
% 0.12/0.37  cnf(c_0_75, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_57]), ['final']).
% 0.12/0.37  # SZS output end Saturation
% 0.12/0.37  # Proof object total steps             : 76
% 0.12/0.37  # Proof object clause steps            : 55
% 0.12/0.37  # Proof object formula steps           : 21
% 0.12/0.37  # Proof object conjectures             : 21
% 0.12/0.37  # Proof object clause conjectures      : 18
% 0.12/0.37  # Proof object formula conjectures     : 3
% 0.12/0.37  # Proof object initial clauses used    : 15
% 0.12/0.37  # Proof object initial formulas used   : 10
% 0.12/0.37  # Proof object generating inferences   : 35
% 0.12/0.37  # Proof object simplifying inferences  : 19
% 0.12/0.37  # Parsed axioms                        : 10
% 0.12/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.37  # Initial clauses                      : 18
% 0.12/0.37  # Removed in clause preprocessing      : 3
% 0.12/0.37  # Initial clauses in saturation        : 15
% 0.12/0.37  # Processed clauses                    : 148
% 0.12/0.37  # ...of these trivial                  : 0
% 0.12/0.37  # ...subsumed                          : 83
% 0.12/0.37  # ...remaining for further processing  : 65
% 0.12/0.37  # Other redundant clauses eliminated   : 2
% 0.12/0.37  # Clauses deleted for lack of memory   : 0
% 0.12/0.37  # Backward-subsumed                    : 0
% 0.12/0.37  # Backward-rewritten                   : 0
% 0.12/0.37  # Generated clauses                    : 134
% 0.12/0.37  # ...of the previous two non-trivial   : 119
% 0.12/0.37  # Contextual simplify-reflections      : 1
% 0.12/0.37  # Paramodulations                      : 132
% 0.12/0.37  # Factorizations                       : 0
% 0.12/0.37  # Equation resolutions                 : 2
% 0.12/0.37  # Propositional unsat checks           : 0
% 0.12/0.37  #    Propositional check models        : 0
% 0.12/0.37  #    Propositional check unsatisfiable : 0
% 0.12/0.37  #    Propositional clauses             : 0
% 0.12/0.37  #    Propositional clauses after purity: 0
% 0.12/0.37  #    Propositional unsat core size     : 0
% 0.12/0.37  #    Propositional preprocessing time  : 0.000
% 0.12/0.37  #    Propositional encoding time       : 0.000
% 0.12/0.37  #    Propositional solver time         : 0.000
% 0.12/0.37  #    Success case prop preproc time    : 0.000
% 0.12/0.37  #    Success case prop encoding time   : 0.000
% 0.12/0.37  #    Success case prop solver time     : 0.000
% 0.12/0.37  # Current number of processed clauses  : 49
% 0.12/0.37  #    Positive orientable unit clauses  : 13
% 0.12/0.37  #    Positive unorientable unit clauses: 0
% 0.12/0.37  #    Negative unit clauses             : 0
% 0.12/0.37  #    Non-unit-clauses                  : 36
% 0.12/0.37  # Current number of unprocessed clauses: 0
% 0.12/0.37  # ...number of literals in the above   : 0
% 0.12/0.37  # Current number of archived formulas  : 0
% 0.12/0.37  # Current number of archived clauses   : 15
% 0.12/0.37  # Clause-clause subsumption calls (NU) : 711
% 0.12/0.37  # Rec. Clause-clause subsumption calls : 373
% 0.12/0.37  # Non-unit clause-clause subsumptions  : 84
% 0.12/0.37  # Unit Clause-clause subsumption calls : 7
% 0.12/0.37  # Rewrite failures with RHS unbound    : 0
% 0.12/0.37  # BW rewrite match attempts            : 8
% 0.12/0.37  # BW rewrite match successes           : 0
% 0.12/0.37  # Condensation attempts                : 0
% 0.12/0.37  # Condensation successes               : 0
% 0.12/0.37  # Termbank termtop insertions          : 3936
% 0.12/0.37  
% 0.12/0.37  # -------------------------------------------------
% 0.12/0.37  # User time                : 0.032 s
% 0.12/0.37  # System time              : 0.005 s
% 0.12/0.37  # Total time               : 0.037 s
% 0.12/0.37  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
