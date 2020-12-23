%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:08:43 EST 2020

% Result     : CounterSatisfiable 0.19s
% Output     : Saturation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 853 expanded)
%              Number of clauses        :   73 ( 401 expanded)
%              Number of leaves         :   10 ( 221 expanded)
%              Depth                    :    7
%              Number of atoms          :  292 (2061 expanded)
%              Number of equality atoms :   99 ( 762 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(redefinition_k7_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k7_subset_1(X1,X2,X3) = k4_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(t46_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

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

fof(t22_pre_topc,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2)) = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_pre_topc)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(dt_k2_subset_1,axiom,(
    ! [X1] : m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

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
    ! [X16,X17] :
      ( ( ~ m1_subset_1(X16,k1_zfmisc_1(X17))
        | r1_tarski(X16,X17) )
      & ( ~ r1_tarski(X16,X17)
        | m1_subset_1(X16,k1_zfmisc_1(X17)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_12,plain,(
    ! [X9,X10] : k4_xboole_0(X9,k2_xboole_0(X9,X10)) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t46_xboole_1])).

fof(c_0_13,plain,(
    ! [X6,X7] :
      ( ~ r1_tarski(X6,X7)
      | k2_xboole_0(X6,X7) = X7 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1] :
        ( l1_struct_0(X1)
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( ~ ( X2 != k2_struct_0(X1)
                  & k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2) = k1_xboole_0 )
              & ~ ( k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2) != k1_xboole_0
                  & X2 = k2_struct_0(X1) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t23_pre_topc])).

cnf(c_0_15,plain,
    ( k7_subset_1(X2,X1,X3) = k4_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_10]),
    [final]).

cnf(c_0_16,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11]),
    [final]).

cnf(c_0_17,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12]),
    [final]).

cnf(c_0_18,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13]),
    [final]).

fof(c_0_19,plain,(
    ! [X18,X19] :
      ( ~ l1_struct_0(X18)
      | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))
      | k7_subset_1(u1_struct_0(X18),k2_struct_0(X18),k7_subset_1(u1_struct_0(X18),k2_struct_0(X18),X19)) = X19 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t22_pre_topc])])])).

fof(c_0_20,negated_conjecture,
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
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])])).

cnf(c_0_21,plain,
    ( k7_subset_1(X1,X2,X3) = k4_xboole_0(X2,X3)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16]),
    [final]).

cnf(c_0_22,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18]),
    [final]).

fof(c_0_23,plain,(
    ! [X8] : k4_xboole_0(X8,k1_xboole_0) = X8 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

fof(c_0_24,plain,(
    ! [X12] : m1_subset_1(k2_subset_1(X12),k1_zfmisc_1(X12)) ),
    inference(variable_rename,[status(thm)],[dt_k2_subset_1])).

fof(c_0_25,plain,(
    ! [X11] : k2_subset_1(X11) = X11 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

cnf(c_0_26,plain,
    ( k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2)) = X2
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_19]),
    [final]).

cnf(c_0_27,negated_conjecture,
    ( esk2_0 = k2_struct_0(esk1_0)
    | k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_20]),
    [final]).

cnf(c_0_28,negated_conjecture,
    ( l1_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20]),
    [final]).

cnf(c_0_29,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_20]),
    [final]).

cnf(c_0_30,plain,
    ( k7_subset_1(X1,X2,X3) = k7_subset_1(X4,X2,X3)
    | ~ r1_tarski(X2,X1)
    | ~ r1_tarski(X2,X4) ),
    inference(spm,[status(thm)],[c_0_21,c_0_21]),
    [final]).

cnf(c_0_31,plain,
    ( k7_subset_1(X1,X2,X3) = k1_xboole_0
    | ~ r1_tarski(X2,X3)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_21]),
    [final]).

cnf(c_0_32,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_23]),
    [final]).

cnf(c_0_33,plain,
    ( m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_34,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_35,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),k1_xboole_0) = esk2_0
    | k2_struct_0(esk1_0) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28]),c_0_29])]),
    [final]).

cnf(c_0_36,plain,
    ( k7_subset_1(X1,k2_struct_0(X2),k7_subset_1(u1_struct_0(X2),k2_struct_0(X2),X3)) = X3
    | ~ l1_struct_0(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r1_tarski(k2_struct_0(X2),u1_struct_0(X2))
    | ~ r1_tarski(k2_struct_0(X2),X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_30]),
    [final]).

cnf(c_0_37,plain,
    ( k7_subset_1(X1,X2,k2_xboole_0(X2,X3)) = k1_xboole_0
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_17,c_0_21]),
    [final]).

cnf(c_0_38,plain,
    ( k1_xboole_0 = X1
    | ~ l1_struct_0(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r1_tarski(k2_struct_0(X2),k7_subset_1(u1_struct_0(X2),k2_struct_0(X2),X1))
    | ~ r1_tarski(k2_struct_0(X2),u1_struct_0(X2)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_31]),
    [final]).

cnf(c_0_39,plain,
    ( k4_xboole_0(k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2)) = X2
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(k2_struct_0(X1),u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_21]),
    [final]).

cnf(c_0_40,plain,
    ( k7_subset_1(X1,X2,k1_xboole_0) = X2
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_32,c_0_21]),
    [final]).

cnf(c_0_41,plain,
    ( k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k1_xboole_0) = X2
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(k2_struct_0(X1),u1_struct_0(X1))
    | ~ r1_tarski(k2_struct_0(X1),X2) ),
    inference(spm,[status(thm)],[c_0_26,c_0_31]),
    [final]).

cnf(c_0_42,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_33,c_0_34]),
    [final]).

cnf(c_0_43,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0) != k1_xboole_0
    | esk2_0 != k2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20]),
    [final]).

cnf(c_0_44,negated_conjecture,
    ( k2_struct_0(esk1_0) = esk2_0
    | ~ r1_tarski(k2_struct_0(esk1_0),u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_21]),c_0_32])]),
    [final]).

fof(c_0_45,plain,(
    ! [X4,X5] :
      ( ( r1_tarski(X4,X5)
        | X4 != X5 )
      & ( r1_tarski(X5,X4)
        | X4 != X5 )
      & ( ~ r1_tarski(X4,X5)
        | ~ r1_tarski(X5,X4)
        | X4 = X5 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_46,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_11]),
    [final]).

cnf(c_0_47,plain,
    ( k7_subset_1(X1,k2_struct_0(X2),k1_xboole_0) = k2_xboole_0(k2_struct_0(X2),X3)
    | ~ l1_struct_0(X2)
    | ~ m1_subset_1(k2_xboole_0(k2_struct_0(X2),X3),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r1_tarski(k2_struct_0(X2),u1_struct_0(X2))
    | ~ r1_tarski(k2_struct_0(X2),X1) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37]),
    [final]).

cnf(c_0_48,plain,
    ( k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k1_xboole_0) = k2_xboole_0(k2_struct_0(X1),X2)
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(k2_xboole_0(k2_struct_0(X1),X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(k2_struct_0(X1),u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_37]),
    [final]).

cnf(c_0_49,plain,
    ( k7_subset_1(X1,k2_struct_0(X2),k1_xboole_0) = X3
    | ~ l1_struct_0(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r1_tarski(k2_struct_0(X2),u1_struct_0(X2))
    | ~ r1_tarski(k2_struct_0(X2),X1)
    | ~ r1_tarski(k2_struct_0(X2),X3) ),
    inference(spm,[status(thm)],[c_0_36,c_0_31]),
    [final]).

cnf(c_0_50,plain,
    ( k2_xboole_0(k2_struct_0(X1),X2) = k1_xboole_0
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(k2_xboole_0(k2_struct_0(X1),X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(k2_struct_0(X1),u1_struct_0(X1))
    | ~ r1_tarski(k2_struct_0(X1),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_37]),
    [final]).

cnf(c_0_51,plain,
    ( k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k4_xboole_0(k2_struct_0(X1),X2)) = X2
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(k2_struct_0(X1),u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_21]),
    [final]).

cnf(c_0_52,plain,
    ( k4_xboole_0(k2_struct_0(X1),k2_struct_0(X1)) = k1_xboole_0
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(k2_struct_0(X1),u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40]),
    [final]).

cnf(c_0_53,plain,
    ( k2_xboole_0(k2_struct_0(X1),X2) = k2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(k2_xboole_0(k2_struct_0(X1),X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(k2_struct_0(X1),u1_struct_0(X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_37]),c_0_32]),
    [final]).

cnf(c_0_54,plain,
    ( k1_xboole_0 = X1
    | ~ l1_struct_0(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r1_tarski(k2_struct_0(X2),u1_struct_0(X2))
    | ~ r1_tarski(k2_struct_0(X2),k1_xboole_0)
    | ~ r1_tarski(k2_struct_0(X2),X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_31]),
    [final]).

cnf(c_0_55,plain,
    ( k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k1_xboole_0) = u1_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ r1_tarski(k2_struct_0(X1),u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42]),
    [final]).

cnf(c_0_56,plain,
    ( k2_struct_0(X1) = X2
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(k2_struct_0(X1),u1_struct_0(X1))
    | ~ r1_tarski(k2_struct_0(X1),X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_31]),c_0_32]),
    [final]).

cnf(c_0_57,plain,
    ( k7_subset_1(X1,X1,X2) = k4_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_15,c_0_42]),
    [final]).

cnf(c_0_58,negated_conjecture,
    ( k4_xboole_0(k2_struct_0(esk1_0),esk2_0) != k1_xboole_0
    | ~ r1_tarski(k2_struct_0(esk1_0),u1_struct_0(esk1_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_21]),c_0_44]),
    [final]).

cnf(c_0_59,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45]),
    [final]).

cnf(c_0_60,negated_conjecture,
    ( r1_tarski(esk2_0,u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_29]),
    [final]).

cnf(c_0_61,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1) = k4_xboole_0(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_15,c_0_29])).

cnf(c_0_62,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_63,plain,
    ( k7_subset_1(X1,k2_struct_0(X2),k7_subset_1(X3,k2_struct_0(X2),X4)) = X4
    | ~ l1_struct_0(X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r1_tarski(k2_struct_0(X2),u1_struct_0(X2))
    | ~ r1_tarski(k2_struct_0(X2),X1)
    | ~ r1_tarski(k2_struct_0(X2),X3) ),
    inference(spm,[status(thm)],[c_0_36,c_0_30]),
    [final]).

cnf(c_0_64,plain,
    ( k7_subset_1(X1,k2_struct_0(X2),k1_xboole_0) = k2_xboole_0(k2_struct_0(X2),X3)
    | ~ l1_struct_0(X2)
    | ~ r1_tarski(k2_xboole_0(k2_struct_0(X2),X3),u1_struct_0(X2))
    | ~ r1_tarski(k2_struct_0(X2),u1_struct_0(X2))
    | ~ r1_tarski(k2_struct_0(X2),X1) ),
    inference(spm,[status(thm)],[c_0_47,c_0_16]),
    [final]).

cnf(c_0_65,plain,
    ( k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k1_xboole_0) = k2_xboole_0(k2_struct_0(X1),X2)
    | ~ l1_struct_0(X1)
    | ~ r1_tarski(k2_xboole_0(k2_struct_0(X1),X2),u1_struct_0(X1))
    | ~ r1_tarski(k2_struct_0(X1),u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_16]),
    [final]).

cnf(c_0_66,plain,
    ( k7_subset_1(X1,k2_struct_0(X2),k1_xboole_0) = X3
    | ~ l1_struct_0(X2)
    | ~ r1_tarski(k2_struct_0(X2),u1_struct_0(X2))
    | ~ r1_tarski(k2_struct_0(X2),X1)
    | ~ r1_tarski(k2_struct_0(X2),X3)
    | ~ r1_tarski(X3,u1_struct_0(X2)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_16]),
    [final]).

cnf(c_0_67,plain,
    ( k2_xboole_0(k2_struct_0(X1),X2) = k1_xboole_0
    | ~ l1_struct_0(X1)
    | ~ r1_tarski(k2_xboole_0(k2_struct_0(X1),X2),u1_struct_0(X1))
    | ~ r1_tarski(k2_struct_0(X1),u1_struct_0(X1))
    | ~ r1_tarski(k2_struct_0(X1),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_16]),
    [final]).

cnf(c_0_68,plain,
    ( k7_subset_1(X1,k2_struct_0(X2),k4_xboole_0(k2_struct_0(X2),X3)) = X3
    | ~ l1_struct_0(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r1_tarski(k2_struct_0(X2),u1_struct_0(X2))
    | ~ r1_tarski(k2_struct_0(X2),X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_51]),
    [final]).

cnf(c_0_69,plain,
    ( k4_xboole_0(k2_struct_0(X1),k7_subset_1(X2,k2_struct_0(X1),X3)) = X3
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(k2_struct_0(X1),u1_struct_0(X1))
    | ~ r1_tarski(k2_struct_0(X1),X2) ),
    inference(spm,[status(thm)],[c_0_39,c_0_30]),
    [final]).

cnf(c_0_70,plain,
    ( k1_xboole_0 = X1
    | ~ l1_struct_0(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r1_tarski(k2_struct_0(X2),k7_subset_1(X3,k2_struct_0(X2),X1))
    | ~ r1_tarski(k2_struct_0(X2),u1_struct_0(X2))
    | ~ r1_tarski(k2_struct_0(X2),X3) ),
    inference(spm,[status(thm)],[c_0_38,c_0_30]),
    [final]).

cnf(c_0_71,plain,
    ( k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k1_xboole_0) = X2
    | ~ l1_struct_0(X1)
    | ~ r1_tarski(k2_struct_0(X1),u1_struct_0(X1))
    | ~ r1_tarski(k2_struct_0(X1),X2)
    | ~ r1_tarski(X2,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_16]),
    [final]).

cnf(c_0_72,plain,
    ( k7_subset_1(X1,k2_struct_0(X2),k2_struct_0(X2)) = k1_xboole_0
    | ~ l1_struct_0(X2)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r1_tarski(k2_struct_0(X2),u1_struct_0(X2))
    | ~ r1_tarski(k2_struct_0(X2),X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_52]),
    [final]).

cnf(c_0_73,plain,
    ( k2_xboole_0(k2_struct_0(X1),X2) = k2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ r1_tarski(k2_xboole_0(k2_struct_0(X1),X2),u1_struct_0(X1))
    | ~ r1_tarski(k2_struct_0(X1),u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_16]),
    [final]).

cnf(c_0_74,plain,
    ( k4_xboole_0(k2_struct_0(X1),k4_xboole_0(k2_struct_0(X1),X2)) = X2
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(k2_struct_0(X1),u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_21]),
    [final]).

cnf(c_0_75,plain,
    ( k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(X2,k2_struct_0(X1),X3)) = X3
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(k2_struct_0(X1),u1_struct_0(X1))
    | ~ r1_tarski(k2_struct_0(X1),X2) ),
    inference(spm,[status(thm)],[c_0_26,c_0_30]),
    [final]).

cnf(c_0_76,plain,
    ( X1 = k1_xboole_0
    | ~ l1_struct_0(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r1_tarski(k2_struct_0(X2),k4_xboole_0(k2_struct_0(X2),X1))
    | ~ r1_tarski(k2_struct_0(X2),u1_struct_0(X2)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_51]),
    [final]).

cnf(c_0_77,plain,
    ( k1_xboole_0 = X1
    | ~ l1_struct_0(X2)
    | ~ r1_tarski(k2_struct_0(X2),u1_struct_0(X2))
    | ~ r1_tarski(k2_struct_0(X2),k1_xboole_0)
    | ~ r1_tarski(k2_struct_0(X2),X1)
    | ~ r1_tarski(X1,u1_struct_0(X2)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_16]),
    [final]).

cnf(c_0_78,plain,
    ( k7_subset_1(X1,k2_struct_0(X2),k1_xboole_0) = u1_struct_0(X2)
    | ~ l1_struct_0(X2)
    | ~ r1_tarski(k2_struct_0(X2),u1_struct_0(X2))
    | ~ r1_tarski(k2_struct_0(X2),X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_55]),
    [final]).

cnf(c_0_79,plain,
    ( k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),u1_struct_0(X1)) = k1_xboole_0
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(k2_struct_0(X1),u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_55]),
    [final]).

cnf(c_0_80,plain,
    ( k2_struct_0(X1) = X2
    | ~ l1_struct_0(X1)
    | ~ r1_tarski(k2_struct_0(X1),u1_struct_0(X1))
    | ~ r1_tarski(k2_struct_0(X1),X2)
    | ~ r1_tarski(X2,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_16]),
    [final]).

cnf(c_0_81,plain,
    ( u1_struct_0(X1) = k1_xboole_0
    | ~ l1_struct_0(X1)
    | ~ r1_tarski(k2_struct_0(X1),u1_struct_0(X1))
    | ~ r1_tarski(k2_struct_0(X1),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_55]),
    [final]).

cnf(c_0_82,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ r1_tarski(k2_struct_0(X1),u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_42]),
    [final]).

cnf(c_0_83,plain,
    ( k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k2_struct_0(X1)) = k1_xboole_0
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(k2_struct_0(X1),u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_40]),
    [final]).

cnf(c_0_84,plain,
    ( k7_subset_1(X1,X1,X2) = k7_subset_1(X3,X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_57,c_0_21]),
    [final]).

cnf(c_0_85,negated_conjecture,
    ( k7_subset_1(X1,k2_struct_0(esk1_0),esk2_0) != k1_xboole_0
    | ~ r1_tarski(k2_struct_0(esk1_0),u1_struct_0(esk1_0))
    | ~ r1_tarski(k2_struct_0(esk1_0),X1) ),
    inference(spm,[status(thm)],[c_0_58,c_0_21]),
    [final]).

cnf(c_0_86,negated_conjecture,
    ( ~ r1_tarski(k2_struct_0(esk1_0),u1_struct_0(esk1_0))
    | ~ r1_tarski(k2_struct_0(esk1_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_58,c_0_22]),
    [final]).

cnf(c_0_87,plain,
    ( k7_subset_1(X1,X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_22,c_0_57]),
    [final]).

cnf(c_0_88,negated_conjecture,
    ( u1_struct_0(esk1_0) = esk2_0
    | ~ r1_tarski(u1_struct_0(esk1_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60]),
    [final]).

cnf(c_0_89,plain,
    ( k1_xboole_0 = X1
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_22]),
    [final]).

cnf(c_0_90,plain,
    ( k7_subset_1(X1,X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_17,c_0_57]),
    [final]).

cnf(c_0_91,plain,
    ( k7_subset_1(X1,X1,k1_xboole_0) = X1 ),
    inference(spm,[status(thm)],[c_0_32,c_0_57]),
    [final]).

cnf(c_0_92,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1) = k7_subset_1(esk2_0,esk2_0,X1) ),
    inference(rw,[status(thm)],[c_0_61,c_0_57]),
    [final]).

cnf(c_0_93,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_62]),
    [final]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n025.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:01:05 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.19/0.39  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.39  #
% 0.19/0.39  # Preprocessing time       : 0.027 s
% 0.19/0.39  # Presaturation interreduction done
% 0.19/0.39  
% 0.19/0.39  # No proof found!
% 0.19/0.39  # SZS status CounterSatisfiable
% 0.19/0.39  # SZS output start Saturation
% 0.19/0.39  fof(redefinition_k7_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k7_subset_1(X1,X2,X3)=k4_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 0.19/0.39  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.19/0.39  fof(t46_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 0.19/0.39  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.19/0.39  fof(t23_pre_topc, conjecture, ![X1]:(l1_struct_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(~((X2!=k2_struct_0(X1)&k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2)=k1_xboole_0))&~((k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2)!=k1_xboole_0&X2=k2_struct_0(X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_pre_topc)).
% 0.19/0.39  fof(t22_pre_topc, axiom, ![X1]:(l1_struct_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2))=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_pre_topc)).
% 0.19/0.39  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 0.19/0.39  fof(dt_k2_subset_1, axiom, ![X1]:m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 0.19/0.39  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 0.19/0.39  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.19/0.39  fof(c_0_10, plain, ![X13, X14, X15]:(~m1_subset_1(X14,k1_zfmisc_1(X13))|k7_subset_1(X13,X14,X15)=k4_xboole_0(X14,X15)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).
% 0.19/0.39  fof(c_0_11, plain, ![X16, X17]:((~m1_subset_1(X16,k1_zfmisc_1(X17))|r1_tarski(X16,X17))&(~r1_tarski(X16,X17)|m1_subset_1(X16,k1_zfmisc_1(X17)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.19/0.39  fof(c_0_12, plain, ![X9, X10]:k4_xboole_0(X9,k2_xboole_0(X9,X10))=k1_xboole_0, inference(variable_rename,[status(thm)],[t46_xboole_1])).
% 0.19/0.39  fof(c_0_13, plain, ![X6, X7]:(~r1_tarski(X6,X7)|k2_xboole_0(X6,X7)=X7), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.19/0.39  fof(c_0_14, negated_conjecture, ~(![X1]:(l1_struct_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(~((X2!=k2_struct_0(X1)&k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2)=k1_xboole_0))&~((k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2)!=k1_xboole_0&X2=k2_struct_0(X1))))))), inference(assume_negation,[status(cth)],[t23_pre_topc])).
% 0.19/0.39  cnf(c_0_15, plain, (k7_subset_1(X2,X1,X3)=k4_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_10]), ['final']).
% 0.19/0.39  cnf(c_0_16, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11]), ['final']).
% 0.19/0.39  cnf(c_0_17, plain, (k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_12]), ['final']).
% 0.19/0.39  cnf(c_0_18, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13]), ['final']).
% 0.19/0.39  fof(c_0_19, plain, ![X18, X19]:(~l1_struct_0(X18)|(~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))|k7_subset_1(u1_struct_0(X18),k2_struct_0(X18),k7_subset_1(u1_struct_0(X18),k2_struct_0(X18),X19))=X19)), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t22_pre_topc])])])).
% 0.19/0.39  fof(c_0_20, negated_conjecture, (l1_struct_0(esk1_0)&(m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&(((k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)!=k1_xboole_0|esk2_0!=k2_struct_0(esk1_0))&(esk2_0=k2_struct_0(esk1_0)|esk2_0!=k2_struct_0(esk1_0)))&((k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)!=k1_xboole_0|k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)=k1_xboole_0)&(esk2_0=k2_struct_0(esk1_0)|k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)=k1_xboole_0))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])])).
% 0.19/0.39  cnf(c_0_21, plain, (k7_subset_1(X1,X2,X3)=k4_xboole_0(X2,X3)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_15, c_0_16]), ['final']).
% 0.19/0.39  cnf(c_0_22, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_17, c_0_18]), ['final']).
% 0.19/0.39  fof(c_0_23, plain, ![X8]:k4_xboole_0(X8,k1_xboole_0)=X8, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.19/0.39  fof(c_0_24, plain, ![X12]:m1_subset_1(k2_subset_1(X12),k1_zfmisc_1(X12)), inference(variable_rename,[status(thm)],[dt_k2_subset_1])).
% 0.19/0.39  fof(c_0_25, plain, ![X11]:k2_subset_1(X11)=X11, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 0.19/0.39  cnf(c_0_26, plain, (k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2))=X2|~l1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_19]), ['final']).
% 0.19/0.39  cnf(c_0_27, negated_conjecture, (esk2_0=k2_struct_0(esk1_0)|k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_20]), ['final']).
% 0.19/0.39  cnf(c_0_28, negated_conjecture, (l1_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_20]), ['final']).
% 0.19/0.39  cnf(c_0_29, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_20]), ['final']).
% 0.19/0.39  cnf(c_0_30, plain, (k7_subset_1(X1,X2,X3)=k7_subset_1(X4,X2,X3)|~r1_tarski(X2,X1)|~r1_tarski(X2,X4)), inference(spm,[status(thm)],[c_0_21, c_0_21]), ['final']).
% 0.19/0.39  cnf(c_0_31, plain, (k7_subset_1(X1,X2,X3)=k1_xboole_0|~r1_tarski(X2,X3)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_22, c_0_21]), ['final']).
% 0.19/0.39  cnf(c_0_32, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_23]), ['final']).
% 0.19/0.39  cnf(c_0_33, plain, (m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.39  cnf(c_0_34, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.39  cnf(c_0_35, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),k1_xboole_0)=esk2_0|k2_struct_0(esk1_0)=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28]), c_0_29])]), ['final']).
% 0.19/0.39  cnf(c_0_36, plain, (k7_subset_1(X1,k2_struct_0(X2),k7_subset_1(u1_struct_0(X2),k2_struct_0(X2),X3))=X3|~l1_struct_0(X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~r1_tarski(k2_struct_0(X2),u1_struct_0(X2))|~r1_tarski(k2_struct_0(X2),X1)), inference(spm,[status(thm)],[c_0_26, c_0_30]), ['final']).
% 0.19/0.39  cnf(c_0_37, plain, (k7_subset_1(X1,X2,k2_xboole_0(X2,X3))=k1_xboole_0|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_17, c_0_21]), ['final']).
% 0.19/0.39  cnf(c_0_38, plain, (k1_xboole_0=X1|~l1_struct_0(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~r1_tarski(k2_struct_0(X2),k7_subset_1(u1_struct_0(X2),k2_struct_0(X2),X1))|~r1_tarski(k2_struct_0(X2),u1_struct_0(X2))), inference(spm,[status(thm)],[c_0_26, c_0_31]), ['final']).
% 0.19/0.39  cnf(c_0_39, plain, (k4_xboole_0(k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2))=X2|~l1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(k2_struct_0(X1),u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_26, c_0_21]), ['final']).
% 0.19/0.39  cnf(c_0_40, plain, (k7_subset_1(X1,X2,k1_xboole_0)=X2|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_32, c_0_21]), ['final']).
% 0.19/0.39  cnf(c_0_41, plain, (k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k1_xboole_0)=X2|~l1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(k2_struct_0(X1),u1_struct_0(X1))|~r1_tarski(k2_struct_0(X1),X2)), inference(spm,[status(thm)],[c_0_26, c_0_31]), ['final']).
% 0.19/0.39  cnf(c_0_42, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_33, c_0_34]), ['final']).
% 0.19/0.39  cnf(c_0_43, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)!=k1_xboole_0|esk2_0!=k2_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_20]), ['final']).
% 0.19/0.39  cnf(c_0_44, negated_conjecture, (k2_struct_0(esk1_0)=esk2_0|~r1_tarski(k2_struct_0(esk1_0),u1_struct_0(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_21]), c_0_32])]), ['final']).
% 0.19/0.39  fof(c_0_45, plain, ![X4, X5]:(((r1_tarski(X4,X5)|X4!=X5)&(r1_tarski(X5,X4)|X4!=X5))&(~r1_tarski(X4,X5)|~r1_tarski(X5,X4)|X4=X5)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.19/0.39  cnf(c_0_46, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_11]), ['final']).
% 0.19/0.39  cnf(c_0_47, plain, (k7_subset_1(X1,k2_struct_0(X2),k1_xboole_0)=k2_xboole_0(k2_struct_0(X2),X3)|~l1_struct_0(X2)|~m1_subset_1(k2_xboole_0(k2_struct_0(X2),X3),k1_zfmisc_1(u1_struct_0(X2)))|~r1_tarski(k2_struct_0(X2),u1_struct_0(X2))|~r1_tarski(k2_struct_0(X2),X1)), inference(spm,[status(thm)],[c_0_36, c_0_37]), ['final']).
% 0.19/0.39  cnf(c_0_48, plain, (k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k1_xboole_0)=k2_xboole_0(k2_struct_0(X1),X2)|~l1_struct_0(X1)|~m1_subset_1(k2_xboole_0(k2_struct_0(X1),X2),k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(k2_struct_0(X1),u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_26, c_0_37]), ['final']).
% 0.19/0.39  cnf(c_0_49, plain, (k7_subset_1(X1,k2_struct_0(X2),k1_xboole_0)=X3|~l1_struct_0(X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~r1_tarski(k2_struct_0(X2),u1_struct_0(X2))|~r1_tarski(k2_struct_0(X2),X1)|~r1_tarski(k2_struct_0(X2),X3)), inference(spm,[status(thm)],[c_0_36, c_0_31]), ['final']).
% 0.19/0.39  cnf(c_0_50, plain, (k2_xboole_0(k2_struct_0(X1),X2)=k1_xboole_0|~l1_struct_0(X1)|~m1_subset_1(k2_xboole_0(k2_struct_0(X1),X2),k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(k2_struct_0(X1),u1_struct_0(X1))|~r1_tarski(k2_struct_0(X1),k1_xboole_0)), inference(spm,[status(thm)],[c_0_38, c_0_37]), ['final']).
% 0.19/0.39  cnf(c_0_51, plain, (k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k4_xboole_0(k2_struct_0(X1),X2))=X2|~l1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(k2_struct_0(X1),u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_26, c_0_21]), ['final']).
% 0.19/0.39  cnf(c_0_52, plain, (k4_xboole_0(k2_struct_0(X1),k2_struct_0(X1))=k1_xboole_0|~l1_struct_0(X1)|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(k2_struct_0(X1),u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_39, c_0_40]), ['final']).
% 0.19/0.39  cnf(c_0_53, plain, (k2_xboole_0(k2_struct_0(X1),X2)=k2_struct_0(X1)|~l1_struct_0(X1)|~m1_subset_1(k2_xboole_0(k2_struct_0(X1),X2),k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(k2_struct_0(X1),u1_struct_0(X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_37]), c_0_32]), ['final']).
% 0.19/0.39  cnf(c_0_54, plain, (k1_xboole_0=X1|~l1_struct_0(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~r1_tarski(k2_struct_0(X2),u1_struct_0(X2))|~r1_tarski(k2_struct_0(X2),k1_xboole_0)|~r1_tarski(k2_struct_0(X2),X1)), inference(spm,[status(thm)],[c_0_38, c_0_31]), ['final']).
% 0.19/0.39  cnf(c_0_55, plain, (k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k1_xboole_0)=u1_struct_0(X1)|~l1_struct_0(X1)|~r1_tarski(k2_struct_0(X1),u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_41, c_0_42]), ['final']).
% 0.19/0.39  cnf(c_0_56, plain, (k2_struct_0(X1)=X2|~l1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(k2_struct_0(X1),u1_struct_0(X1))|~r1_tarski(k2_struct_0(X1),X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_31]), c_0_32]), ['final']).
% 0.19/0.39  cnf(c_0_57, plain, (k7_subset_1(X1,X1,X2)=k4_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_15, c_0_42]), ['final']).
% 0.19/0.39  cnf(c_0_58, negated_conjecture, (k4_xboole_0(k2_struct_0(esk1_0),esk2_0)!=k1_xboole_0|~r1_tarski(k2_struct_0(esk1_0),u1_struct_0(esk1_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_21]), c_0_44]), ['final']).
% 0.19/0.39  cnf(c_0_59, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_45]), ['final']).
% 0.19/0.39  cnf(c_0_60, negated_conjecture, (r1_tarski(esk2_0,u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_46, c_0_29]), ['final']).
% 0.19/0.39  cnf(c_0_61, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1)=k4_xboole_0(esk2_0,X1)), inference(spm,[status(thm)],[c_0_15, c_0_29])).
% 0.19/0.39  cnf(c_0_62, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.19/0.39  cnf(c_0_63, plain, (k7_subset_1(X1,k2_struct_0(X2),k7_subset_1(X3,k2_struct_0(X2),X4))=X4|~l1_struct_0(X2)|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))|~r1_tarski(k2_struct_0(X2),u1_struct_0(X2))|~r1_tarski(k2_struct_0(X2),X1)|~r1_tarski(k2_struct_0(X2),X3)), inference(spm,[status(thm)],[c_0_36, c_0_30]), ['final']).
% 0.19/0.39  cnf(c_0_64, plain, (k7_subset_1(X1,k2_struct_0(X2),k1_xboole_0)=k2_xboole_0(k2_struct_0(X2),X3)|~l1_struct_0(X2)|~r1_tarski(k2_xboole_0(k2_struct_0(X2),X3),u1_struct_0(X2))|~r1_tarski(k2_struct_0(X2),u1_struct_0(X2))|~r1_tarski(k2_struct_0(X2),X1)), inference(spm,[status(thm)],[c_0_47, c_0_16]), ['final']).
% 0.19/0.39  cnf(c_0_65, plain, (k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k1_xboole_0)=k2_xboole_0(k2_struct_0(X1),X2)|~l1_struct_0(X1)|~r1_tarski(k2_xboole_0(k2_struct_0(X1),X2),u1_struct_0(X1))|~r1_tarski(k2_struct_0(X1),u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_48, c_0_16]), ['final']).
% 0.19/0.39  cnf(c_0_66, plain, (k7_subset_1(X1,k2_struct_0(X2),k1_xboole_0)=X3|~l1_struct_0(X2)|~r1_tarski(k2_struct_0(X2),u1_struct_0(X2))|~r1_tarski(k2_struct_0(X2),X1)|~r1_tarski(k2_struct_0(X2),X3)|~r1_tarski(X3,u1_struct_0(X2))), inference(spm,[status(thm)],[c_0_49, c_0_16]), ['final']).
% 0.19/0.39  cnf(c_0_67, plain, (k2_xboole_0(k2_struct_0(X1),X2)=k1_xboole_0|~l1_struct_0(X1)|~r1_tarski(k2_xboole_0(k2_struct_0(X1),X2),u1_struct_0(X1))|~r1_tarski(k2_struct_0(X1),u1_struct_0(X1))|~r1_tarski(k2_struct_0(X1),k1_xboole_0)), inference(spm,[status(thm)],[c_0_50, c_0_16]), ['final']).
% 0.19/0.39  cnf(c_0_68, plain, (k7_subset_1(X1,k2_struct_0(X2),k4_xboole_0(k2_struct_0(X2),X3))=X3|~l1_struct_0(X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~r1_tarski(k2_struct_0(X2),u1_struct_0(X2))|~r1_tarski(k2_struct_0(X2),X1)), inference(spm,[status(thm)],[c_0_30, c_0_51]), ['final']).
% 0.19/0.39  cnf(c_0_69, plain, (k4_xboole_0(k2_struct_0(X1),k7_subset_1(X2,k2_struct_0(X1),X3))=X3|~l1_struct_0(X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(k2_struct_0(X1),u1_struct_0(X1))|~r1_tarski(k2_struct_0(X1),X2)), inference(spm,[status(thm)],[c_0_39, c_0_30]), ['final']).
% 0.19/0.39  cnf(c_0_70, plain, (k1_xboole_0=X1|~l1_struct_0(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~r1_tarski(k2_struct_0(X2),k7_subset_1(X3,k2_struct_0(X2),X1))|~r1_tarski(k2_struct_0(X2),u1_struct_0(X2))|~r1_tarski(k2_struct_0(X2),X3)), inference(spm,[status(thm)],[c_0_38, c_0_30]), ['final']).
% 0.19/0.39  cnf(c_0_71, plain, (k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k1_xboole_0)=X2|~l1_struct_0(X1)|~r1_tarski(k2_struct_0(X1),u1_struct_0(X1))|~r1_tarski(k2_struct_0(X1),X2)|~r1_tarski(X2,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_41, c_0_16]), ['final']).
% 0.19/0.39  cnf(c_0_72, plain, (k7_subset_1(X1,k2_struct_0(X2),k2_struct_0(X2))=k1_xboole_0|~l1_struct_0(X2)|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X2)))|~r1_tarski(k2_struct_0(X2),u1_struct_0(X2))|~r1_tarski(k2_struct_0(X2),X1)), inference(spm,[status(thm)],[c_0_21, c_0_52]), ['final']).
% 0.19/0.39  cnf(c_0_73, plain, (k2_xboole_0(k2_struct_0(X1),X2)=k2_struct_0(X1)|~l1_struct_0(X1)|~r1_tarski(k2_xboole_0(k2_struct_0(X1),X2),u1_struct_0(X1))|~r1_tarski(k2_struct_0(X1),u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_53, c_0_16]), ['final']).
% 0.19/0.39  cnf(c_0_74, plain, (k4_xboole_0(k2_struct_0(X1),k4_xboole_0(k2_struct_0(X1),X2))=X2|~l1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(k2_struct_0(X1),u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_39, c_0_21]), ['final']).
% 0.19/0.39  cnf(c_0_75, plain, (k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(X2,k2_struct_0(X1),X3))=X3|~l1_struct_0(X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(k2_struct_0(X1),u1_struct_0(X1))|~r1_tarski(k2_struct_0(X1),X2)), inference(spm,[status(thm)],[c_0_26, c_0_30]), ['final']).
% 0.19/0.39  cnf(c_0_76, plain, (X1=k1_xboole_0|~l1_struct_0(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~r1_tarski(k2_struct_0(X2),k4_xboole_0(k2_struct_0(X2),X1))|~r1_tarski(k2_struct_0(X2),u1_struct_0(X2))), inference(spm,[status(thm)],[c_0_31, c_0_51]), ['final']).
% 0.19/0.39  cnf(c_0_77, plain, (k1_xboole_0=X1|~l1_struct_0(X2)|~r1_tarski(k2_struct_0(X2),u1_struct_0(X2))|~r1_tarski(k2_struct_0(X2),k1_xboole_0)|~r1_tarski(k2_struct_0(X2),X1)|~r1_tarski(X1,u1_struct_0(X2))), inference(spm,[status(thm)],[c_0_54, c_0_16]), ['final']).
% 0.19/0.39  cnf(c_0_78, plain, (k7_subset_1(X1,k2_struct_0(X2),k1_xboole_0)=u1_struct_0(X2)|~l1_struct_0(X2)|~r1_tarski(k2_struct_0(X2),u1_struct_0(X2))|~r1_tarski(k2_struct_0(X2),X1)), inference(spm,[status(thm)],[c_0_30, c_0_55]), ['final']).
% 0.19/0.39  cnf(c_0_79, plain, (k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),u1_struct_0(X1))=k1_xboole_0|~l1_struct_0(X1)|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(k2_struct_0(X1),u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_26, c_0_55]), ['final']).
% 0.19/0.39  cnf(c_0_80, plain, (k2_struct_0(X1)=X2|~l1_struct_0(X1)|~r1_tarski(k2_struct_0(X1),u1_struct_0(X1))|~r1_tarski(k2_struct_0(X1),X2)|~r1_tarski(X2,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_56, c_0_16]), ['final']).
% 0.19/0.39  cnf(c_0_81, plain, (u1_struct_0(X1)=k1_xboole_0|~l1_struct_0(X1)|~r1_tarski(k2_struct_0(X1),u1_struct_0(X1))|~r1_tarski(k2_struct_0(X1),k1_xboole_0)), inference(spm,[status(thm)],[c_0_31, c_0_55]), ['final']).
% 0.19/0.39  cnf(c_0_82, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_struct_0(X1)|~r1_tarski(k2_struct_0(X1),u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_56, c_0_42]), ['final']).
% 0.19/0.39  cnf(c_0_83, plain, (k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k2_struct_0(X1))=k1_xboole_0|~l1_struct_0(X1)|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(k2_struct_0(X1),u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_26, c_0_40]), ['final']).
% 0.19/0.39  cnf(c_0_84, plain, (k7_subset_1(X1,X1,X2)=k7_subset_1(X3,X1,X2)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_57, c_0_21]), ['final']).
% 0.19/0.39  cnf(c_0_85, negated_conjecture, (k7_subset_1(X1,k2_struct_0(esk1_0),esk2_0)!=k1_xboole_0|~r1_tarski(k2_struct_0(esk1_0),u1_struct_0(esk1_0))|~r1_tarski(k2_struct_0(esk1_0),X1)), inference(spm,[status(thm)],[c_0_58, c_0_21]), ['final']).
% 0.19/0.39  cnf(c_0_86, negated_conjecture, (~r1_tarski(k2_struct_0(esk1_0),u1_struct_0(esk1_0))|~r1_tarski(k2_struct_0(esk1_0),esk2_0)), inference(spm,[status(thm)],[c_0_58, c_0_22]), ['final']).
% 0.19/0.39  cnf(c_0_87, plain, (k7_subset_1(X1,X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_22, c_0_57]), ['final']).
% 0.19/0.39  cnf(c_0_88, negated_conjecture, (u1_struct_0(esk1_0)=esk2_0|~r1_tarski(u1_struct_0(esk1_0),esk2_0)), inference(spm,[status(thm)],[c_0_59, c_0_60]), ['final']).
% 0.19/0.39  cnf(c_0_89, plain, (k1_xboole_0=X1|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_32, c_0_22]), ['final']).
% 0.19/0.39  cnf(c_0_90, plain, (k7_subset_1(X1,X1,k2_xboole_0(X1,X2))=k1_xboole_0), inference(spm,[status(thm)],[c_0_17, c_0_57]), ['final']).
% 0.19/0.39  cnf(c_0_91, plain, (k7_subset_1(X1,X1,k1_xboole_0)=X1), inference(spm,[status(thm)],[c_0_32, c_0_57]), ['final']).
% 0.19/0.39  cnf(c_0_92, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1)=k7_subset_1(esk2_0,esk2_0,X1)), inference(rw,[status(thm)],[c_0_61, c_0_57]), ['final']).
% 0.19/0.39  cnf(c_0_93, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_62]), ['final']).
% 0.19/0.39  # SZS output end Saturation
% 0.19/0.39  # Proof object total steps             : 94
% 0.19/0.39  # Proof object clause steps            : 73
% 0.19/0.39  # Proof object formula steps           : 21
% 0.19/0.39  # Proof object conjectures             : 16
% 0.19/0.39  # Proof object clause conjectures      : 13
% 0.19/0.39  # Proof object formula conjectures     : 3
% 0.19/0.39  # Proof object initial clauses used    : 15
% 0.19/0.39  # Proof object initial formulas used   : 10
% 0.19/0.39  # Proof object generating inferences   : 55
% 0.19/0.39  # Proof object simplifying inferences  : 11
% 0.19/0.39  # Parsed axioms                        : 10
% 0.19/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.39  # Initial clauses                      : 18
% 0.19/0.39  # Removed in clause preprocessing      : 3
% 0.19/0.39  # Initial clauses in saturation        : 15
% 0.19/0.39  # Processed clauses                    : 374
% 0.19/0.39  # ...of these trivial                  : 0
% 0.19/0.39  # ...subsumed                          : 288
% 0.19/0.39  # ...remaining for further processing  : 86
% 0.19/0.39  # Other redundant clauses eliminated   : 2
% 0.19/0.39  # Clauses deleted for lack of memory   : 0
% 0.19/0.39  # Backward-subsumed                    : 0
% 0.19/0.39  # Backward-rewritten                   : 1
% 0.19/0.39  # Generated clauses                    : 368
% 0.19/0.39  # ...of the previous two non-trivial   : 345
% 0.19/0.39  # Contextual simplify-reflections      : 1
% 0.19/0.39  # Paramodulations                      : 366
% 0.19/0.39  # Factorizations                       : 0
% 0.19/0.39  # Equation resolutions                 : 2
% 0.19/0.39  # Propositional unsat checks           : 0
% 0.19/0.39  #    Propositional check models        : 0
% 0.19/0.39  #    Propositional check unsatisfiable : 0
% 0.19/0.39  #    Propositional clauses             : 0
% 0.19/0.39  #    Propositional clauses after purity: 0
% 0.19/0.39  #    Propositional unsat core size     : 0
% 0.19/0.39  #    Propositional preprocessing time  : 0.000
% 0.19/0.39  #    Propositional encoding time       : 0.000
% 0.19/0.39  #    Propositional solver time         : 0.000
% 0.19/0.39  #    Success case prop preproc time    : 0.000
% 0.19/0.39  #    Success case prop encoding time   : 0.000
% 0.19/0.39  #    Success case prop solver time     : 0.000
% 0.19/0.39  # Current number of processed clauses  : 69
% 0.19/0.39  #    Positive orientable unit clauses  : 10
% 0.19/0.39  #    Positive unorientable unit clauses: 1
% 0.19/0.39  #    Negative unit clauses             : 0
% 0.19/0.39  #    Non-unit-clauses                  : 58
% 0.19/0.39  # Current number of unprocessed clauses: 0
% 0.19/0.39  # ...number of literals in the above   : 0
% 0.19/0.39  # Current number of archived formulas  : 0
% 0.19/0.39  # Current number of archived clauses   : 16
% 0.19/0.39  # Clause-clause subsumption calls (NU) : 2420
% 0.19/0.39  # Rec. Clause-clause subsumption calls : 1006
% 0.19/0.39  # Non-unit clause-clause subsumptions  : 287
% 0.19/0.39  # Unit Clause-clause subsumption calls : 3
% 0.19/0.39  # Rewrite failures with RHS unbound    : 0
% 0.19/0.39  # BW rewrite match attempts            : 31
% 0.19/0.39  # BW rewrite match successes           : 5
% 0.19/0.39  # Condensation attempts                : 0
% 0.19/0.39  # Condensation successes               : 0
% 0.19/0.39  # Termbank termtop insertions          : 9063
% 0.19/0.39  
% 0.19/0.39  # -------------------------------------------------
% 0.19/0.39  # User time                : 0.039 s
% 0.19/0.39  # System time              : 0.008 s
% 0.19/0.39  # Total time               : 0.046 s
% 0.19/0.39  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
