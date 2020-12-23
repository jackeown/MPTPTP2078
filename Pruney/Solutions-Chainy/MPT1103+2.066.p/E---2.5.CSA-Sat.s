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
% DateTime   : Thu Dec  3 11:08:44 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  137 (2814 expanded)
%              Number of clauses        :  112 (1323 expanded)
%              Number of leaves         :   12 ( 731 expanded)
%              Depth                    :   11
%              Number of atoms          :  434 (5464 expanded)
%              Number of equality atoms :  143 (2779 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   10 (   3 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(redefinition_k7_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k7_subset_1(X1,X2,X3) = k4_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(t46_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t23_pre_topc,conjecture,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( ~ ( X2 != k2_struct_0(X1)
                & k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2) = k1_xboole_0 )
            & ~ ( k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2) != k1_xboole_0
                & X2 = k2_struct_0(X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_pre_topc)).

fof(t22_pre_topc,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2)) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_pre_topc)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(c_0_12,plain,(
    ! [X15,X16] : k2_xboole_0(X15,X16) = k5_xboole_0(X15,k4_xboole_0(X16,X15)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_13,plain,(
    ! [X6,X7] : k4_xboole_0(X6,X7) = k5_xboole_0(X6,k3_xboole_0(X6,X7)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_14,plain,(
    ! [X17,X18,X19] :
      ( ~ m1_subset_1(X18,k1_zfmisc_1(X17))
      | k7_subset_1(X17,X18,X19) = k4_xboole_0(X18,X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).

fof(c_0_15,plain,(
    ! [X13,X14] : k4_xboole_0(X13,k2_xboole_0(X13,X14)) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t46_xboole_1])).

cnf(c_0_16,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( k7_subset_1(X2,X1,X3) = k4_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_19,plain,(
    ! [X20,X21] :
      ( ( ~ m1_subset_1(X20,k1_zfmisc_1(X21))
        | r1_tarski(X20,X21) )
      & ( ~ r1_tarski(X20,X21)
        | m1_subset_1(X20,k1_zfmisc_1(X21)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_20,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(rw,[status(thm)],[c_0_16,c_0_17])).

fof(c_0_22,plain,(
    ! [X8,X9] :
      ( ~ r1_tarski(X8,X9)
      | k3_xboole_0(X8,X9) = X8 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

fof(c_0_23,plain,(
    ! [X12] : k4_xboole_0(X12,k1_xboole_0) = X12 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

cnf(c_0_24,plain,
    ( k7_subset_1(X2,X1,X3) = k5_xboole_0(X1,k3_xboole_0(X1,X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_18,c_0_17]),
    [final]).

cnf(c_0_25,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19]),
    [final]).

cnf(c_0_26,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20,c_0_17]),c_0_21]),
    [final]).

cnf(c_0_27,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22]),
    [final]).

cnf(c_0_28,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_29,plain,(
    ! [X10] : k3_xboole_0(X10,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

fof(c_0_30,plain,(
    ! [X4,X5] :
      ( ( r1_tarski(X4,X5)
        | X4 != X5 )
      & ( r1_tarski(X5,X4)
        | X4 != X5 )
      & ( ~ r1_tarski(X4,X5)
        | ~ r1_tarski(X5,X4)
        | X4 = X5 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_31,negated_conjecture,(
    ~ ! [X1] :
        ( l1_struct_0(X1)
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( ~ ( X2 != k2_struct_0(X1)
                  & k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2) = k1_xboole_0 )
              & ~ ( k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2) != k1_xboole_0
                  & X2 = k2_struct_0(X1) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t23_pre_topc])).

cnf(c_0_32,plain,
    ( k7_subset_1(X1,X2,X3) = k5_xboole_0(X2,k3_xboole_0(X2,X3))
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25]),
    [final]).

fof(c_0_33,plain,(
    ! [X22,X23] :
      ( ~ l1_struct_0(X22)
      | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))
      | k7_subset_1(u1_struct_0(X22),k2_struct_0(X22),k7_subset_1(u1_struct_0(X22),k2_struct_0(X22),X23)) = X23 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t22_pre_topc])])])).

cnf(c_0_34,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0
    | ~ r1_tarski(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_35,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0)) = X1 ),
    inference(rw,[status(thm)],[c_0_28,c_0_17])).

cnf(c_0_36,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_29]),
    [final]).

cnf(c_0_37,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_38,plain,(
    ! [X11] : r1_tarski(k1_xboole_0,X11) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

fof(c_0_39,negated_conjecture,
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
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_31])])])])).

cnf(c_0_40,plain,
    ( k7_subset_1(X1,X2,k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2)))) = k1_xboole_0
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_32]),
    [final]).

cnf(c_0_41,plain,
    ( k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2)) = X2
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_33]),
    [final]).

cnf(c_0_42,plain,
    ( k7_subset_1(X1,X2,X3) = k7_subset_1(X4,X2,X3)
    | ~ r1_tarski(X2,X1)
    | ~ r1_tarski(X2,X4) ),
    inference(spm,[status(thm)],[c_0_32,c_0_32]),
    [final]).

cnf(c_0_43,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0
    | ~ r1_tarski(X1,k5_xboole_0(X1,k5_xboole_0(X2,X2)))
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_27])).

cnf(c_0_44,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[c_0_35,c_0_36]),
    [final]).

cnf(c_0_45,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_37]),
    [final]).

cnf(c_0_46,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38]),
    [final]).

cnf(c_0_47,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_39]),
    [final]).

cnf(c_0_48,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k7_subset_1(X2,X3,X1)))) = k1_xboole_0
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_26,c_0_32]),
    [final]).

cnf(c_0_49,plain,
    ( k7_subset_1(X1,X2,k5_xboole_0(X2,k7_subset_1(X3,X4,X2))) = k1_xboole_0
    | ~ r1_tarski(X2,X1)
    | ~ r1_tarski(X4,X3) ),
    inference(spm,[status(thm)],[c_0_40,c_0_32]),
    [final]).

cnf(c_0_50,plain,
    ( k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(X2,k2_struct_0(X1),X3)) = X3
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(k2_struct_0(X1),u1_struct_0(X1))
    | ~ r1_tarski(k2_struct_0(X1),X2) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42]),
    [final]).

cnf(c_0_51,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_44]),c_0_45]),c_0_46])]),
    [final]).

cnf(c_0_52,negated_conjecture,
    ( k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,X1)) = k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_47]),
    [final]).

cnf(c_0_53,negated_conjecture,
    ( esk2_0 = k2_struct_0(esk1_0)
    | k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_39]),
    [final]).

cnf(c_0_54,negated_conjecture,
    ( l1_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_39]),
    [final]).

cnf(c_0_55,plain,
    ( k5_xboole_0(k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2),k3_xboole_0(k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2),k5_xboole_0(k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2),X2))) = k1_xboole_0
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(k2_struct_0(X1),u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_41]),
    [final]).

cnf(c_0_56,plain,
    ( k7_subset_1(X1,k7_subset_1(X2,k2_struct_0(X3),X4),k5_xboole_0(k7_subset_1(X2,k2_struct_0(X3),X4),X4)) = k1_xboole_0
    | ~ l1_struct_0(X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ r1_tarski(k7_subset_1(X2,k2_struct_0(X3),X4),X1)
    | ~ r1_tarski(k2_struct_0(X3),u1_struct_0(X3))
    | ~ r1_tarski(k2_struct_0(X3),X2) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50]),
    [final]).

cnf(c_0_57,plain,
    ( k7_subset_1(X1,X2,X3) = k1_xboole_0
    | ~ r1_tarski(X2,X1)
    | ~ r1_tarski(X2,X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_27]),c_0_51]),
    [final]).

cnf(c_0_58,negated_conjecture,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1)))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_26,c_0_52]),
    [final]).

cnf(c_0_59,plain,
    ( k7_subset_1(X1,k2_struct_0(X2),k7_subset_1(u1_struct_0(X2),k2_struct_0(X2),X3)) = X3
    | ~ l1_struct_0(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r1_tarski(k2_struct_0(X2),u1_struct_0(X2))
    | ~ r1_tarski(k2_struct_0(X2),X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42]),
    [final]).

cnf(c_0_60,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),k1_xboole_0) = esk2_0
    | k2_struct_0(esk1_0) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_53]),c_0_54]),c_0_47])]),
    [final]).

cnf(c_0_61,plain,
    ( k7_subset_1(X1,X2,k1_xboole_0) = X2
    | ~ r1_tarski(X2,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_36]),c_0_44]),
    [final]).

cnf(c_0_62,plain,
    ( k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))),k3_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))),k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_26]),c_0_44])).

cnf(c_0_63,plain,
    ( k5_xboole_0(k7_subset_1(X1,k2_struct_0(X2),X3),k3_xboole_0(k7_subset_1(X1,k2_struct_0(X2),X3),k5_xboole_0(k7_subset_1(X1,k2_struct_0(X2),X3),X3))) = k1_xboole_0
    | ~ l1_struct_0(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r1_tarski(k2_struct_0(X2),u1_struct_0(X2))
    | ~ r1_tarski(k2_struct_0(X2),X1) ),
    inference(spm,[status(thm)],[c_0_55,c_0_42]),
    [final]).

cnf(c_0_64,plain,
    ( k7_subset_1(X1,k5_xboole_0(k2_struct_0(X2),k3_xboole_0(k2_struct_0(X2),X3)),k5_xboole_0(k5_xboole_0(k2_struct_0(X2),k3_xboole_0(k2_struct_0(X2),X3)),X3)) = k1_xboole_0
    | ~ l1_struct_0(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r1_tarski(k5_xboole_0(k2_struct_0(X2),k3_xboole_0(k2_struct_0(X2),X3)),X1)
    | ~ r1_tarski(k2_struct_0(X2),u1_struct_0(X2))
    | ~ r1_tarski(k2_struct_0(X2),X4) ),
    inference(spm,[status(thm)],[c_0_56,c_0_32]),
    [final]).

cnf(c_0_65,plain,
    ( k1_xboole_0 = X1
    | ~ l1_struct_0(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r1_tarski(k2_struct_0(X2),k7_subset_1(u1_struct_0(X2),k2_struct_0(X2),X1))
    | ~ r1_tarski(k2_struct_0(X2),u1_struct_0(X2)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_57]),
    [final]).

cnf(c_0_66,negated_conjecture,
    ( k7_subset_1(X1,X2,k5_xboole_0(X2,k7_subset_1(u1_struct_0(esk1_0),esk2_0,X2))) = k1_xboole_0
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_32,c_0_58]),
    [final]).

cnf(c_0_67,plain,
    ( k5_xboole_0(k2_struct_0(X1),k5_xboole_0(X2,k3_xboole_0(X2,k2_struct_0(X1)))) = k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k1_xboole_0)
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(k5_xboole_0(k2_struct_0(X1),k5_xboole_0(X2,k3_xboole_0(X2,k2_struct_0(X1)))),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(k2_struct_0(X1),u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_40]),
    [final]).

cnf(c_0_68,plain,
    ( k7_subset_1(X1,k2_struct_0(X2),k7_subset_1(X3,k2_struct_0(X2),X4)) = X4
    | ~ l1_struct_0(X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r1_tarski(k2_struct_0(X2),u1_struct_0(X2))
    | ~ r1_tarski(k2_struct_0(X2),X1)
    | ~ r1_tarski(k2_struct_0(X2),X3) ),
    inference(spm,[status(thm)],[c_0_59,c_0_42]),
    [final]).

cnf(c_0_69,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0) != k1_xboole_0
    | esk2_0 != k2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_39]),
    [final]).

cnf(c_0_70,negated_conjecture,
    ( k2_struct_0(esk1_0) = esk2_0
    | ~ r1_tarski(k2_struct_0(esk1_0),u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61]),
    [final]).

cnf(c_0_71,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X1)) = k1_xboole_0
    | ~ r1_tarski(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_27]),c_0_51]),c_0_44]),c_0_51]),c_0_44]),c_0_51]),c_0_44])).

cnf(c_0_72,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_19]),
    [final]).

cnf(c_0_73,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k1_xboole_0
    | ~ r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_32,c_0_57])).

cnf(c_0_74,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),esk2_0,k5_xboole_0(esk2_0,k5_xboole_0(X1,k3_xboole_0(X1,esk2_0)))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_26,c_0_52]),
    [final]).

cnf(c_0_75,plain,
    ( k5_xboole_0(k5_xboole_0(k2_struct_0(X1),k3_xboole_0(k2_struct_0(X1),X2)),k3_xboole_0(k5_xboole_0(k2_struct_0(X1),k3_xboole_0(k2_struct_0(X1),X2)),k5_xboole_0(k5_xboole_0(k2_struct_0(X1),k3_xboole_0(k2_struct_0(X1),X2)),X2))) = k1_xboole_0
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(k2_struct_0(X1),u1_struct_0(X1))
    | ~ r1_tarski(k2_struct_0(X1),X3) ),
    inference(spm,[status(thm)],[c_0_63,c_0_32]),
    [final]).

cnf(c_0_76,plain,
    ( k7_subset_1(k5_xboole_0(k2_struct_0(X1),k3_xboole_0(k2_struct_0(X1),X2)),k5_xboole_0(k2_struct_0(X1),k3_xboole_0(k2_struct_0(X1),X2)),k5_xboole_0(k5_xboole_0(k2_struct_0(X1),k3_xboole_0(k2_struct_0(X1),X2)),X2)) = k1_xboole_0
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(k2_struct_0(X1),u1_struct_0(X1))
    | ~ r1_tarski(k2_struct_0(X1),X3) ),
    inference(spm,[status(thm)],[c_0_64,c_0_45]),
    [final]).

cnf(c_0_77,plain,
    ( k7_subset_1(X1,k2_struct_0(X2),k1_xboole_0) = k5_xboole_0(k2_struct_0(X2),k5_xboole_0(X3,k3_xboole_0(X3,k2_struct_0(X2))))
    | ~ l1_struct_0(X2)
    | ~ m1_subset_1(k5_xboole_0(k2_struct_0(X2),k5_xboole_0(X3,k3_xboole_0(X3,k2_struct_0(X2)))),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r1_tarski(k2_struct_0(X2),u1_struct_0(X2))
    | ~ r1_tarski(k2_struct_0(X2),X1) ),
    inference(spm,[status(thm)],[c_0_59,c_0_40]),
    [final]).

cnf(c_0_78,plain,
    ( k7_subset_1(X1,k2_struct_0(X2),k1_xboole_0) = k5_xboole_0(k2_struct_0(X2),k7_subset_1(X3,X4,k2_struct_0(X2)))
    | ~ l1_struct_0(X2)
    | ~ m1_subset_1(k5_xboole_0(k2_struct_0(X2),k7_subset_1(X3,X4,k2_struct_0(X2))),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r1_tarski(k2_struct_0(X2),u1_struct_0(X2))
    | ~ r1_tarski(k2_struct_0(X2),X1)
    | ~ r1_tarski(X4,X3) ),
    inference(spm,[status(thm)],[c_0_59,c_0_49]),
    [final]).

cnf(c_0_79,plain,
    ( k5_xboole_0(k2_struct_0(X1),k5_xboole_0(X2,k3_xboole_0(X2,k2_struct_0(X1)))) = k1_xboole_0
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(k5_xboole_0(k2_struct_0(X1),k5_xboole_0(X2,k3_xboole_0(X2,k2_struct_0(X1)))),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(k2_struct_0(X1),u1_struct_0(X1))
    | ~ r1_tarski(k2_struct_0(X1),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_65,c_0_40]),
    [final]).

cnf(c_0_80,negated_conjecture,
    ( k7_subset_1(X1,k2_struct_0(X2),k1_xboole_0) = k5_xboole_0(k2_struct_0(X2),k7_subset_1(u1_struct_0(esk1_0),esk2_0,k2_struct_0(X2)))
    | ~ l1_struct_0(X2)
    | ~ m1_subset_1(k5_xboole_0(k2_struct_0(X2),k7_subset_1(u1_struct_0(esk1_0),esk2_0,k2_struct_0(X2))),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r1_tarski(k2_struct_0(X2),u1_struct_0(X2))
    | ~ r1_tarski(k2_struct_0(X2),X1) ),
    inference(spm,[status(thm)],[c_0_59,c_0_66]),
    [final]).

cnf(c_0_81,plain,
    ( k5_xboole_0(k2_struct_0(X1),k7_subset_1(X2,X3,k2_struct_0(X1))) = k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k1_xboole_0)
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(k5_xboole_0(k2_struct_0(X1),k7_subset_1(X2,X3,k2_struct_0(X1))),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(k2_struct_0(X1),u1_struct_0(X1))
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_67,c_0_32]),
    [final]).

cnf(c_0_82,plain,
    ( k5_xboole_0(k2_struct_0(X1),k7_subset_1(X2,X3,k2_struct_0(X1))) = k1_xboole_0
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(k5_xboole_0(k2_struct_0(X1),k7_subset_1(X2,X3,k2_struct_0(X1))),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(k2_struct_0(X1),u1_struct_0(X1))
    | ~ r1_tarski(k2_struct_0(X1),k1_xboole_0)
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_65,c_0_49]),
    [final]).

cnf(c_0_83,plain,
    ( k7_subset_1(X1,k2_struct_0(X2),k5_xboole_0(k2_struct_0(X2),k3_xboole_0(k2_struct_0(X2),X3))) = X3
    | ~ l1_struct_0(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r1_tarski(k2_struct_0(X2),u1_struct_0(X2))
    | ~ r1_tarski(k2_struct_0(X2),X1)
    | ~ r1_tarski(k2_struct_0(X2),X4) ),
    inference(spm,[status(thm)],[c_0_68,c_0_32]),
    [final]).

cnf(c_0_84,plain,
    ( k5_xboole_0(k2_struct_0(X1),k3_xboole_0(k2_struct_0(X1),k7_subset_1(X2,k2_struct_0(X1),X3))) = X3
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(k2_struct_0(X1),u1_struct_0(X1))
    | ~ r1_tarski(k2_struct_0(X1),X4)
    | ~ r1_tarski(k2_struct_0(X1),X2) ),
    inference(spm,[status(thm)],[c_0_32,c_0_68]),
    [final]).

cnf(c_0_85,negated_conjecture,
    ( k5_xboole_0(k2_struct_0(X1),k7_subset_1(u1_struct_0(esk1_0),esk2_0,k2_struct_0(X1))) = k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k1_xboole_0)
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(k5_xboole_0(k2_struct_0(X1),k7_subset_1(u1_struct_0(esk1_0),esk2_0,k2_struct_0(X1))),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(k2_struct_0(X1),u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_66]),
    [final]).

cnf(c_0_86,plain,
    ( k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k5_xboole_0(k2_struct_0(X1),k3_xboole_0(k2_struct_0(X1),X2))) = X2
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(k2_struct_0(X1),u1_struct_0(X1))
    | ~ r1_tarski(k2_struct_0(X1),X3) ),
    inference(spm,[status(thm)],[c_0_50,c_0_32]),
    [final]).

cnf(c_0_87,negated_conjecture,
    ( k5_xboole_0(k2_struct_0(X1),k7_subset_1(u1_struct_0(esk1_0),esk2_0,k2_struct_0(X1))) = k1_xboole_0
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(k5_xboole_0(k2_struct_0(X1),k7_subset_1(u1_struct_0(esk1_0),esk2_0,k2_struct_0(X1))),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(k2_struct_0(X1),u1_struct_0(X1))
    | ~ r1_tarski(k2_struct_0(X1),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66]),
    [final]).

cnf(c_0_88,plain,
    ( k5_xboole_0(k2_struct_0(X1),k3_xboole_0(k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2))) = X2
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(k2_struct_0(X1),u1_struct_0(X1))
    | ~ r1_tarski(k2_struct_0(X1),X3) ),
    inference(spm,[status(thm)],[c_0_32,c_0_59]),
    [final]).

cnf(c_0_89,plain,
    ( k7_subset_1(X1,k2_struct_0(X2),k1_xboole_0) = X3
    | ~ l1_struct_0(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r1_tarski(k2_struct_0(X2),u1_struct_0(X2))
    | ~ r1_tarski(k2_struct_0(X2),X1)
    | ~ r1_tarski(k2_struct_0(X2),X3) ),
    inference(spm,[status(thm)],[c_0_59,c_0_57]),
    [final]).

cnf(c_0_90,plain,
    ( k1_xboole_0 = X1
    | ~ l1_struct_0(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r1_tarski(k2_struct_0(X2),k7_subset_1(X3,k2_struct_0(X2),X1))
    | ~ r1_tarski(k2_struct_0(X2),u1_struct_0(X2))
    | ~ r1_tarski(k2_struct_0(X2),X3) ),
    inference(spm,[status(thm)],[c_0_65,c_0_42]),
    [final]).

cnf(c_0_91,plain,
    ( k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k1_xboole_0) = X2
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(k2_struct_0(X1),u1_struct_0(X1))
    | ~ r1_tarski(k2_struct_0(X1),X2) ),
    inference(spm,[status(thm)],[c_0_41,c_0_57]),
    [final]).

cnf(c_0_92,plain,
    ( k1_xboole_0 = X1
    | ~ l1_struct_0(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r1_tarski(k2_struct_0(X2),u1_struct_0(X2))
    | ~ r1_tarski(k2_struct_0(X2),k1_xboole_0)
    | ~ r1_tarski(k2_struct_0(X2),X1) ),
    inference(spm,[status(thm)],[c_0_65,c_0_57]),
    [final]).

cnf(c_0_93,negated_conjecture,
    ( k7_subset_1(X1,k2_struct_0(esk1_0),esk2_0) != k1_xboole_0
    | ~ r1_tarski(k2_struct_0(esk1_0),u1_struct_0(esk1_0))
    | ~ r1_tarski(k2_struct_0(esk1_0),X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_42]),c_0_70]),
    [final]).

cnf(c_0_94,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X1)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_71,c_0_46]),
    [final]).

cnf(c_0_95,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30]),
    [final]).

cnf(c_0_96,negated_conjecture,
    ( r1_tarski(esk2_0,u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_72,c_0_47]),
    [final]).

cnf(c_0_97,plain,
    ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1)) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_46]),c_0_46])]),
    [final]).

cnf(c_0_98,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),esk2_0,esk2_0) = k1_xboole_0
    | ~ r1_tarski(X1,esk2_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_27]),c_0_51]),c_0_44])).

cnf(c_0_99,plain,
    ( k5_xboole_0(k5_xboole_0(k2_struct_0(X1),k3_xboole_0(k2_struct_0(X1),X2)),k3_xboole_0(k5_xboole_0(k2_struct_0(X1),k3_xboole_0(k2_struct_0(X1),X2)),k5_xboole_0(k5_xboole_0(k2_struct_0(X1),k3_xboole_0(k2_struct_0(X1),X2)),X2))) = k1_xboole_0
    | ~ l1_struct_0(X1)
    | ~ r1_tarski(k2_struct_0(X1),u1_struct_0(X1))
    | ~ r1_tarski(k2_struct_0(X1),X3)
    | ~ r1_tarski(X2,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_75,c_0_25]),
    [final]).

cnf(c_0_100,plain,
    ( k7_subset_1(k5_xboole_0(k2_struct_0(X1),k3_xboole_0(k2_struct_0(X1),X2)),k5_xboole_0(k2_struct_0(X1),k3_xboole_0(k2_struct_0(X1),X2)),k5_xboole_0(k5_xboole_0(k2_struct_0(X1),k3_xboole_0(k2_struct_0(X1),X2)),X2)) = k1_xboole_0
    | ~ l1_struct_0(X1)
    | ~ r1_tarski(k2_struct_0(X1),u1_struct_0(X1))
    | ~ r1_tarski(k2_struct_0(X1),X3)
    | ~ r1_tarski(X2,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_76,c_0_25]),
    [final]).

cnf(c_0_101,negated_conjecture,
    ( k7_subset_1(k5_xboole_0(k2_struct_0(esk1_0),k3_xboole_0(k2_struct_0(esk1_0),esk2_0)),k5_xboole_0(k2_struct_0(esk1_0),k3_xboole_0(k2_struct_0(esk1_0),esk2_0)),k5_xboole_0(k5_xboole_0(k2_struct_0(esk1_0),k3_xboole_0(k2_struct_0(esk1_0),esk2_0)),esk2_0)) = k1_xboole_0
    | ~ r1_tarski(k2_struct_0(esk1_0),u1_struct_0(esk1_0))
    | ~ r1_tarski(k2_struct_0(esk1_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_47]),c_0_54])]),
    [final]).

cnf(c_0_102,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(k2_struct_0(esk1_0),k3_xboole_0(k2_struct_0(esk1_0),esk2_0)),k3_xboole_0(k5_xboole_0(k2_struct_0(esk1_0),k3_xboole_0(k2_struct_0(esk1_0),esk2_0)),k5_xboole_0(k5_xboole_0(k2_struct_0(esk1_0),k3_xboole_0(k2_struct_0(esk1_0),esk2_0)),esk2_0))) = k1_xboole_0
    | ~ r1_tarski(k2_struct_0(esk1_0),u1_struct_0(esk1_0))
    | ~ r1_tarski(k2_struct_0(esk1_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_47]),c_0_54])]),
    [final]).

cnf(c_0_103,plain,
    ( k7_subset_1(X1,k2_struct_0(X2),k1_xboole_0) = k5_xboole_0(k2_struct_0(X2),k5_xboole_0(X3,k3_xboole_0(X3,k2_struct_0(X2))))
    | ~ l1_struct_0(X2)
    | ~ r1_tarski(k5_xboole_0(k2_struct_0(X2),k5_xboole_0(X3,k3_xboole_0(X3,k2_struct_0(X2)))),u1_struct_0(X2))
    | ~ r1_tarski(k2_struct_0(X2),u1_struct_0(X2))
    | ~ r1_tarski(k2_struct_0(X2),X1) ),
    inference(spm,[status(thm)],[c_0_77,c_0_25]),
    [final]).

cnf(c_0_104,plain,
    ( k7_subset_1(X1,k2_struct_0(X2),k1_xboole_0) = k5_xboole_0(k2_struct_0(X2),k7_subset_1(X3,X4,k2_struct_0(X2)))
    | ~ l1_struct_0(X2)
    | ~ r1_tarski(k5_xboole_0(k2_struct_0(X2),k7_subset_1(X3,X4,k2_struct_0(X2))),u1_struct_0(X2))
    | ~ r1_tarski(k2_struct_0(X2),u1_struct_0(X2))
    | ~ r1_tarski(k2_struct_0(X2),X1)
    | ~ r1_tarski(X4,X3) ),
    inference(spm,[status(thm)],[c_0_78,c_0_25]),
    [final]).

cnf(c_0_105,plain,
    ( k5_xboole_0(k2_struct_0(X1),k5_xboole_0(X2,k3_xboole_0(X2,k2_struct_0(X1)))) = k1_xboole_0
    | ~ l1_struct_0(X1)
    | ~ r1_tarski(k5_xboole_0(k2_struct_0(X1),k5_xboole_0(X2,k3_xboole_0(X2,k2_struct_0(X1)))),u1_struct_0(X1))
    | ~ r1_tarski(k2_struct_0(X1),u1_struct_0(X1))
    | ~ r1_tarski(k2_struct_0(X1),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_79,c_0_25]),
    [final]).

cnf(c_0_106,negated_conjecture,
    ( k7_subset_1(X1,k2_struct_0(X2),k1_xboole_0) = k5_xboole_0(k2_struct_0(X2),k7_subset_1(u1_struct_0(esk1_0),esk2_0,k2_struct_0(X2)))
    | ~ l1_struct_0(X2)
    | ~ r1_tarski(k5_xboole_0(k2_struct_0(X2),k7_subset_1(u1_struct_0(esk1_0),esk2_0,k2_struct_0(X2))),u1_struct_0(X2))
    | ~ r1_tarski(k2_struct_0(X2),u1_struct_0(X2))
    | ~ r1_tarski(k2_struct_0(X2),X1) ),
    inference(spm,[status(thm)],[c_0_80,c_0_25]),
    [final]).

cnf(c_0_107,plain,
    ( k7_subset_1(X1,k7_subset_1(u1_struct_0(X2),k2_struct_0(X2),X3),k5_xboole_0(k7_subset_1(u1_struct_0(X2),k2_struct_0(X2),X3),X3)) = k1_xboole_0
    | ~ l1_struct_0(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r1_tarski(k7_subset_1(u1_struct_0(X2),k2_struct_0(X2),X3),X1)
    | ~ r1_tarski(k2_struct_0(X2),u1_struct_0(X2)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_41]),
    [final]).

cnf(c_0_108,plain,
    ( k5_xboole_0(k2_struct_0(X1),k7_subset_1(X2,X3,k2_struct_0(X1))) = k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k1_xboole_0)
    | ~ l1_struct_0(X1)
    | ~ r1_tarski(k5_xboole_0(k2_struct_0(X1),k7_subset_1(X2,X3,k2_struct_0(X1))),u1_struct_0(X1))
    | ~ r1_tarski(k2_struct_0(X1),u1_struct_0(X1))
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_81,c_0_25]),
    [final]).

cnf(c_0_109,plain,
    ( k5_xboole_0(k2_struct_0(X1),k7_subset_1(X2,X3,k2_struct_0(X1))) = k1_xboole_0
    | ~ l1_struct_0(X1)
    | ~ r1_tarski(k5_xboole_0(k2_struct_0(X1),k7_subset_1(X2,X3,k2_struct_0(X1))),u1_struct_0(X1))
    | ~ r1_tarski(k2_struct_0(X1),u1_struct_0(X1))
    | ~ r1_tarski(k2_struct_0(X1),k1_xboole_0)
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_82,c_0_25]),
    [final]).

cnf(c_0_110,plain,
    ( k7_subset_1(X1,k2_struct_0(X2),k5_xboole_0(k2_struct_0(X2),k3_xboole_0(k2_struct_0(X2),X3))) = X3
    | ~ l1_struct_0(X2)
    | ~ r1_tarski(k2_struct_0(X2),u1_struct_0(X2))
    | ~ r1_tarski(k2_struct_0(X2),X1)
    | ~ r1_tarski(k2_struct_0(X2),X4)
    | ~ r1_tarski(X3,u1_struct_0(X2)) ),
    inference(spm,[status(thm)],[c_0_83,c_0_25]),
    [final]).

cnf(c_0_111,negated_conjecture,
    ( k7_subset_1(X1,k2_struct_0(esk1_0),k5_xboole_0(k2_struct_0(esk1_0),k3_xboole_0(k2_struct_0(esk1_0),esk2_0))) = esk2_0
    | ~ r1_tarski(k2_struct_0(esk1_0),u1_struct_0(esk1_0))
    | ~ r1_tarski(k2_struct_0(esk1_0),X1)
    | ~ r1_tarski(k2_struct_0(esk1_0),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_47]),c_0_54])]),
    [final]).

cnf(c_0_112,plain,
    ( k5_xboole_0(k2_struct_0(X1),k3_xboole_0(k2_struct_0(X1),k7_subset_1(X2,k2_struct_0(X1),X3))) = X3
    | ~ l1_struct_0(X1)
    | ~ r1_tarski(k2_struct_0(X1),u1_struct_0(X1))
    | ~ r1_tarski(k2_struct_0(X1),X4)
    | ~ r1_tarski(k2_struct_0(X1),X2)
    | ~ r1_tarski(X3,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_84,c_0_25]),
    [final]).

cnf(c_0_113,negated_conjecture,
    ( k5_xboole_0(k2_struct_0(esk1_0),k3_xboole_0(k2_struct_0(esk1_0),k7_subset_1(X1,k2_struct_0(esk1_0),esk2_0))) = esk2_0
    | ~ r1_tarski(k2_struct_0(esk1_0),u1_struct_0(esk1_0))
    | ~ r1_tarski(k2_struct_0(esk1_0),X2)
    | ~ r1_tarski(k2_struct_0(esk1_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_47]),c_0_54])]),
    [final]).

cnf(c_0_114,plain,
    ( k5_xboole_0(k2_struct_0(X1),k5_xboole_0(X2,k3_xboole_0(X2,k2_struct_0(X1)))) = k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k1_xboole_0)
    | ~ l1_struct_0(X1)
    | ~ r1_tarski(k5_xboole_0(k2_struct_0(X1),k5_xboole_0(X2,k3_xboole_0(X2,k2_struct_0(X1)))),u1_struct_0(X1))
    | ~ r1_tarski(k2_struct_0(X1),u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_67,c_0_25]),
    [final]).

cnf(c_0_115,negated_conjecture,
    ( k5_xboole_0(k2_struct_0(X1),k7_subset_1(u1_struct_0(esk1_0),esk2_0,k2_struct_0(X1))) = k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k1_xboole_0)
    | ~ l1_struct_0(X1)
    | ~ r1_tarski(k5_xboole_0(k2_struct_0(X1),k7_subset_1(u1_struct_0(esk1_0),esk2_0,k2_struct_0(X1))),u1_struct_0(X1))
    | ~ r1_tarski(k2_struct_0(X1),u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_85,c_0_25]),
    [final]).

cnf(c_0_116,plain,
    ( k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k5_xboole_0(k2_struct_0(X1),k3_xboole_0(k2_struct_0(X1),X2))) = X2
    | ~ l1_struct_0(X1)
    | ~ r1_tarski(k2_struct_0(X1),u1_struct_0(X1))
    | ~ r1_tarski(k2_struct_0(X1),X3)
    | ~ r1_tarski(X2,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_86,c_0_25]),
    [final]).

cnf(c_0_117,negated_conjecture,
    ( k5_xboole_0(k2_struct_0(X1),k7_subset_1(u1_struct_0(esk1_0),esk2_0,k2_struct_0(X1))) = k1_xboole_0
    | ~ l1_struct_0(X1)
    | ~ r1_tarski(k5_xboole_0(k2_struct_0(X1),k7_subset_1(u1_struct_0(esk1_0),esk2_0,k2_struct_0(X1))),u1_struct_0(X1))
    | ~ r1_tarski(k2_struct_0(X1),u1_struct_0(X1))
    | ~ r1_tarski(k2_struct_0(X1),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_87,c_0_25]),
    [final]).

cnf(c_0_118,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),k5_xboole_0(k2_struct_0(esk1_0),k3_xboole_0(k2_struct_0(esk1_0),esk2_0))) = esk2_0
    | ~ r1_tarski(k2_struct_0(esk1_0),u1_struct_0(esk1_0))
    | ~ r1_tarski(k2_struct_0(esk1_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_47]),c_0_54])]),
    [final]).

cnf(c_0_119,plain,
    ( k5_xboole_0(k2_struct_0(X1),k3_xboole_0(k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2))) = X2
    | ~ l1_struct_0(X1)
    | ~ r1_tarski(k2_struct_0(X1),u1_struct_0(X1))
    | ~ r1_tarski(k2_struct_0(X1),X3)
    | ~ r1_tarski(X2,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_88,c_0_25]),
    [final]).

cnf(c_0_120,negated_conjecture,
    ( k5_xboole_0(k2_struct_0(esk1_0),k3_xboole_0(k2_struct_0(esk1_0),k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0))) = esk2_0
    | ~ r1_tarski(k2_struct_0(esk1_0),u1_struct_0(esk1_0))
    | ~ r1_tarski(k2_struct_0(esk1_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_47]),c_0_54])]),
    [final]).

cnf(c_0_121,plain,
    ( k7_subset_1(X1,k2_struct_0(X2),k1_xboole_0) = X3
    | ~ l1_struct_0(X2)
    | ~ r1_tarski(k2_struct_0(X2),u1_struct_0(X2))
    | ~ r1_tarski(k2_struct_0(X2),X1)
    | ~ r1_tarski(k2_struct_0(X2),X3)
    | ~ r1_tarski(X3,u1_struct_0(X2)) ),
    inference(spm,[status(thm)],[c_0_89,c_0_25]),
    [final]).

cnf(c_0_122,plain,
    ( k1_xboole_0 = X1
    | ~ l1_struct_0(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r1_tarski(k2_struct_0(X2),k5_xboole_0(k2_struct_0(X2),k3_xboole_0(k2_struct_0(X2),X1)))
    | ~ r1_tarski(k2_struct_0(X2),u1_struct_0(X2))
    | ~ r1_tarski(k2_struct_0(X2),X3) ),
    inference(spm,[status(thm)],[c_0_90,c_0_32]),
    [final]).

cnf(c_0_123,plain,
    ( k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k1_xboole_0) = X2
    | ~ l1_struct_0(X1)
    | ~ r1_tarski(k2_struct_0(X1),u1_struct_0(X1))
    | ~ r1_tarski(k2_struct_0(X1),X2)
    | ~ r1_tarski(X2,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_91,c_0_25]),
    [final]).

cnf(c_0_124,plain,
    ( k1_xboole_0 = X1
    | ~ l1_struct_0(X2)
    | ~ r1_tarski(k2_struct_0(X2),u1_struct_0(X2))
    | ~ r1_tarski(k2_struct_0(X2),k1_xboole_0)
    | ~ r1_tarski(k2_struct_0(X2),X1)
    | ~ r1_tarski(X1,u1_struct_0(X2)) ),
    inference(spm,[status(thm)],[c_0_92,c_0_25]),
    [final]).

cnf(c_0_125,negated_conjecture,
    ( k5_xboole_0(k2_struct_0(esk1_0),k3_xboole_0(k2_struct_0(esk1_0),esk2_0)) != k1_xboole_0
    | ~ r1_tarski(k2_struct_0(esk1_0),u1_struct_0(esk1_0))
    | ~ r1_tarski(k2_struct_0(esk1_0),X1) ),
    inference(spm,[status(thm)],[c_0_93,c_0_32]),
    [final]).

cnf(c_0_126,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),esk2_0,k5_xboole_0(esk2_0,k7_subset_1(X1,X2,esk2_0))) = k1_xboole_0
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_74,c_0_32]),
    [final]).

cnf(c_0_127,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_73,c_0_45]),
    [final]).

cnf(c_0_128,negated_conjecture,
    ( ~ r1_tarski(k2_struct_0(esk1_0),u1_struct_0(esk1_0))
    | ~ r1_tarski(k2_struct_0(esk1_0),esk2_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_57]),c_0_70]),
    [final]).

cnf(c_0_129,negated_conjecture,
    ( k7_subset_1(X1,esk2_0,X2) = k7_subset_1(u1_struct_0(esk1_0),esk2_0,X2)
    | ~ r1_tarski(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_52,c_0_32]),
    [final]).

cnf(c_0_130,plain,
    ( k7_subset_1(X1,X2,X2) = k1_xboole_0
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_32,c_0_94]),
    [final]).

cnf(c_0_131,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1) = k1_xboole_0
    | ~ r1_tarski(esk2_0,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_27]),c_0_51]),
    [final]).

cnf(c_0_132,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_95,c_0_46]),
    [final]).

cnf(c_0_133,negated_conjecture,
    ( u1_struct_0(esk1_0) = esk2_0
    | ~ r1_tarski(u1_struct_0(esk1_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_95,c_0_96]),
    [final]).

cnf(c_0_134,plain,
    ( k7_subset_1(X1,k1_xboole_0,X2) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_97]),c_0_46])]),
    [final]).

cnf(c_0_135,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),esk2_0,esk2_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_98,c_0_46]),
    [final]).

cnf(c_0_136,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),esk2_0,k1_xboole_0) = esk2_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_36]),c_0_44]),
    [final]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.35  % Computer   : n006.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:31:37 EST 2020
% 0.21/0.35  % CPUTime    : 
% 0.21/0.35  # Version: 2.5pre002
% 0.21/0.35  # No SInE strategy applied
% 0.21/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.41  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.21/0.41  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.21/0.41  #
% 0.21/0.41  # Preprocessing time       : 0.027 s
% 0.21/0.41  # Presaturation interreduction done
% 0.21/0.41  
% 0.21/0.41  # No proof found!
% 0.21/0.41  # SZS status CounterSatisfiable
% 0.21/0.41  # SZS output start Saturation
% 0.21/0.41  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.21/0.41  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.21/0.41  fof(redefinition_k7_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k7_subset_1(X1,X2,X3)=k4_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 0.21/0.41  fof(t46_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 0.21/0.41  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.21/0.41  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.21/0.41  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 0.21/0.41  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 0.21/0.41  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.21/0.41  fof(t23_pre_topc, conjecture, ![X1]:(l1_struct_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(~((X2!=k2_struct_0(X1)&k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2)=k1_xboole_0))&~((k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2)!=k1_xboole_0&X2=k2_struct_0(X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_pre_topc)).
% 0.21/0.41  fof(t22_pre_topc, axiom, ![X1]:(l1_struct_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2))=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_pre_topc)).
% 0.21/0.41  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.21/0.41  fof(c_0_12, plain, ![X15, X16]:k2_xboole_0(X15,X16)=k5_xboole_0(X15,k4_xboole_0(X16,X15)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.21/0.41  fof(c_0_13, plain, ![X6, X7]:k4_xboole_0(X6,X7)=k5_xboole_0(X6,k3_xboole_0(X6,X7)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.21/0.41  fof(c_0_14, plain, ![X17, X18, X19]:(~m1_subset_1(X18,k1_zfmisc_1(X17))|k7_subset_1(X17,X18,X19)=k4_xboole_0(X18,X19)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).
% 0.21/0.41  fof(c_0_15, plain, ![X13, X14]:k4_xboole_0(X13,k2_xboole_0(X13,X14))=k1_xboole_0, inference(variable_rename,[status(thm)],[t46_xboole_1])).
% 0.21/0.41  cnf(c_0_16, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.41  cnf(c_0_17, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.21/0.41  cnf(c_0_18, plain, (k7_subset_1(X2,X1,X3)=k4_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.41  fof(c_0_19, plain, ![X20, X21]:((~m1_subset_1(X20,k1_zfmisc_1(X21))|r1_tarski(X20,X21))&(~r1_tarski(X20,X21)|m1_subset_1(X20,k1_zfmisc_1(X21)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.21/0.41  cnf(c_0_20, plain, (k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.41  cnf(c_0_21, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))), inference(rw,[status(thm)],[c_0_16, c_0_17])).
% 0.21/0.41  fof(c_0_22, plain, ![X8, X9]:(~r1_tarski(X8,X9)|k3_xboole_0(X8,X9)=X8), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.21/0.41  fof(c_0_23, plain, ![X12]:k4_xboole_0(X12,k1_xboole_0)=X12, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.21/0.41  cnf(c_0_24, plain, (k7_subset_1(X2,X1,X3)=k5_xboole_0(X1,k3_xboole_0(X1,X3))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_18, c_0_17]), ['final']).
% 0.21/0.41  cnf(c_0_25, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19]), ['final']).
% 0.21/0.41  cnf(c_0_26, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20, c_0_17]), c_0_21]), ['final']).
% 0.21/0.41  cnf(c_0_27, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22]), ['final']).
% 0.21/0.41  cnf(c_0_28, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.21/0.41  fof(c_0_29, plain, ![X10]:k3_xboole_0(X10,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 0.21/0.41  fof(c_0_30, plain, ![X4, X5]:(((r1_tarski(X4,X5)|X4!=X5)&(r1_tarski(X5,X4)|X4!=X5))&(~r1_tarski(X4,X5)|~r1_tarski(X5,X4)|X4=X5)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.21/0.41  fof(c_0_31, negated_conjecture, ~(![X1]:(l1_struct_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(~((X2!=k2_struct_0(X1)&k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2)=k1_xboole_0))&~((k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2)!=k1_xboole_0&X2=k2_struct_0(X1))))))), inference(assume_negation,[status(cth)],[t23_pre_topc])).
% 0.21/0.41  cnf(c_0_32, plain, (k7_subset_1(X1,X2,X3)=k5_xboole_0(X2,k3_xboole_0(X2,X3))|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_24, c_0_25]), ['final']).
% 0.21/0.41  fof(c_0_33, plain, ![X22, X23]:(~l1_struct_0(X22)|(~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))|k7_subset_1(u1_struct_0(X22),k2_struct_0(X22),k7_subset_1(u1_struct_0(X22),k2_struct_0(X22),X23))=X23)), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t22_pre_topc])])])).
% 0.21/0.41  cnf(c_0_34, plain, (k5_xboole_0(X1,X1)=k1_xboole_0|~r1_tarski(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.21/0.41  cnf(c_0_35, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0))=X1), inference(rw,[status(thm)],[c_0_28, c_0_17])).
% 0.21/0.41  cnf(c_0_36, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_29]), ['final']).
% 0.21/0.41  cnf(c_0_37, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.21/0.41  fof(c_0_38, plain, ![X11]:r1_tarski(k1_xboole_0,X11), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.21/0.41  fof(c_0_39, negated_conjecture, (l1_struct_0(esk1_0)&(m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&(((k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)!=k1_xboole_0|esk2_0!=k2_struct_0(esk1_0))&(esk2_0=k2_struct_0(esk1_0)|esk2_0!=k2_struct_0(esk1_0)))&((k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)!=k1_xboole_0|k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)=k1_xboole_0)&(esk2_0=k2_struct_0(esk1_0)|k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)=k1_xboole_0))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_31])])])])).
% 0.21/0.41  cnf(c_0_40, plain, (k7_subset_1(X1,X2,k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2))))=k1_xboole_0|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_26, c_0_32]), ['final']).
% 0.21/0.41  cnf(c_0_41, plain, (k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2))=X2|~l1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_33]), ['final']).
% 0.21/0.41  cnf(c_0_42, plain, (k7_subset_1(X1,X2,X3)=k7_subset_1(X4,X2,X3)|~r1_tarski(X2,X1)|~r1_tarski(X2,X4)), inference(spm,[status(thm)],[c_0_32, c_0_32]), ['final']).
% 0.21/0.41  cnf(c_0_43, plain, (k5_xboole_0(X1,X1)=k1_xboole_0|~r1_tarski(X1,k5_xboole_0(X1,k5_xboole_0(X2,X2)))|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_34, c_0_27])).
% 0.21/0.41  cnf(c_0_44, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[c_0_35, c_0_36]), ['final']).
% 0.21/0.41  cnf(c_0_45, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_37]), ['final']).
% 0.21/0.41  cnf(c_0_46, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_38]), ['final']).
% 0.21/0.41  cnf(c_0_47, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_39]), ['final']).
% 0.21/0.41  cnf(c_0_48, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k7_subset_1(X2,X3,X1))))=k1_xboole_0|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_26, c_0_32]), ['final']).
% 0.21/0.41  cnf(c_0_49, plain, (k7_subset_1(X1,X2,k5_xboole_0(X2,k7_subset_1(X3,X4,X2)))=k1_xboole_0|~r1_tarski(X2,X1)|~r1_tarski(X4,X3)), inference(spm,[status(thm)],[c_0_40, c_0_32]), ['final']).
% 0.21/0.41  cnf(c_0_50, plain, (k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(X2,k2_struct_0(X1),X3))=X3|~l1_struct_0(X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(k2_struct_0(X1),u1_struct_0(X1))|~r1_tarski(k2_struct_0(X1),X2)), inference(spm,[status(thm)],[c_0_41, c_0_42]), ['final']).
% 0.21/0.41  cnf(c_0_51, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_44]), c_0_45]), c_0_46])]), ['final']).
% 0.21/0.41  cnf(c_0_52, negated_conjecture, (k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,X1))=k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1)), inference(spm,[status(thm)],[c_0_24, c_0_47]), ['final']).
% 0.21/0.41  cnf(c_0_53, negated_conjecture, (esk2_0=k2_struct_0(esk1_0)|k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_39]), ['final']).
% 0.21/0.41  cnf(c_0_54, negated_conjecture, (l1_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_39]), ['final']).
% 0.21/0.41  cnf(c_0_55, plain, (k5_xboole_0(k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2),k3_xboole_0(k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2),k5_xboole_0(k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2),X2)))=k1_xboole_0|~l1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(k2_struct_0(X1),u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_48, c_0_41]), ['final']).
% 0.21/0.41  cnf(c_0_56, plain, (k7_subset_1(X1,k7_subset_1(X2,k2_struct_0(X3),X4),k5_xboole_0(k7_subset_1(X2,k2_struct_0(X3),X4),X4))=k1_xboole_0|~l1_struct_0(X3)|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))|~r1_tarski(k7_subset_1(X2,k2_struct_0(X3),X4),X1)|~r1_tarski(k2_struct_0(X3),u1_struct_0(X3))|~r1_tarski(k2_struct_0(X3),X2)), inference(spm,[status(thm)],[c_0_49, c_0_50]), ['final']).
% 0.21/0.41  cnf(c_0_57, plain, (k7_subset_1(X1,X2,X3)=k1_xboole_0|~r1_tarski(X2,X1)|~r1_tarski(X2,X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_27]), c_0_51]), ['final']).
% 0.21/0.41  cnf(c_0_58, negated_conjecture, (k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1))))=k1_xboole_0), inference(spm,[status(thm)],[c_0_26, c_0_52]), ['final']).
% 0.21/0.41  cnf(c_0_59, plain, (k7_subset_1(X1,k2_struct_0(X2),k7_subset_1(u1_struct_0(X2),k2_struct_0(X2),X3))=X3|~l1_struct_0(X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~r1_tarski(k2_struct_0(X2),u1_struct_0(X2))|~r1_tarski(k2_struct_0(X2),X1)), inference(spm,[status(thm)],[c_0_41, c_0_42]), ['final']).
% 0.21/0.41  cnf(c_0_60, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),k1_xboole_0)=esk2_0|k2_struct_0(esk1_0)=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_53]), c_0_54]), c_0_47])]), ['final']).
% 0.21/0.41  cnf(c_0_61, plain, (k7_subset_1(X1,X2,k1_xboole_0)=X2|~r1_tarski(X2,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_36]), c_0_44]), ['final']).
% 0.21/0.41  cnf(c_0_62, plain, (k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))),k3_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))),k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_26]), c_0_44])).
% 0.21/0.41  cnf(c_0_63, plain, (k5_xboole_0(k7_subset_1(X1,k2_struct_0(X2),X3),k3_xboole_0(k7_subset_1(X1,k2_struct_0(X2),X3),k5_xboole_0(k7_subset_1(X1,k2_struct_0(X2),X3),X3)))=k1_xboole_0|~l1_struct_0(X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~r1_tarski(k2_struct_0(X2),u1_struct_0(X2))|~r1_tarski(k2_struct_0(X2),X1)), inference(spm,[status(thm)],[c_0_55, c_0_42]), ['final']).
% 0.21/0.41  cnf(c_0_64, plain, (k7_subset_1(X1,k5_xboole_0(k2_struct_0(X2),k3_xboole_0(k2_struct_0(X2),X3)),k5_xboole_0(k5_xboole_0(k2_struct_0(X2),k3_xboole_0(k2_struct_0(X2),X3)),X3))=k1_xboole_0|~l1_struct_0(X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~r1_tarski(k5_xboole_0(k2_struct_0(X2),k3_xboole_0(k2_struct_0(X2),X3)),X1)|~r1_tarski(k2_struct_0(X2),u1_struct_0(X2))|~r1_tarski(k2_struct_0(X2),X4)), inference(spm,[status(thm)],[c_0_56, c_0_32]), ['final']).
% 0.21/0.41  cnf(c_0_65, plain, (k1_xboole_0=X1|~l1_struct_0(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~r1_tarski(k2_struct_0(X2),k7_subset_1(u1_struct_0(X2),k2_struct_0(X2),X1))|~r1_tarski(k2_struct_0(X2),u1_struct_0(X2))), inference(spm,[status(thm)],[c_0_41, c_0_57]), ['final']).
% 0.21/0.41  cnf(c_0_66, negated_conjecture, (k7_subset_1(X1,X2,k5_xboole_0(X2,k7_subset_1(u1_struct_0(esk1_0),esk2_0,X2)))=k1_xboole_0|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_32, c_0_58]), ['final']).
% 0.21/0.41  cnf(c_0_67, plain, (k5_xboole_0(k2_struct_0(X1),k5_xboole_0(X2,k3_xboole_0(X2,k2_struct_0(X1))))=k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k1_xboole_0)|~l1_struct_0(X1)|~m1_subset_1(k5_xboole_0(k2_struct_0(X1),k5_xboole_0(X2,k3_xboole_0(X2,k2_struct_0(X1)))),k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(k2_struct_0(X1),u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_41, c_0_40]), ['final']).
% 0.21/0.41  cnf(c_0_68, plain, (k7_subset_1(X1,k2_struct_0(X2),k7_subset_1(X3,k2_struct_0(X2),X4))=X4|~l1_struct_0(X2)|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))|~r1_tarski(k2_struct_0(X2),u1_struct_0(X2))|~r1_tarski(k2_struct_0(X2),X1)|~r1_tarski(k2_struct_0(X2),X3)), inference(spm,[status(thm)],[c_0_59, c_0_42]), ['final']).
% 0.21/0.41  cnf(c_0_69, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)!=k1_xboole_0|esk2_0!=k2_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_39]), ['final']).
% 0.21/0.41  cnf(c_0_70, negated_conjecture, (k2_struct_0(esk1_0)=esk2_0|~r1_tarski(k2_struct_0(esk1_0),u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_60, c_0_61]), ['final']).
% 0.21/0.41  cnf(c_0_71, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X1))=k1_xboole_0|~r1_tarski(X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_27]), c_0_51]), c_0_44]), c_0_51]), c_0_44]), c_0_51]), c_0_44])).
% 0.21/0.41  cnf(c_0_72, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_19]), ['final']).
% 0.21/0.41  cnf(c_0_73, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X2))=k1_xboole_0|~r1_tarski(X1,X3)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_32, c_0_57])).
% 0.21/0.41  cnf(c_0_74, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),esk2_0,k5_xboole_0(esk2_0,k5_xboole_0(X1,k3_xboole_0(X1,esk2_0))))=k1_xboole_0), inference(spm,[status(thm)],[c_0_26, c_0_52]), ['final']).
% 0.21/0.41  cnf(c_0_75, plain, (k5_xboole_0(k5_xboole_0(k2_struct_0(X1),k3_xboole_0(k2_struct_0(X1),X2)),k3_xboole_0(k5_xboole_0(k2_struct_0(X1),k3_xboole_0(k2_struct_0(X1),X2)),k5_xboole_0(k5_xboole_0(k2_struct_0(X1),k3_xboole_0(k2_struct_0(X1),X2)),X2)))=k1_xboole_0|~l1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(k2_struct_0(X1),u1_struct_0(X1))|~r1_tarski(k2_struct_0(X1),X3)), inference(spm,[status(thm)],[c_0_63, c_0_32]), ['final']).
% 0.21/0.41  cnf(c_0_76, plain, (k7_subset_1(k5_xboole_0(k2_struct_0(X1),k3_xboole_0(k2_struct_0(X1),X2)),k5_xboole_0(k2_struct_0(X1),k3_xboole_0(k2_struct_0(X1),X2)),k5_xboole_0(k5_xboole_0(k2_struct_0(X1),k3_xboole_0(k2_struct_0(X1),X2)),X2))=k1_xboole_0|~l1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(k2_struct_0(X1),u1_struct_0(X1))|~r1_tarski(k2_struct_0(X1),X3)), inference(spm,[status(thm)],[c_0_64, c_0_45]), ['final']).
% 0.21/0.41  cnf(c_0_77, plain, (k7_subset_1(X1,k2_struct_0(X2),k1_xboole_0)=k5_xboole_0(k2_struct_0(X2),k5_xboole_0(X3,k3_xboole_0(X3,k2_struct_0(X2))))|~l1_struct_0(X2)|~m1_subset_1(k5_xboole_0(k2_struct_0(X2),k5_xboole_0(X3,k3_xboole_0(X3,k2_struct_0(X2)))),k1_zfmisc_1(u1_struct_0(X2)))|~r1_tarski(k2_struct_0(X2),u1_struct_0(X2))|~r1_tarski(k2_struct_0(X2),X1)), inference(spm,[status(thm)],[c_0_59, c_0_40]), ['final']).
% 0.21/0.41  cnf(c_0_78, plain, (k7_subset_1(X1,k2_struct_0(X2),k1_xboole_0)=k5_xboole_0(k2_struct_0(X2),k7_subset_1(X3,X4,k2_struct_0(X2)))|~l1_struct_0(X2)|~m1_subset_1(k5_xboole_0(k2_struct_0(X2),k7_subset_1(X3,X4,k2_struct_0(X2))),k1_zfmisc_1(u1_struct_0(X2)))|~r1_tarski(k2_struct_0(X2),u1_struct_0(X2))|~r1_tarski(k2_struct_0(X2),X1)|~r1_tarski(X4,X3)), inference(spm,[status(thm)],[c_0_59, c_0_49]), ['final']).
% 0.21/0.41  cnf(c_0_79, plain, (k5_xboole_0(k2_struct_0(X1),k5_xboole_0(X2,k3_xboole_0(X2,k2_struct_0(X1))))=k1_xboole_0|~l1_struct_0(X1)|~m1_subset_1(k5_xboole_0(k2_struct_0(X1),k5_xboole_0(X2,k3_xboole_0(X2,k2_struct_0(X1)))),k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(k2_struct_0(X1),u1_struct_0(X1))|~r1_tarski(k2_struct_0(X1),k1_xboole_0)), inference(spm,[status(thm)],[c_0_65, c_0_40]), ['final']).
% 0.21/0.41  cnf(c_0_80, negated_conjecture, (k7_subset_1(X1,k2_struct_0(X2),k1_xboole_0)=k5_xboole_0(k2_struct_0(X2),k7_subset_1(u1_struct_0(esk1_0),esk2_0,k2_struct_0(X2)))|~l1_struct_0(X2)|~m1_subset_1(k5_xboole_0(k2_struct_0(X2),k7_subset_1(u1_struct_0(esk1_0),esk2_0,k2_struct_0(X2))),k1_zfmisc_1(u1_struct_0(X2)))|~r1_tarski(k2_struct_0(X2),u1_struct_0(X2))|~r1_tarski(k2_struct_0(X2),X1)), inference(spm,[status(thm)],[c_0_59, c_0_66]), ['final']).
% 0.21/0.41  cnf(c_0_81, plain, (k5_xboole_0(k2_struct_0(X1),k7_subset_1(X2,X3,k2_struct_0(X1)))=k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k1_xboole_0)|~l1_struct_0(X1)|~m1_subset_1(k5_xboole_0(k2_struct_0(X1),k7_subset_1(X2,X3,k2_struct_0(X1))),k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(k2_struct_0(X1),u1_struct_0(X1))|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_67, c_0_32]), ['final']).
% 0.21/0.41  cnf(c_0_82, plain, (k5_xboole_0(k2_struct_0(X1),k7_subset_1(X2,X3,k2_struct_0(X1)))=k1_xboole_0|~l1_struct_0(X1)|~m1_subset_1(k5_xboole_0(k2_struct_0(X1),k7_subset_1(X2,X3,k2_struct_0(X1))),k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(k2_struct_0(X1),u1_struct_0(X1))|~r1_tarski(k2_struct_0(X1),k1_xboole_0)|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_65, c_0_49]), ['final']).
% 0.21/0.41  cnf(c_0_83, plain, (k7_subset_1(X1,k2_struct_0(X2),k5_xboole_0(k2_struct_0(X2),k3_xboole_0(k2_struct_0(X2),X3)))=X3|~l1_struct_0(X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~r1_tarski(k2_struct_0(X2),u1_struct_0(X2))|~r1_tarski(k2_struct_0(X2),X1)|~r1_tarski(k2_struct_0(X2),X4)), inference(spm,[status(thm)],[c_0_68, c_0_32]), ['final']).
% 0.21/0.41  cnf(c_0_84, plain, (k5_xboole_0(k2_struct_0(X1),k3_xboole_0(k2_struct_0(X1),k7_subset_1(X2,k2_struct_0(X1),X3)))=X3|~l1_struct_0(X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(k2_struct_0(X1),u1_struct_0(X1))|~r1_tarski(k2_struct_0(X1),X4)|~r1_tarski(k2_struct_0(X1),X2)), inference(spm,[status(thm)],[c_0_32, c_0_68]), ['final']).
% 0.21/0.41  cnf(c_0_85, negated_conjecture, (k5_xboole_0(k2_struct_0(X1),k7_subset_1(u1_struct_0(esk1_0),esk2_0,k2_struct_0(X1)))=k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k1_xboole_0)|~l1_struct_0(X1)|~m1_subset_1(k5_xboole_0(k2_struct_0(X1),k7_subset_1(u1_struct_0(esk1_0),esk2_0,k2_struct_0(X1))),k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(k2_struct_0(X1),u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_41, c_0_66]), ['final']).
% 0.21/0.41  cnf(c_0_86, plain, (k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k5_xboole_0(k2_struct_0(X1),k3_xboole_0(k2_struct_0(X1),X2)))=X2|~l1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(k2_struct_0(X1),u1_struct_0(X1))|~r1_tarski(k2_struct_0(X1),X3)), inference(spm,[status(thm)],[c_0_50, c_0_32]), ['final']).
% 0.21/0.41  cnf(c_0_87, negated_conjecture, (k5_xboole_0(k2_struct_0(X1),k7_subset_1(u1_struct_0(esk1_0),esk2_0,k2_struct_0(X1)))=k1_xboole_0|~l1_struct_0(X1)|~m1_subset_1(k5_xboole_0(k2_struct_0(X1),k7_subset_1(u1_struct_0(esk1_0),esk2_0,k2_struct_0(X1))),k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(k2_struct_0(X1),u1_struct_0(X1))|~r1_tarski(k2_struct_0(X1),k1_xboole_0)), inference(spm,[status(thm)],[c_0_65, c_0_66]), ['final']).
% 0.21/0.41  cnf(c_0_88, plain, (k5_xboole_0(k2_struct_0(X1),k3_xboole_0(k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2)))=X2|~l1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(k2_struct_0(X1),u1_struct_0(X1))|~r1_tarski(k2_struct_0(X1),X3)), inference(spm,[status(thm)],[c_0_32, c_0_59]), ['final']).
% 0.21/0.41  cnf(c_0_89, plain, (k7_subset_1(X1,k2_struct_0(X2),k1_xboole_0)=X3|~l1_struct_0(X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~r1_tarski(k2_struct_0(X2),u1_struct_0(X2))|~r1_tarski(k2_struct_0(X2),X1)|~r1_tarski(k2_struct_0(X2),X3)), inference(spm,[status(thm)],[c_0_59, c_0_57]), ['final']).
% 0.21/0.41  cnf(c_0_90, plain, (k1_xboole_0=X1|~l1_struct_0(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~r1_tarski(k2_struct_0(X2),k7_subset_1(X3,k2_struct_0(X2),X1))|~r1_tarski(k2_struct_0(X2),u1_struct_0(X2))|~r1_tarski(k2_struct_0(X2),X3)), inference(spm,[status(thm)],[c_0_65, c_0_42]), ['final']).
% 0.21/0.41  cnf(c_0_91, plain, (k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k1_xboole_0)=X2|~l1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(k2_struct_0(X1),u1_struct_0(X1))|~r1_tarski(k2_struct_0(X1),X2)), inference(spm,[status(thm)],[c_0_41, c_0_57]), ['final']).
% 0.21/0.41  cnf(c_0_92, plain, (k1_xboole_0=X1|~l1_struct_0(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~r1_tarski(k2_struct_0(X2),u1_struct_0(X2))|~r1_tarski(k2_struct_0(X2),k1_xboole_0)|~r1_tarski(k2_struct_0(X2),X1)), inference(spm,[status(thm)],[c_0_65, c_0_57]), ['final']).
% 0.21/0.41  cnf(c_0_93, negated_conjecture, (k7_subset_1(X1,k2_struct_0(esk1_0),esk2_0)!=k1_xboole_0|~r1_tarski(k2_struct_0(esk1_0),u1_struct_0(esk1_0))|~r1_tarski(k2_struct_0(esk1_0),X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_42]), c_0_70]), ['final']).
% 0.21/0.41  cnf(c_0_94, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X1))=k1_xboole_0), inference(spm,[status(thm)],[c_0_71, c_0_46]), ['final']).
% 0.21/0.41  cnf(c_0_95, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_30]), ['final']).
% 0.21/0.41  cnf(c_0_96, negated_conjecture, (r1_tarski(esk2_0,u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_72, c_0_47]), ['final']).
% 0.21/0.41  cnf(c_0_97, plain, (k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1))=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_46]), c_0_46])]), ['final']).
% 0.21/0.41  cnf(c_0_98, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),esk2_0,esk2_0)=k1_xboole_0|~r1_tarski(X1,esk2_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_27]), c_0_51]), c_0_44])).
% 0.21/0.41  cnf(c_0_99, plain, (k5_xboole_0(k5_xboole_0(k2_struct_0(X1),k3_xboole_0(k2_struct_0(X1),X2)),k3_xboole_0(k5_xboole_0(k2_struct_0(X1),k3_xboole_0(k2_struct_0(X1),X2)),k5_xboole_0(k5_xboole_0(k2_struct_0(X1),k3_xboole_0(k2_struct_0(X1),X2)),X2)))=k1_xboole_0|~l1_struct_0(X1)|~r1_tarski(k2_struct_0(X1),u1_struct_0(X1))|~r1_tarski(k2_struct_0(X1),X3)|~r1_tarski(X2,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_75, c_0_25]), ['final']).
% 0.21/0.41  cnf(c_0_100, plain, (k7_subset_1(k5_xboole_0(k2_struct_0(X1),k3_xboole_0(k2_struct_0(X1),X2)),k5_xboole_0(k2_struct_0(X1),k3_xboole_0(k2_struct_0(X1),X2)),k5_xboole_0(k5_xboole_0(k2_struct_0(X1),k3_xboole_0(k2_struct_0(X1),X2)),X2))=k1_xboole_0|~l1_struct_0(X1)|~r1_tarski(k2_struct_0(X1),u1_struct_0(X1))|~r1_tarski(k2_struct_0(X1),X3)|~r1_tarski(X2,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_76, c_0_25]), ['final']).
% 0.21/0.41  cnf(c_0_101, negated_conjecture, (k7_subset_1(k5_xboole_0(k2_struct_0(esk1_0),k3_xboole_0(k2_struct_0(esk1_0),esk2_0)),k5_xboole_0(k2_struct_0(esk1_0),k3_xboole_0(k2_struct_0(esk1_0),esk2_0)),k5_xboole_0(k5_xboole_0(k2_struct_0(esk1_0),k3_xboole_0(k2_struct_0(esk1_0),esk2_0)),esk2_0))=k1_xboole_0|~r1_tarski(k2_struct_0(esk1_0),u1_struct_0(esk1_0))|~r1_tarski(k2_struct_0(esk1_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_47]), c_0_54])]), ['final']).
% 0.21/0.41  cnf(c_0_102, negated_conjecture, (k5_xboole_0(k5_xboole_0(k2_struct_0(esk1_0),k3_xboole_0(k2_struct_0(esk1_0),esk2_0)),k3_xboole_0(k5_xboole_0(k2_struct_0(esk1_0),k3_xboole_0(k2_struct_0(esk1_0),esk2_0)),k5_xboole_0(k5_xboole_0(k2_struct_0(esk1_0),k3_xboole_0(k2_struct_0(esk1_0),esk2_0)),esk2_0)))=k1_xboole_0|~r1_tarski(k2_struct_0(esk1_0),u1_struct_0(esk1_0))|~r1_tarski(k2_struct_0(esk1_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_47]), c_0_54])]), ['final']).
% 0.21/0.41  cnf(c_0_103, plain, (k7_subset_1(X1,k2_struct_0(X2),k1_xboole_0)=k5_xboole_0(k2_struct_0(X2),k5_xboole_0(X3,k3_xboole_0(X3,k2_struct_0(X2))))|~l1_struct_0(X2)|~r1_tarski(k5_xboole_0(k2_struct_0(X2),k5_xboole_0(X3,k3_xboole_0(X3,k2_struct_0(X2)))),u1_struct_0(X2))|~r1_tarski(k2_struct_0(X2),u1_struct_0(X2))|~r1_tarski(k2_struct_0(X2),X1)), inference(spm,[status(thm)],[c_0_77, c_0_25]), ['final']).
% 0.21/0.41  cnf(c_0_104, plain, (k7_subset_1(X1,k2_struct_0(X2),k1_xboole_0)=k5_xboole_0(k2_struct_0(X2),k7_subset_1(X3,X4,k2_struct_0(X2)))|~l1_struct_0(X2)|~r1_tarski(k5_xboole_0(k2_struct_0(X2),k7_subset_1(X3,X4,k2_struct_0(X2))),u1_struct_0(X2))|~r1_tarski(k2_struct_0(X2),u1_struct_0(X2))|~r1_tarski(k2_struct_0(X2),X1)|~r1_tarski(X4,X3)), inference(spm,[status(thm)],[c_0_78, c_0_25]), ['final']).
% 0.21/0.41  cnf(c_0_105, plain, (k5_xboole_0(k2_struct_0(X1),k5_xboole_0(X2,k3_xboole_0(X2,k2_struct_0(X1))))=k1_xboole_0|~l1_struct_0(X1)|~r1_tarski(k5_xboole_0(k2_struct_0(X1),k5_xboole_0(X2,k3_xboole_0(X2,k2_struct_0(X1)))),u1_struct_0(X1))|~r1_tarski(k2_struct_0(X1),u1_struct_0(X1))|~r1_tarski(k2_struct_0(X1),k1_xboole_0)), inference(spm,[status(thm)],[c_0_79, c_0_25]), ['final']).
% 0.21/0.41  cnf(c_0_106, negated_conjecture, (k7_subset_1(X1,k2_struct_0(X2),k1_xboole_0)=k5_xboole_0(k2_struct_0(X2),k7_subset_1(u1_struct_0(esk1_0),esk2_0,k2_struct_0(X2)))|~l1_struct_0(X2)|~r1_tarski(k5_xboole_0(k2_struct_0(X2),k7_subset_1(u1_struct_0(esk1_0),esk2_0,k2_struct_0(X2))),u1_struct_0(X2))|~r1_tarski(k2_struct_0(X2),u1_struct_0(X2))|~r1_tarski(k2_struct_0(X2),X1)), inference(spm,[status(thm)],[c_0_80, c_0_25]), ['final']).
% 0.21/0.41  cnf(c_0_107, plain, (k7_subset_1(X1,k7_subset_1(u1_struct_0(X2),k2_struct_0(X2),X3),k5_xboole_0(k7_subset_1(u1_struct_0(X2),k2_struct_0(X2),X3),X3))=k1_xboole_0|~l1_struct_0(X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~r1_tarski(k7_subset_1(u1_struct_0(X2),k2_struct_0(X2),X3),X1)|~r1_tarski(k2_struct_0(X2),u1_struct_0(X2))), inference(spm,[status(thm)],[c_0_49, c_0_41]), ['final']).
% 0.21/0.41  cnf(c_0_108, plain, (k5_xboole_0(k2_struct_0(X1),k7_subset_1(X2,X3,k2_struct_0(X1)))=k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k1_xboole_0)|~l1_struct_0(X1)|~r1_tarski(k5_xboole_0(k2_struct_0(X1),k7_subset_1(X2,X3,k2_struct_0(X1))),u1_struct_0(X1))|~r1_tarski(k2_struct_0(X1),u1_struct_0(X1))|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_81, c_0_25]), ['final']).
% 0.21/0.41  cnf(c_0_109, plain, (k5_xboole_0(k2_struct_0(X1),k7_subset_1(X2,X3,k2_struct_0(X1)))=k1_xboole_0|~l1_struct_0(X1)|~r1_tarski(k5_xboole_0(k2_struct_0(X1),k7_subset_1(X2,X3,k2_struct_0(X1))),u1_struct_0(X1))|~r1_tarski(k2_struct_0(X1),u1_struct_0(X1))|~r1_tarski(k2_struct_0(X1),k1_xboole_0)|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_82, c_0_25]), ['final']).
% 0.21/0.41  cnf(c_0_110, plain, (k7_subset_1(X1,k2_struct_0(X2),k5_xboole_0(k2_struct_0(X2),k3_xboole_0(k2_struct_0(X2),X3)))=X3|~l1_struct_0(X2)|~r1_tarski(k2_struct_0(X2),u1_struct_0(X2))|~r1_tarski(k2_struct_0(X2),X1)|~r1_tarski(k2_struct_0(X2),X4)|~r1_tarski(X3,u1_struct_0(X2))), inference(spm,[status(thm)],[c_0_83, c_0_25]), ['final']).
% 0.21/0.41  cnf(c_0_111, negated_conjecture, (k7_subset_1(X1,k2_struct_0(esk1_0),k5_xboole_0(k2_struct_0(esk1_0),k3_xboole_0(k2_struct_0(esk1_0),esk2_0)))=esk2_0|~r1_tarski(k2_struct_0(esk1_0),u1_struct_0(esk1_0))|~r1_tarski(k2_struct_0(esk1_0),X1)|~r1_tarski(k2_struct_0(esk1_0),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_47]), c_0_54])]), ['final']).
% 0.21/0.41  cnf(c_0_112, plain, (k5_xboole_0(k2_struct_0(X1),k3_xboole_0(k2_struct_0(X1),k7_subset_1(X2,k2_struct_0(X1),X3)))=X3|~l1_struct_0(X1)|~r1_tarski(k2_struct_0(X1),u1_struct_0(X1))|~r1_tarski(k2_struct_0(X1),X4)|~r1_tarski(k2_struct_0(X1),X2)|~r1_tarski(X3,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_84, c_0_25]), ['final']).
% 0.21/0.41  cnf(c_0_113, negated_conjecture, (k5_xboole_0(k2_struct_0(esk1_0),k3_xboole_0(k2_struct_0(esk1_0),k7_subset_1(X1,k2_struct_0(esk1_0),esk2_0)))=esk2_0|~r1_tarski(k2_struct_0(esk1_0),u1_struct_0(esk1_0))|~r1_tarski(k2_struct_0(esk1_0),X2)|~r1_tarski(k2_struct_0(esk1_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_47]), c_0_54])]), ['final']).
% 0.21/0.41  cnf(c_0_114, plain, (k5_xboole_0(k2_struct_0(X1),k5_xboole_0(X2,k3_xboole_0(X2,k2_struct_0(X1))))=k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k1_xboole_0)|~l1_struct_0(X1)|~r1_tarski(k5_xboole_0(k2_struct_0(X1),k5_xboole_0(X2,k3_xboole_0(X2,k2_struct_0(X1)))),u1_struct_0(X1))|~r1_tarski(k2_struct_0(X1),u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_67, c_0_25]), ['final']).
% 0.21/0.41  cnf(c_0_115, negated_conjecture, (k5_xboole_0(k2_struct_0(X1),k7_subset_1(u1_struct_0(esk1_0),esk2_0,k2_struct_0(X1)))=k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k1_xboole_0)|~l1_struct_0(X1)|~r1_tarski(k5_xboole_0(k2_struct_0(X1),k7_subset_1(u1_struct_0(esk1_0),esk2_0,k2_struct_0(X1))),u1_struct_0(X1))|~r1_tarski(k2_struct_0(X1),u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_85, c_0_25]), ['final']).
% 0.21/0.41  cnf(c_0_116, plain, (k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k5_xboole_0(k2_struct_0(X1),k3_xboole_0(k2_struct_0(X1),X2)))=X2|~l1_struct_0(X1)|~r1_tarski(k2_struct_0(X1),u1_struct_0(X1))|~r1_tarski(k2_struct_0(X1),X3)|~r1_tarski(X2,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_86, c_0_25]), ['final']).
% 0.21/0.41  cnf(c_0_117, negated_conjecture, (k5_xboole_0(k2_struct_0(X1),k7_subset_1(u1_struct_0(esk1_0),esk2_0,k2_struct_0(X1)))=k1_xboole_0|~l1_struct_0(X1)|~r1_tarski(k5_xboole_0(k2_struct_0(X1),k7_subset_1(u1_struct_0(esk1_0),esk2_0,k2_struct_0(X1))),u1_struct_0(X1))|~r1_tarski(k2_struct_0(X1),u1_struct_0(X1))|~r1_tarski(k2_struct_0(X1),k1_xboole_0)), inference(spm,[status(thm)],[c_0_87, c_0_25]), ['final']).
% 0.21/0.41  cnf(c_0_118, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),k5_xboole_0(k2_struct_0(esk1_0),k3_xboole_0(k2_struct_0(esk1_0),esk2_0)))=esk2_0|~r1_tarski(k2_struct_0(esk1_0),u1_struct_0(esk1_0))|~r1_tarski(k2_struct_0(esk1_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_47]), c_0_54])]), ['final']).
% 0.21/0.41  cnf(c_0_119, plain, (k5_xboole_0(k2_struct_0(X1),k3_xboole_0(k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2)))=X2|~l1_struct_0(X1)|~r1_tarski(k2_struct_0(X1),u1_struct_0(X1))|~r1_tarski(k2_struct_0(X1),X3)|~r1_tarski(X2,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_88, c_0_25]), ['final']).
% 0.21/0.41  cnf(c_0_120, negated_conjecture, (k5_xboole_0(k2_struct_0(esk1_0),k3_xboole_0(k2_struct_0(esk1_0),k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)))=esk2_0|~r1_tarski(k2_struct_0(esk1_0),u1_struct_0(esk1_0))|~r1_tarski(k2_struct_0(esk1_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_47]), c_0_54])]), ['final']).
% 0.21/0.41  cnf(c_0_121, plain, (k7_subset_1(X1,k2_struct_0(X2),k1_xboole_0)=X3|~l1_struct_0(X2)|~r1_tarski(k2_struct_0(X2),u1_struct_0(X2))|~r1_tarski(k2_struct_0(X2),X1)|~r1_tarski(k2_struct_0(X2),X3)|~r1_tarski(X3,u1_struct_0(X2))), inference(spm,[status(thm)],[c_0_89, c_0_25]), ['final']).
% 0.21/0.41  cnf(c_0_122, plain, (k1_xboole_0=X1|~l1_struct_0(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~r1_tarski(k2_struct_0(X2),k5_xboole_0(k2_struct_0(X2),k3_xboole_0(k2_struct_0(X2),X1)))|~r1_tarski(k2_struct_0(X2),u1_struct_0(X2))|~r1_tarski(k2_struct_0(X2),X3)), inference(spm,[status(thm)],[c_0_90, c_0_32]), ['final']).
% 0.21/0.41  cnf(c_0_123, plain, (k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k1_xboole_0)=X2|~l1_struct_0(X1)|~r1_tarski(k2_struct_0(X1),u1_struct_0(X1))|~r1_tarski(k2_struct_0(X1),X2)|~r1_tarski(X2,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_91, c_0_25]), ['final']).
% 0.21/0.41  cnf(c_0_124, plain, (k1_xboole_0=X1|~l1_struct_0(X2)|~r1_tarski(k2_struct_0(X2),u1_struct_0(X2))|~r1_tarski(k2_struct_0(X2),k1_xboole_0)|~r1_tarski(k2_struct_0(X2),X1)|~r1_tarski(X1,u1_struct_0(X2))), inference(spm,[status(thm)],[c_0_92, c_0_25]), ['final']).
% 0.21/0.41  cnf(c_0_125, negated_conjecture, (k5_xboole_0(k2_struct_0(esk1_0),k3_xboole_0(k2_struct_0(esk1_0),esk2_0))!=k1_xboole_0|~r1_tarski(k2_struct_0(esk1_0),u1_struct_0(esk1_0))|~r1_tarski(k2_struct_0(esk1_0),X1)), inference(spm,[status(thm)],[c_0_93, c_0_32]), ['final']).
% 0.21/0.41  cnf(c_0_126, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),esk2_0,k5_xboole_0(esk2_0,k7_subset_1(X1,X2,esk2_0)))=k1_xboole_0|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_74, c_0_32]), ['final']).
% 0.21/0.41  cnf(c_0_127, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X2))=k1_xboole_0|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_73, c_0_45]), ['final']).
% 0.21/0.41  cnf(c_0_128, negated_conjecture, (~r1_tarski(k2_struct_0(esk1_0),u1_struct_0(esk1_0))|~r1_tarski(k2_struct_0(esk1_0),esk2_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_57]), c_0_70]), ['final']).
% 0.21/0.41  cnf(c_0_129, negated_conjecture, (k7_subset_1(X1,esk2_0,X2)=k7_subset_1(u1_struct_0(esk1_0),esk2_0,X2)|~r1_tarski(esk2_0,X1)), inference(spm,[status(thm)],[c_0_52, c_0_32]), ['final']).
% 0.21/0.41  cnf(c_0_130, plain, (k7_subset_1(X1,X2,X2)=k1_xboole_0|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_32, c_0_94]), ['final']).
% 0.21/0.41  cnf(c_0_131, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1)=k1_xboole_0|~r1_tarski(esk2_0,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_27]), c_0_51]), ['final']).
% 0.21/0.41  cnf(c_0_132, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_95, c_0_46]), ['final']).
% 0.21/0.41  cnf(c_0_133, negated_conjecture, (u1_struct_0(esk1_0)=esk2_0|~r1_tarski(u1_struct_0(esk1_0),esk2_0)), inference(spm,[status(thm)],[c_0_95, c_0_96]), ['final']).
% 0.21/0.41  cnf(c_0_134, plain, (k7_subset_1(X1,k1_xboole_0,X2)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_97]), c_0_46])]), ['final']).
% 0.21/0.41  cnf(c_0_135, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),esk2_0,esk2_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_98, c_0_46]), ['final']).
% 0.21/0.41  cnf(c_0_136, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),esk2_0,k1_xboole_0)=esk2_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_36]), c_0_44]), ['final']).
% 0.21/0.41  # SZS output end Saturation
% 0.21/0.41  # Proof object total steps             : 137
% 0.21/0.41  # Proof object clause steps            : 112
% 0.21/0.41  # Proof object formula steps           : 25
% 0.21/0.41  # Proof object conjectures             : 36
% 0.21/0.41  # Proof object clause conjectures      : 33
% 0.21/0.41  # Proof object formula conjectures     : 3
% 0.21/0.41  # Proof object initial clauses used    : 17
% 0.21/0.41  # Proof object initial formulas used   : 12
% 0.21/0.41  # Proof object generating inferences   : 89
% 0.21/0.41  # Proof object simplifying inferences  : 45
% 0.21/0.41  # Parsed axioms                        : 12
% 0.21/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.41  # Initial clauses                      : 20
% 0.21/0.41  # Removed in clause preprocessing      : 4
% 0.21/0.41  # Initial clauses in saturation        : 16
% 0.21/0.41  # Processed clauses                    : 603
% 0.21/0.41  # ...of these trivial                  : 6
% 0.21/0.41  # ...subsumed                          : 464
% 0.21/0.41  # ...remaining for further processing  : 133
% 0.21/0.41  # Other redundant clauses eliminated   : 2
% 0.21/0.41  # Clauses deleted for lack of memory   : 0
% 0.21/0.41  # Backward-subsumed                    : 8
% 0.21/0.41  # Backward-rewritten                   : 10
% 0.21/0.41  # Generated clauses                    : 846
% 0.21/0.41  # ...of the previous two non-trivial   : 638
% 0.21/0.41  # Contextual simplify-reflections      : 2
% 0.21/0.41  # Paramodulations                      : 844
% 0.21/0.41  # Factorizations                       : 0
% 0.21/0.41  # Equation resolutions                 : 2
% 0.21/0.41  # Propositional unsat checks           : 0
% 0.21/0.41  #    Propositional check models        : 0
% 0.21/0.41  #    Propositional check unsatisfiable : 0
% 0.21/0.41  #    Propositional clauses             : 0
% 0.21/0.41  #    Propositional clauses after purity: 0
% 0.21/0.41  #    Propositional unsat core size     : 0
% 0.21/0.41  #    Propositional preprocessing time  : 0.000
% 0.21/0.41  #    Propositional encoding time       : 0.000
% 0.21/0.41  #    Propositional solver time         : 0.000
% 0.21/0.41  #    Success case prop preproc time    : 0.000
% 0.21/0.41  #    Success case prop encoding time   : 0.000
% 0.21/0.41  #    Success case prop solver time     : 0.000
% 0.21/0.41  # Current number of processed clauses  : 98
% 0.21/0.41  #    Positive orientable unit clauses  : 17
% 0.21/0.41  #    Positive unorientable unit clauses: 0
% 0.21/0.41  #    Negative unit clauses             : 0
% 0.21/0.41  #    Non-unit-clauses                  : 81
% 0.21/0.41  # Current number of unprocessed clauses: 0
% 0.21/0.41  # ...number of literals in the above   : 0
% 0.21/0.41  # Current number of archived formulas  : 0
% 0.21/0.41  # Current number of archived clauses   : 35
% 0.21/0.41  # Clause-clause subsumption calls (NU) : 5766
% 0.21/0.41  # Rec. Clause-clause subsumption calls : 2179
% 0.21/0.41  # Non-unit clause-clause subsumptions  : 474
% 0.21/0.41  # Unit Clause-clause subsumption calls : 4
% 0.21/0.41  # Rewrite failures with RHS unbound    : 0
% 0.21/0.41  # BW rewrite match attempts            : 37
% 0.21/0.41  # BW rewrite match successes           : 11
% 0.21/0.41  # Condensation attempts                : 0
% 0.21/0.41  # Condensation successes               : 0
% 0.21/0.41  # Termbank termtop insertions          : 20596
% 0.21/0.41  
% 0.21/0.41  # -------------------------------------------------
% 0.21/0.41  # User time                : 0.061 s
% 0.21/0.41  # System time              : 0.005 s
% 0.21/0.41  # Total time               : 0.066 s
% 0.21/0.41  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
