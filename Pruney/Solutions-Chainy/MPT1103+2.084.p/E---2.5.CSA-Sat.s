%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:08:46 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  117 (3230 expanded)
%              Number of clauses        :   80 (1348 expanded)
%              Number of leaves         :   18 ( 931 expanded)
%              Depth                    :   13
%              Number of atoms          :  298 (4357 expanded)
%              Number of equality atoms :  119 (3427 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   10 (   3 average)
%              Maximal term depth       :    8 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(t75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(redefinition_k7_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k7_subset_1(X1,X2,X3) = k4_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(involutiveness_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,k3_subset_1(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

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

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(dt_k2_subset_1,axiom,(
    ! [X1] : m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(t22_pre_topc,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2)) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_pre_topc)).

fof(c_0_18,plain,(
    ! [X48,X49] : k1_setfam_1(k2_tarski(X48,X49)) = k3_xboole_0(X48,X49) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_19,plain,(
    ! [X12,X13] : k1_enumset1(X12,X12,X13) = k2_tarski(X12,X13) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_20,plain,(
    ! [X8,X9] : k4_xboole_0(X8,X9) = k5_xboole_0(X8,k3_xboole_0(X8,X9)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_21,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_22,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_23,plain,(
    ! [X40,X41] :
      ( ~ m1_subset_1(X41,k1_zfmisc_1(X40))
      | k3_subset_1(X40,X41) = k4_xboole_0(X40,X41) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

cnf(c_0_24,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_25,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_21,c_0_22])).

fof(c_0_26,plain,(
    ! [X14,X15,X16] : k2_enumset1(X14,X14,X15,X16) = k1_enumset1(X14,X15,X16) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_27,plain,(
    ! [X17,X18,X19,X20] : k3_enumset1(X17,X17,X18,X19,X20) = k2_enumset1(X17,X18,X19,X20) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_28,plain,(
    ! [X21,X22,X23,X24,X25] : k4_enumset1(X21,X21,X22,X23,X24,X25) = k3_enumset1(X21,X22,X23,X24,X25) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_29,plain,(
    ! [X26,X27,X28,X29,X30,X31] : k5_enumset1(X26,X26,X27,X28,X29,X30,X31) = k4_enumset1(X26,X27,X28,X29,X30,X31) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_30,plain,(
    ! [X32,X33,X34,X35,X36,X37,X38] : k6_enumset1(X32,X32,X33,X34,X35,X36,X37,X38) = k5_enumset1(X32,X33,X34,X35,X36,X37,X38) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_31,plain,(
    ! [X45,X46,X47] :
      ( ~ m1_subset_1(X46,k1_zfmisc_1(X45))
      | k7_subset_1(X45,X46,X47) = k4_xboole_0(X46,X47) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).

cnf(c_0_32,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_33,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2))) ),
    inference(rw,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_34,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_35,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_36,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_37,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_38,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_39,plain,
    ( k7_subset_1(X2,X1,X3) = k4_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_40,plain,(
    ! [X43,X44] :
      ( ~ m1_subset_1(X44,k1_zfmisc_1(X43))
      | k3_subset_1(X43,k3_subset_1(X43,X44)) = X44 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).

cnf(c_0_41,plain,
    ( k3_subset_1(X2,X1) = k5_xboole_0(X2,k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_33]),c_0_34]),c_0_35]),c_0_36]),c_0_37]),c_0_38]),
    [final]).

cnf(c_0_42,plain,
    ( k7_subset_1(X2,X1,X3) = k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_33]),c_0_34]),c_0_35]),c_0_36]),c_0_37]),c_0_38]),
    [final]).

cnf(c_0_43,plain,
    ( k3_subset_1(X2,k3_subset_1(X2,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_40]),
    [final]).

cnf(c_0_44,plain,
    ( k7_subset_1(X1,X2,X3) = k3_subset_1(X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42]),
    [final]).

fof(c_0_45,negated_conjecture,(
    ~ ! [X1] :
        ( l1_struct_0(X1)
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( ~ ( X2 != k2_struct_0(X1)
                  & k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2) = k1_xboole_0 )
              & ~ ( k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2) != k1_xboole_0
                  & X2 = k2_struct_0(X1) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t23_pre_topc])).

fof(c_0_46,plain,(
    ! [X11] : k4_xboole_0(X11,k1_xboole_0) = X11 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

fof(c_0_47,plain,(
    ! [X50,X51] :
      ( ( ~ m1_subset_1(X50,k1_zfmisc_1(X51))
        | r1_tarski(X50,X51) )
      & ( ~ r1_tarski(X50,X51)
        | m1_subset_1(X50,k1_zfmisc_1(X51)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_48,plain,(
    ! [X10] : r1_tarski(k1_xboole_0,X10) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_49,plain,
    ( k3_subset_1(X1,k7_subset_1(X2,X1,X3)) = X3
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44]),
    [final]).

fof(c_0_50,negated_conjecture,
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
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_45])])])])).

fof(c_0_51,plain,(
    ! [X42] : m1_subset_1(k2_subset_1(X42),k1_zfmisc_1(X42)) ),
    inference(variable_rename,[status(thm)],[dt_k2_subset_1])).

fof(c_0_52,plain,(
    ! [X39] : k2_subset_1(X39) = X39 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

cnf(c_0_53,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_54,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_47]),
    [final]).

cnf(c_0_55,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48]),
    [final]).

cnf(c_0_56,plain,
    ( k3_subset_1(X1,k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))) = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_42]),
    [final]).

cnf(c_0_57,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_50]),
    [final]).

cnf(c_0_58,plain,
    ( m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_59,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

fof(c_0_60,plain,(
    ! [X52,X53] :
      ( ~ l1_struct_0(X52)
      | ~ m1_subset_1(X53,k1_zfmisc_1(u1_struct_0(X52)))
      | k7_subset_1(u1_struct_0(X52),k2_struct_0(X52),k7_subset_1(u1_struct_0(X52),k2_struct_0(X52),X53)) = X53 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t22_pre_topc])])])).

cnf(c_0_61,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k1_xboole_0))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53,c_0_33]),c_0_34]),c_0_35]),c_0_36]),c_0_37]),c_0_38]),
    [final]).

cnf(c_0_62,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55]),
    [final]).

cnf(c_0_63,negated_conjecture,
    ( k3_subset_1(u1_struct_0(esk1_0),k5_xboole_0(u1_struct_0(esk1_0),k1_setfam_1(k6_enumset1(u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),esk2_0)))) = esk2_0
    | ~ m1_subset_1(u1_struct_0(esk1_0),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_64,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_58,c_0_59]),
    [final]).

cnf(c_0_65,plain,
    ( k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2)) = X2
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_60]),
    [final]).

cnf(c_0_66,negated_conjecture,
    ( esk2_0 = k2_struct_0(esk1_0)
    | k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_50]),
    [final]).

cnf(c_0_67,negated_conjecture,
    ( l1_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_50]),
    [final]).

cnf(c_0_68,plain,
    ( k3_subset_1(X1,k1_xboole_0) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_41]),c_0_62])]),
    [final]).

cnf(c_0_69,plain,
    ( k7_subset_1(X1,X2,k3_subset_1(X2,X3)) = X3
    | ~ m1_subset_1(k3_subset_1(X2,X3),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44]),
    [final]).

cnf(c_0_70,plain,
    ( k7_subset_1(X1,X2,X3) = k7_subset_1(X4,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X4)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_42]),
    [final]).

cnf(c_0_71,negated_conjecture,
    ( k3_subset_1(u1_struct_0(esk1_0),k5_xboole_0(u1_struct_0(esk1_0),k1_setfam_1(k6_enumset1(u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),esk2_0)))) = esk2_0 ),
    inference(spm,[status(thm)],[c_0_63,c_0_64]),
    [final]).

cnf(c_0_72,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),k1_xboole_0) = esk2_0
    | k2_struct_0(esk1_0) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_67]),c_0_57])]),
    [final]).

cnf(c_0_73,plain,
    ( k7_subset_1(X1,X2,k1_xboole_0) = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_61,c_0_42]),
    [final]).

cnf(c_0_74,plain,
    ( k3_subset_1(X1,X1) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_68]),c_0_62])]),
    [final]).

cnf(c_0_75,plain,
    ( k3_subset_1(k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2)) = X2
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2),k1_zfmisc_1(k2_struct_0(X1)))
    | ~ m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_65,c_0_44]),
    [final]).

cnf(c_0_76,plain,
    ( k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2) = k3_subset_1(k2_struct_0(X1),X2)
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2),k1_zfmisc_1(k2_struct_0(X1)))
    | ~ m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_49,c_0_65]),
    [final]).

cnf(c_0_77,plain,
    ( k7_subset_1(X1,X2,k7_subset_1(X3,X2,X4)) = X4
    | ~ m1_subset_1(k7_subset_1(X3,X2,X4),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_69,c_0_44]),
    [final]).

cnf(c_0_78,plain,
    ( k7_subset_1(X1,k2_struct_0(X2),k7_subset_1(u1_struct_0(X2),k2_struct_0(X2),X3)) = X3
    | ~ l1_struct_0(X2)
    | ~ m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_65,c_0_70]),
    [final]).

cnf(c_0_79,plain,
    ( k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k3_subset_1(k2_struct_0(X1),X2)) = X2
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_65,c_0_44]),
    [final]).

cnf(c_0_80,negated_conjecture,
    ( k3_subset_1(u1_struct_0(esk1_0),k7_subset_1(X1,u1_struct_0(esk1_0),esk2_0)) = esk2_0
    | ~ m1_subset_1(u1_struct_0(esk1_0),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_71,c_0_42]),
    [final]).

cnf(c_0_81,negated_conjecture,
    ( k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_41]),c_0_57])]),
    [final]).

cnf(c_0_82,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0) != k1_xboole_0
    | esk2_0 != k2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_50]),
    [final]).

cnf(c_0_83,negated_conjecture,
    ( k2_struct_0(esk1_0) = esk2_0
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_72,c_0_73]),
    [final]).

cnf(c_0_84,plain,
    ( k7_subset_1(X1,X2,X2) = k1_xboole_0
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_44]),c_0_64])]),
    [final]).

cnf(c_0_85,plain,
    ( k3_subset_1(k2_struct_0(X1),k7_subset_1(X2,k2_struct_0(X1),X3)) = X3
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(k7_subset_1(X2,k2_struct_0(X1),X3),k1_zfmisc_1(k2_struct_0(X1)))
    | ~ m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_75,c_0_70]),
    [final]).

cnf(c_0_86,plain,
    ( k7_subset_1(X1,k2_struct_0(X2),X3) = k3_subset_1(k2_struct_0(X2),X3)
    | ~ l1_struct_0(X2)
    | ~ m1_subset_1(k7_subset_1(X1,k2_struct_0(X2),X3),k1_zfmisc_1(k2_struct_0(X2)))
    | ~ m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_76,c_0_70]),
    [final]).

cnf(c_0_87,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k7_subset_1(X2,X1,X3)))) = X3
    | ~ m1_subset_1(k7_subset_1(X2,X1,X3),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X4))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_77]),
    [final]).

cnf(c_0_88,plain,
    ( k7_subset_1(X1,k2_struct_0(X2),k7_subset_1(X3,k2_struct_0(X2),X4)) = X4
    | ~ l1_struct_0(X2)
    | ~ m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_78,c_0_70]),
    [final]).

cnf(c_0_89,plain,
    ( k7_subset_1(X1,k2_struct_0(X2),k3_subset_1(k2_struct_0(X2),X3)) = X3
    | ~ l1_struct_0(X2)
    | ~ m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(X2))) ),
    inference(spm,[status(thm)],[c_0_70,c_0_79]),
    [final]).

cnf(c_0_90,plain,
    ( k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(X2,k2_struct_0(X1),X3)) = X3
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_65,c_0_70]),
    [final]).

cnf(c_0_91,negated_conjecture,
    ( k7_subset_1(X1,u1_struct_0(esk1_0),k5_xboole_0(u1_struct_0(esk1_0),k1_setfam_1(k6_enumset1(u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),esk2_0)))) = esk2_0
    | ~ m1_subset_1(k5_xboole_0(u1_struct_0(esk1_0),k1_setfam_1(k6_enumset1(u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),esk2_0))),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(u1_struct_0(esk1_0),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_71]),
    [final]).

cnf(c_0_92,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k3_subset_1(X1,X2)))) = X2
    | ~ m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_69]),
    [final]).

cnf(c_0_93,negated_conjecture,
    ( k7_subset_1(X1,u1_struct_0(esk1_0),k7_subset_1(X2,u1_struct_0(esk1_0),esk2_0)) = esk2_0
    | ~ m1_subset_1(k7_subset_1(X2,u1_struct_0(esk1_0),esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(u1_struct_0(esk1_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(u1_struct_0(esk1_0),k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_80]),
    [final]).

cnf(c_0_94,negated_conjecture,
    ( k7_subset_1(X1,u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)) = esk2_0
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(u1_struct_0(esk1_0),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_81]),
    [final]).

cnf(c_0_95,negated_conjecture,
    ( k7_subset_1(X1,k2_struct_0(esk1_0),esk2_0) != k1_xboole_0
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_70]),c_0_83]),
    [final]).

cnf(c_0_96,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) = k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_84])).

cnf(c_0_97,plain,
    ( k3_subset_1(k2_struct_0(X1),k5_xboole_0(k2_struct_0(X1),k1_setfam_1(k6_enumset1(k2_struct_0(X1),k2_struct_0(X1),k2_struct_0(X1),k2_struct_0(X1),k2_struct_0(X1),k2_struct_0(X1),k2_struct_0(X1),X2)))) = X2
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(k5_xboole_0(k2_struct_0(X1),k1_setfam_1(k6_enumset1(k2_struct_0(X1),k2_struct_0(X1),k2_struct_0(X1),k2_struct_0(X1),k2_struct_0(X1),k2_struct_0(X1),k2_struct_0(X1),X2))),k1_zfmisc_1(k2_struct_0(X1)))
    | ~ m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_85,c_0_42]),
    [final]).

cnf(c_0_98,plain,
    ( k5_xboole_0(k2_struct_0(X1),k1_setfam_1(k6_enumset1(k2_struct_0(X1),k2_struct_0(X1),k2_struct_0(X1),k2_struct_0(X1),k2_struct_0(X1),k2_struct_0(X1),k2_struct_0(X1),X2))) = k3_subset_1(k2_struct_0(X1),X2)
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(k5_xboole_0(k2_struct_0(X1),k1_setfam_1(k6_enumset1(k2_struct_0(X1),k2_struct_0(X1),k2_struct_0(X1),k2_struct_0(X1),k2_struct_0(X1),k2_struct_0(X1),k2_struct_0(X1),X2))),k1_zfmisc_1(k2_struct_0(X1)))
    | ~ m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_86,c_0_42]),
    [final]).

cnf(c_0_99,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))))) = X2
    | ~ m1_subset_1(k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X4)) ),
    inference(spm,[status(thm)],[c_0_87,c_0_42]),
    [final]).

cnf(c_0_100,plain,
    ( k7_subset_1(X1,k2_struct_0(X2),k5_xboole_0(k2_struct_0(X2),k1_setfam_1(k6_enumset1(k2_struct_0(X2),k2_struct_0(X2),k2_struct_0(X2),k2_struct_0(X2),k2_struct_0(X2),k2_struct_0(X2),k2_struct_0(X2),X3)))) = X3
    | ~ l1_struct_0(X2)
    | ~ m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(X4)) ),
    inference(spm,[status(thm)],[c_0_88,c_0_42]),
    [final]).

cnf(c_0_101,plain,
    ( k5_xboole_0(k2_struct_0(X1),k1_setfam_1(k6_enumset1(k2_struct_0(X1),k2_struct_0(X1),k2_struct_0(X1),k2_struct_0(X1),k2_struct_0(X1),k2_struct_0(X1),k2_struct_0(X1),k7_subset_1(X2,k2_struct_0(X1),X3)))) = X3
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(X4))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_88]),
    [final]).

cnf(c_0_102,plain,
    ( k7_subset_1(X1,X2,k5_xboole_0(X2,k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)))) = X3
    | ~ m1_subset_1(k5_xboole_0(X2,k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3))),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X4)) ),
    inference(spm,[status(thm)],[c_0_77,c_0_42]),
    [final]).

cnf(c_0_103,plain,
    ( k5_xboole_0(k2_struct_0(X1),k1_setfam_1(k6_enumset1(k2_struct_0(X1),k2_struct_0(X1),k2_struct_0(X1),k2_struct_0(X1),k2_struct_0(X1),k2_struct_0(X1),k2_struct_0(X1),k3_subset_1(k2_struct_0(X1),X2)))) = X2
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_42,c_0_89]),
    [final]).

cnf(c_0_104,plain,
    ( k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k5_xboole_0(k2_struct_0(X1),k1_setfam_1(k6_enumset1(k2_struct_0(X1),k2_struct_0(X1),k2_struct_0(X1),k2_struct_0(X1),k2_struct_0(X1),k2_struct_0(X1),k2_struct_0(X1),X2)))) = X2
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_90,c_0_42]),
    [final]).

cnf(c_0_105,plain,
    ( k5_xboole_0(k2_struct_0(X1),k1_setfam_1(k6_enumset1(k2_struct_0(X1),k2_struct_0(X1),k2_struct_0(X1),k2_struct_0(X1),k2_struct_0(X1),k2_struct_0(X1),k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2)))) = X2
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_42,c_0_78]),
    [final]).

cnf(c_0_106,negated_conjecture,
    ( k5_xboole_0(u1_struct_0(esk1_0),k1_setfam_1(k6_enumset1(u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),k5_xboole_0(u1_struct_0(esk1_0),k1_setfam_1(k6_enumset1(u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),esk2_0)))))) = esk2_0
    | ~ m1_subset_1(k5_xboole_0(u1_struct_0(esk1_0),k1_setfam_1(k6_enumset1(u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),esk2_0))),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(u1_struct_0(esk1_0),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_91]),
    [final]).

cnf(c_0_107,negated_conjecture,
    ( k5_xboole_0(u1_struct_0(esk1_0),k1_setfam_1(k6_enumset1(u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),esk2_0))) = k3_subset_1(u1_struct_0(esk1_0),esk2_0)
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(u1_struct_0(esk1_0),k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_81]),c_0_57])]),
    [final]).

cnf(c_0_108,negated_conjecture,
    ( k5_xboole_0(u1_struct_0(esk1_0),k1_setfam_1(k6_enumset1(u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),esk2_0))) = k3_subset_1(u1_struct_0(esk1_0),esk2_0)
    | ~ m1_subset_1(k5_xboole_0(u1_struct_0(esk1_0),k1_setfam_1(k6_enumset1(u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),esk2_0))),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_43,c_0_71]),
    [final]).

cnf(c_0_109,negated_conjecture,
    ( k5_xboole_0(u1_struct_0(esk1_0),k1_setfam_1(k6_enumset1(u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),k7_subset_1(X1,u1_struct_0(esk1_0),esk2_0)))) = esk2_0
    | ~ m1_subset_1(k7_subset_1(X1,u1_struct_0(esk1_0),esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(u1_struct_0(esk1_0),k1_zfmisc_1(X2))
    | ~ m1_subset_1(u1_struct_0(esk1_0),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_93]),
    [final]).

cnf(c_0_110,negated_conjecture,
    ( k5_xboole_0(u1_struct_0(esk1_0),k1_setfam_1(k6_enumset1(u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)))) = esk2_0
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(u1_struct_0(esk1_0),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_94]),
    [final]).

cnf(c_0_111,negated_conjecture,
    ( k3_subset_1(u1_struct_0(esk1_0),esk2_0) = k7_subset_1(X1,u1_struct_0(esk1_0),esk2_0)
    | ~ m1_subset_1(k7_subset_1(X1,u1_struct_0(esk1_0),esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(u1_struct_0(esk1_0),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_80]),
    [final]).

cnf(c_0_112,negated_conjecture,
    ( k7_subset_1(X1,u1_struct_0(esk1_0),esk2_0) = k3_subset_1(u1_struct_0(esk1_0),esk2_0)
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(u1_struct_0(esk1_0),k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_81]),c_0_57])]),
    [final]).

cnf(c_0_113,negated_conjecture,
    ( k5_xboole_0(k2_struct_0(esk1_0),k1_setfam_1(k6_enumset1(k2_struct_0(esk1_0),k2_struct_0(esk1_0),k2_struct_0(esk1_0),k2_struct_0(esk1_0),k2_struct_0(esk1_0),k2_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0))) != k1_xboole_0
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_95,c_0_42]),
    [final]).

cnf(c_0_114,negated_conjecture,
    ( k3_subset_1(k2_struct_0(esk1_0),esk2_0) != k1_xboole_0
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(k2_struct_0(esk1_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_44]),c_0_83]),
    [final]).

cnf(c_0_115,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_47]),
    [final]).

cnf(c_0_116,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_96,c_0_64]),
    [final]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 11:45:02 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.34  # Version: 2.5pre002
% 0.20/0.35  # No SInE strategy applied
% 0.20/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.20/0.39  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.20/0.39  #
% 0.20/0.39  # Preprocessing time       : 0.027 s
% 0.20/0.39  # Presaturation interreduction done
% 0.20/0.39  
% 0.20/0.39  # No proof found!
% 0.20/0.39  # SZS status CounterSatisfiable
% 0.20/0.39  # SZS output start Saturation
% 0.20/0.39  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.20/0.39  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.20/0.39  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.20/0.39  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 0.20/0.39  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.20/0.39  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.20/0.39  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 0.20/0.39  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 0.20/0.39  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 0.20/0.39  fof(redefinition_k7_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k7_subset_1(X1,X2,X3)=k4_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 0.20/0.39  fof(involutiveness_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,k3_subset_1(X1,X2))=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 0.20/0.39  fof(t23_pre_topc, conjecture, ![X1]:(l1_struct_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(~((X2!=k2_struct_0(X1)&k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2)=k1_xboole_0))&~((k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2)!=k1_xboole_0&X2=k2_struct_0(X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_pre_topc)).
% 0.20/0.39  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 0.20/0.39  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.20/0.39  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.20/0.39  fof(dt_k2_subset_1, axiom, ![X1]:m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 0.20/0.39  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 0.20/0.39  fof(t22_pre_topc, axiom, ![X1]:(l1_struct_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2))=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_pre_topc)).
% 0.20/0.39  fof(c_0_18, plain, ![X48, X49]:k1_setfam_1(k2_tarski(X48,X49))=k3_xboole_0(X48,X49), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.20/0.39  fof(c_0_19, plain, ![X12, X13]:k1_enumset1(X12,X12,X13)=k2_tarski(X12,X13), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.20/0.39  fof(c_0_20, plain, ![X8, X9]:k4_xboole_0(X8,X9)=k5_xboole_0(X8,k3_xboole_0(X8,X9)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.20/0.39  cnf(c_0_21, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.39  cnf(c_0_22, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.39  fof(c_0_23, plain, ![X40, X41]:(~m1_subset_1(X41,k1_zfmisc_1(X40))|k3_subset_1(X40,X41)=k4_xboole_0(X40,X41)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 0.20/0.39  cnf(c_0_24, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.39  cnf(c_0_25, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_21, c_0_22])).
% 0.20/0.39  fof(c_0_26, plain, ![X14, X15, X16]:k2_enumset1(X14,X14,X15,X16)=k1_enumset1(X14,X15,X16), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.20/0.39  fof(c_0_27, plain, ![X17, X18, X19, X20]:k3_enumset1(X17,X17,X18,X19,X20)=k2_enumset1(X17,X18,X19,X20), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.20/0.39  fof(c_0_28, plain, ![X21, X22, X23, X24, X25]:k4_enumset1(X21,X21,X22,X23,X24,X25)=k3_enumset1(X21,X22,X23,X24,X25), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.20/0.39  fof(c_0_29, plain, ![X26, X27, X28, X29, X30, X31]:k5_enumset1(X26,X26,X27,X28,X29,X30,X31)=k4_enumset1(X26,X27,X28,X29,X30,X31), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.20/0.39  fof(c_0_30, plain, ![X32, X33, X34, X35, X36, X37, X38]:k6_enumset1(X32,X32,X33,X34,X35,X36,X37,X38)=k5_enumset1(X32,X33,X34,X35,X36,X37,X38), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.20/0.39  fof(c_0_31, plain, ![X45, X46, X47]:(~m1_subset_1(X46,k1_zfmisc_1(X45))|k7_subset_1(X45,X46,X47)=k4_xboole_0(X46,X47)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).
% 0.20/0.39  cnf(c_0_32, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.39  cnf(c_0_33, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2)))), inference(rw,[status(thm)],[c_0_24, c_0_25])).
% 0.20/0.39  cnf(c_0_34, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.39  cnf(c_0_35, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.39  cnf(c_0_36, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.39  cnf(c_0_37, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.20/0.39  cnf(c_0_38, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.39  cnf(c_0_39, plain, (k7_subset_1(X2,X1,X3)=k4_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.20/0.39  fof(c_0_40, plain, ![X43, X44]:(~m1_subset_1(X44,k1_zfmisc_1(X43))|k3_subset_1(X43,k3_subset_1(X43,X44))=X44), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).
% 0.20/0.39  cnf(c_0_41, plain, (k3_subset_1(X2,X1)=k5_xboole_0(X2,k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1)))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_33]), c_0_34]), c_0_35]), c_0_36]), c_0_37]), c_0_38]), ['final']).
% 0.20/0.39  cnf(c_0_42, plain, (k7_subset_1(X2,X1,X3)=k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X3)))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39, c_0_33]), c_0_34]), c_0_35]), c_0_36]), c_0_37]), c_0_38]), ['final']).
% 0.20/0.39  cnf(c_0_43, plain, (k3_subset_1(X2,k3_subset_1(X2,X1))=X1|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_40]), ['final']).
% 0.20/0.39  cnf(c_0_44, plain, (k7_subset_1(X1,X2,X3)=k3_subset_1(X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(X2))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_41, c_0_42]), ['final']).
% 0.20/0.39  fof(c_0_45, negated_conjecture, ~(![X1]:(l1_struct_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(~((X2!=k2_struct_0(X1)&k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2)=k1_xboole_0))&~((k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2)!=k1_xboole_0&X2=k2_struct_0(X1))))))), inference(assume_negation,[status(cth)],[t23_pre_topc])).
% 0.20/0.39  fof(c_0_46, plain, ![X11]:k4_xboole_0(X11,k1_xboole_0)=X11, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.20/0.39  fof(c_0_47, plain, ![X50, X51]:((~m1_subset_1(X50,k1_zfmisc_1(X51))|r1_tarski(X50,X51))&(~r1_tarski(X50,X51)|m1_subset_1(X50,k1_zfmisc_1(X51)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.20/0.39  fof(c_0_48, plain, ![X10]:r1_tarski(k1_xboole_0,X10), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.20/0.39  cnf(c_0_49, plain, (k3_subset_1(X1,k7_subset_1(X2,X1,X3))=X3|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_43, c_0_44]), ['final']).
% 0.20/0.39  fof(c_0_50, negated_conjecture, (l1_struct_0(esk1_0)&(m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&(((k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)!=k1_xboole_0|esk2_0!=k2_struct_0(esk1_0))&(esk2_0=k2_struct_0(esk1_0)|esk2_0!=k2_struct_0(esk1_0)))&((k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)!=k1_xboole_0|k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)=k1_xboole_0)&(esk2_0=k2_struct_0(esk1_0)|k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)=k1_xboole_0))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_45])])])])).
% 0.20/0.39  fof(c_0_51, plain, ![X42]:m1_subset_1(k2_subset_1(X42),k1_zfmisc_1(X42)), inference(variable_rename,[status(thm)],[dt_k2_subset_1])).
% 0.20/0.39  fof(c_0_52, plain, ![X39]:k2_subset_1(X39)=X39, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 0.20/0.39  cnf(c_0_53, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.20/0.39  cnf(c_0_54, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_47]), ['final']).
% 0.20/0.39  cnf(c_0_55, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_48]), ['final']).
% 0.20/0.39  cnf(c_0_56, plain, (k3_subset_1(X1,k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))))=X2|~m1_subset_1(X2,k1_zfmisc_1(X1))|~m1_subset_1(X1,k1_zfmisc_1(X3))), inference(spm,[status(thm)],[c_0_49, c_0_42]), ['final']).
% 0.20/0.39  cnf(c_0_57, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_50]), ['final']).
% 0.20/0.39  cnf(c_0_58, plain, (m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.20/0.39  cnf(c_0_59, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.20/0.39  fof(c_0_60, plain, ![X52, X53]:(~l1_struct_0(X52)|(~m1_subset_1(X53,k1_zfmisc_1(u1_struct_0(X52)))|k7_subset_1(u1_struct_0(X52),k2_struct_0(X52),k7_subset_1(u1_struct_0(X52),k2_struct_0(X52),X53))=X53)), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t22_pre_topc])])])).
% 0.20/0.39  cnf(c_0_61, plain, (k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k1_xboole_0)))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53, c_0_33]), c_0_34]), c_0_35]), c_0_36]), c_0_37]), c_0_38]), ['final']).
% 0.20/0.39  cnf(c_0_62, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_54, c_0_55]), ['final']).
% 0.20/0.39  cnf(c_0_63, negated_conjecture, (k3_subset_1(u1_struct_0(esk1_0),k5_xboole_0(u1_struct_0(esk1_0),k1_setfam_1(k6_enumset1(u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),esk2_0))))=esk2_0|~m1_subset_1(u1_struct_0(esk1_0),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.20/0.39  cnf(c_0_64, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_58, c_0_59]), ['final']).
% 0.20/0.39  cnf(c_0_65, plain, (k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2))=X2|~l1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_60]), ['final']).
% 0.20/0.39  cnf(c_0_66, negated_conjecture, (esk2_0=k2_struct_0(esk1_0)|k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_50]), ['final']).
% 0.20/0.39  cnf(c_0_67, negated_conjecture, (l1_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_50]), ['final']).
% 0.20/0.39  cnf(c_0_68, plain, (k3_subset_1(X1,k1_xboole_0)=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_41]), c_0_62])]), ['final']).
% 0.20/0.39  cnf(c_0_69, plain, (k7_subset_1(X1,X2,k3_subset_1(X2,X3))=X3|~m1_subset_1(k3_subset_1(X2,X3),k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_43, c_0_44]), ['final']).
% 0.20/0.39  cnf(c_0_70, plain, (k7_subset_1(X1,X2,X3)=k7_subset_1(X4,X2,X3)|~m1_subset_1(X2,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X4))), inference(spm,[status(thm)],[c_0_42, c_0_42]), ['final']).
% 0.20/0.39  cnf(c_0_71, negated_conjecture, (k3_subset_1(u1_struct_0(esk1_0),k5_xboole_0(u1_struct_0(esk1_0),k1_setfam_1(k6_enumset1(u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),esk2_0))))=esk2_0), inference(spm,[status(thm)],[c_0_63, c_0_64]), ['final']).
% 0.20/0.39  cnf(c_0_72, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),k1_xboole_0)=esk2_0|k2_struct_0(esk1_0)=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_67]), c_0_57])]), ['final']).
% 0.20/0.39  cnf(c_0_73, plain, (k7_subset_1(X1,X2,k1_xboole_0)=X2|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_61, c_0_42]), ['final']).
% 0.20/0.39  cnf(c_0_74, plain, (k3_subset_1(X1,X1)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_68]), c_0_62])]), ['final']).
% 0.20/0.39  cnf(c_0_75, plain, (k3_subset_1(k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2))=X2|~l1_struct_0(X1)|~m1_subset_1(k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2),k1_zfmisc_1(k2_struct_0(X1)))|~m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_65, c_0_44]), ['final']).
% 0.20/0.39  cnf(c_0_76, plain, (k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2)=k3_subset_1(k2_struct_0(X1),X2)|~l1_struct_0(X1)|~m1_subset_1(k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2),k1_zfmisc_1(k2_struct_0(X1)))|~m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_49, c_0_65]), ['final']).
% 0.20/0.39  cnf(c_0_77, plain, (k7_subset_1(X1,X2,k7_subset_1(X3,X2,X4))=X4|~m1_subset_1(k7_subset_1(X3,X2,X4),k1_zfmisc_1(X2))|~m1_subset_1(X4,k1_zfmisc_1(X2))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(spm,[status(thm)],[c_0_69, c_0_44]), ['final']).
% 0.20/0.39  cnf(c_0_78, plain, (k7_subset_1(X1,k2_struct_0(X2),k7_subset_1(u1_struct_0(X2),k2_struct_0(X2),X3))=X3|~l1_struct_0(X2)|~m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_65, c_0_70]), ['final']).
% 0.20/0.39  cnf(c_0_79, plain, (k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k3_subset_1(k2_struct_0(X1),X2))=X2|~l1_struct_0(X1)|~m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(X1)))), inference(spm,[status(thm)],[c_0_65, c_0_44]), ['final']).
% 0.20/0.39  cnf(c_0_80, negated_conjecture, (k3_subset_1(u1_struct_0(esk1_0),k7_subset_1(X1,u1_struct_0(esk1_0),esk2_0))=esk2_0|~m1_subset_1(u1_struct_0(esk1_0),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_71, c_0_42]), ['final']).
% 0.20/0.39  cnf(c_0_81, negated_conjecture, (k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0))=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_41]), c_0_57])]), ['final']).
% 0.20/0.39  cnf(c_0_82, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)!=k1_xboole_0|esk2_0!=k2_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_50]), ['final']).
% 0.20/0.39  cnf(c_0_83, negated_conjecture, (k2_struct_0(esk1_0)=esk2_0|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_72, c_0_73]), ['final']).
% 0.20/0.39  cnf(c_0_84, plain, (k7_subset_1(X1,X2,X2)=k1_xboole_0|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_44]), c_0_64])]), ['final']).
% 0.20/0.39  cnf(c_0_85, plain, (k3_subset_1(k2_struct_0(X1),k7_subset_1(X2,k2_struct_0(X1),X3))=X3|~l1_struct_0(X1)|~m1_subset_1(k7_subset_1(X2,k2_struct_0(X1),X3),k1_zfmisc_1(k2_struct_0(X1)))|~m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_75, c_0_70]), ['final']).
% 0.20/0.39  cnf(c_0_86, plain, (k7_subset_1(X1,k2_struct_0(X2),X3)=k3_subset_1(k2_struct_0(X2),X3)|~l1_struct_0(X2)|~m1_subset_1(k7_subset_1(X1,k2_struct_0(X2),X3),k1_zfmisc_1(k2_struct_0(X2)))|~m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_76, c_0_70]), ['final']).
% 0.20/0.39  cnf(c_0_87, plain, (k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k7_subset_1(X2,X1,X3))))=X3|~m1_subset_1(k7_subset_1(X2,X1,X3),k1_zfmisc_1(X1))|~m1_subset_1(X1,k1_zfmisc_1(X4))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_42, c_0_77]), ['final']).
% 0.20/0.39  cnf(c_0_88, plain, (k7_subset_1(X1,k2_struct_0(X2),k7_subset_1(X3,k2_struct_0(X2),X4))=X4|~l1_struct_0(X2)|~m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(X1))|~m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(X3))), inference(spm,[status(thm)],[c_0_78, c_0_70]), ['final']).
% 0.20/0.39  cnf(c_0_89, plain, (k7_subset_1(X1,k2_struct_0(X2),k3_subset_1(k2_struct_0(X2),X3))=X3|~l1_struct_0(X2)|~m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(X1))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(X2)))), inference(spm,[status(thm)],[c_0_70, c_0_79]), ['final']).
% 0.20/0.39  cnf(c_0_90, plain, (k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(X2,k2_struct_0(X1),X3))=X3|~l1_struct_0(X1)|~m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_65, c_0_70]), ['final']).
% 0.20/0.39  cnf(c_0_91, negated_conjecture, (k7_subset_1(X1,u1_struct_0(esk1_0),k5_xboole_0(u1_struct_0(esk1_0),k1_setfam_1(k6_enumset1(u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),esk2_0))))=esk2_0|~m1_subset_1(k5_xboole_0(u1_struct_0(esk1_0),k1_setfam_1(k6_enumset1(u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),esk2_0))),k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(u1_struct_0(esk1_0),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_44, c_0_71]), ['final']).
% 0.20/0.39  cnf(c_0_92, plain, (k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k3_subset_1(X1,X2))))=X2|~m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1))|~m1_subset_1(X1,k1_zfmisc_1(X3))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_42, c_0_69]), ['final']).
% 0.20/0.39  cnf(c_0_93, negated_conjecture, (k7_subset_1(X1,u1_struct_0(esk1_0),k7_subset_1(X2,u1_struct_0(esk1_0),esk2_0))=esk2_0|~m1_subset_1(k7_subset_1(X2,u1_struct_0(esk1_0),esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(u1_struct_0(esk1_0),k1_zfmisc_1(X1))|~m1_subset_1(u1_struct_0(esk1_0),k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_44, c_0_80]), ['final']).
% 0.20/0.39  cnf(c_0_94, negated_conjecture, (k7_subset_1(X1,u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0))=esk2_0|~m1_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(u1_struct_0(esk1_0),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_44, c_0_81]), ['final']).
% 0.20/0.39  cnf(c_0_95, negated_conjecture, (k7_subset_1(X1,k2_struct_0(esk1_0),esk2_0)!=k1_xboole_0|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_70]), c_0_83]), ['final']).
% 0.20/0.39  cnf(c_0_96, plain, (k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_42, c_0_84])).
% 0.20/0.39  cnf(c_0_97, plain, (k3_subset_1(k2_struct_0(X1),k5_xboole_0(k2_struct_0(X1),k1_setfam_1(k6_enumset1(k2_struct_0(X1),k2_struct_0(X1),k2_struct_0(X1),k2_struct_0(X1),k2_struct_0(X1),k2_struct_0(X1),k2_struct_0(X1),X2))))=X2|~l1_struct_0(X1)|~m1_subset_1(k5_xboole_0(k2_struct_0(X1),k1_setfam_1(k6_enumset1(k2_struct_0(X1),k2_struct_0(X1),k2_struct_0(X1),k2_struct_0(X1),k2_struct_0(X1),k2_struct_0(X1),k2_struct_0(X1),X2))),k1_zfmisc_1(k2_struct_0(X1)))|~m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(X3))), inference(spm,[status(thm)],[c_0_85, c_0_42]), ['final']).
% 0.20/0.39  cnf(c_0_98, plain, (k5_xboole_0(k2_struct_0(X1),k1_setfam_1(k6_enumset1(k2_struct_0(X1),k2_struct_0(X1),k2_struct_0(X1),k2_struct_0(X1),k2_struct_0(X1),k2_struct_0(X1),k2_struct_0(X1),X2)))=k3_subset_1(k2_struct_0(X1),X2)|~l1_struct_0(X1)|~m1_subset_1(k5_xboole_0(k2_struct_0(X1),k1_setfam_1(k6_enumset1(k2_struct_0(X1),k2_struct_0(X1),k2_struct_0(X1),k2_struct_0(X1),k2_struct_0(X1),k2_struct_0(X1),k2_struct_0(X1),X2))),k1_zfmisc_1(k2_struct_0(X1)))|~m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(X3))), inference(spm,[status(thm)],[c_0_86, c_0_42]), ['final']).
% 0.20/0.39  cnf(c_0_99, plain, (k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))))))=X2|~m1_subset_1(k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))),k1_zfmisc_1(X1))|~m1_subset_1(X1,k1_zfmisc_1(X3))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~m1_subset_1(X1,k1_zfmisc_1(X4))), inference(spm,[status(thm)],[c_0_87, c_0_42]), ['final']).
% 0.20/0.39  cnf(c_0_100, plain, (k7_subset_1(X1,k2_struct_0(X2),k5_xboole_0(k2_struct_0(X2),k1_setfam_1(k6_enumset1(k2_struct_0(X2),k2_struct_0(X2),k2_struct_0(X2),k2_struct_0(X2),k2_struct_0(X2),k2_struct_0(X2),k2_struct_0(X2),X3))))=X3|~l1_struct_0(X2)|~m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(X1))|~m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(X4))), inference(spm,[status(thm)],[c_0_88, c_0_42]), ['final']).
% 0.20/0.39  cnf(c_0_101, plain, (k5_xboole_0(k2_struct_0(X1),k1_setfam_1(k6_enumset1(k2_struct_0(X1),k2_struct_0(X1),k2_struct_0(X1),k2_struct_0(X1),k2_struct_0(X1),k2_struct_0(X1),k2_struct_0(X1),k7_subset_1(X2,k2_struct_0(X1),X3))))=X3|~l1_struct_0(X1)|~m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(X4))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_42, c_0_88]), ['final']).
% 0.20/0.39  cnf(c_0_102, plain, (k7_subset_1(X1,X2,k5_xboole_0(X2,k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3))))=X3|~m1_subset_1(k5_xboole_0(X2,k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3))),k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X4))), inference(spm,[status(thm)],[c_0_77, c_0_42]), ['final']).
% 0.20/0.39  cnf(c_0_103, plain, (k5_xboole_0(k2_struct_0(X1),k1_setfam_1(k6_enumset1(k2_struct_0(X1),k2_struct_0(X1),k2_struct_0(X1),k2_struct_0(X1),k2_struct_0(X1),k2_struct_0(X1),k2_struct_0(X1),k3_subset_1(k2_struct_0(X1),X2))))=X2|~l1_struct_0(X1)|~m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(X3))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(X1)))), inference(spm,[status(thm)],[c_0_42, c_0_89]), ['final']).
% 0.20/0.39  cnf(c_0_104, plain, (k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k5_xboole_0(k2_struct_0(X1),k1_setfam_1(k6_enumset1(k2_struct_0(X1),k2_struct_0(X1),k2_struct_0(X1),k2_struct_0(X1),k2_struct_0(X1),k2_struct_0(X1),k2_struct_0(X1),X2))))=X2|~l1_struct_0(X1)|~m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(X3))), inference(spm,[status(thm)],[c_0_90, c_0_42]), ['final']).
% 0.20/0.39  cnf(c_0_105, plain, (k5_xboole_0(k2_struct_0(X1),k1_setfam_1(k6_enumset1(k2_struct_0(X1),k2_struct_0(X1),k2_struct_0(X1),k2_struct_0(X1),k2_struct_0(X1),k2_struct_0(X1),k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2))))=X2|~l1_struct_0(X1)|~m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(X3))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_42, c_0_78]), ['final']).
% 0.20/0.39  cnf(c_0_106, negated_conjecture, (k5_xboole_0(u1_struct_0(esk1_0),k1_setfam_1(k6_enumset1(u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),k5_xboole_0(u1_struct_0(esk1_0),k1_setfam_1(k6_enumset1(u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),esk2_0))))))=esk2_0|~m1_subset_1(k5_xboole_0(u1_struct_0(esk1_0),k1_setfam_1(k6_enumset1(u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),esk2_0))),k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(u1_struct_0(esk1_0),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_42, c_0_91]), ['final']).
% 0.20/0.39  cnf(c_0_107, negated_conjecture, (k5_xboole_0(u1_struct_0(esk1_0),k1_setfam_1(k6_enumset1(u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),esk2_0)))=k3_subset_1(u1_struct_0(esk1_0),esk2_0)|~m1_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(u1_struct_0(esk1_0),k1_zfmisc_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_81]), c_0_57])]), ['final']).
% 0.20/0.39  cnf(c_0_108, negated_conjecture, (k5_xboole_0(u1_struct_0(esk1_0),k1_setfam_1(k6_enumset1(u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),esk2_0)))=k3_subset_1(u1_struct_0(esk1_0),esk2_0)|~m1_subset_1(k5_xboole_0(u1_struct_0(esk1_0),k1_setfam_1(k6_enumset1(u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),esk2_0))),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_43, c_0_71]), ['final']).
% 0.20/0.39  cnf(c_0_109, negated_conjecture, (k5_xboole_0(u1_struct_0(esk1_0),k1_setfam_1(k6_enumset1(u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),k7_subset_1(X1,u1_struct_0(esk1_0),esk2_0))))=esk2_0|~m1_subset_1(k7_subset_1(X1,u1_struct_0(esk1_0),esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(u1_struct_0(esk1_0),k1_zfmisc_1(X2))|~m1_subset_1(u1_struct_0(esk1_0),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_42, c_0_93]), ['final']).
% 0.20/0.39  cnf(c_0_110, negated_conjecture, (k5_xboole_0(u1_struct_0(esk1_0),k1_setfam_1(k6_enumset1(u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0))))=esk2_0|~m1_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(u1_struct_0(esk1_0),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_42, c_0_94]), ['final']).
% 0.20/0.39  cnf(c_0_111, negated_conjecture, (k3_subset_1(u1_struct_0(esk1_0),esk2_0)=k7_subset_1(X1,u1_struct_0(esk1_0),esk2_0)|~m1_subset_1(k7_subset_1(X1,u1_struct_0(esk1_0),esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(u1_struct_0(esk1_0),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_43, c_0_80]), ['final']).
% 0.20/0.39  cnf(c_0_112, negated_conjecture, (k7_subset_1(X1,u1_struct_0(esk1_0),esk2_0)=k3_subset_1(u1_struct_0(esk1_0),esk2_0)|~m1_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(u1_struct_0(esk1_0),k1_zfmisc_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_81]), c_0_57])]), ['final']).
% 0.20/0.39  cnf(c_0_113, negated_conjecture, (k5_xboole_0(k2_struct_0(esk1_0),k1_setfam_1(k6_enumset1(k2_struct_0(esk1_0),k2_struct_0(esk1_0),k2_struct_0(esk1_0),k2_struct_0(esk1_0),k2_struct_0(esk1_0),k2_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)))!=k1_xboole_0|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_95, c_0_42]), ['final']).
% 0.20/0.39  cnf(c_0_114, negated_conjecture, (k3_subset_1(k2_struct_0(esk1_0),esk2_0)!=k1_xboole_0|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(esk2_0,k1_zfmisc_1(k2_struct_0(esk1_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_44]), c_0_83]), ['final']).
% 0.20/0.39  cnf(c_0_115, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_47]), ['final']).
% 0.20/0.39  cnf(c_0_116, plain, (k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))=k1_xboole_0), inference(spm,[status(thm)],[c_0_96, c_0_64]), ['final']).
% 0.20/0.39  # SZS output end Saturation
% 0.20/0.39  # Proof object total steps             : 117
% 0.20/0.39  # Proof object clause steps            : 80
% 0.20/0.39  # Proof object formula steps           : 37
% 0.20/0.39  # Proof object conjectures             : 26
% 0.20/0.39  # Proof object clause conjectures      : 23
% 0.20/0.39  # Proof object formula conjectures     : 3
% 0.20/0.39  # Proof object initial clauses used    : 22
% 0.20/0.39  # Proof object initial formulas used   : 18
% 0.20/0.39  # Proof object generating inferences   : 52
% 0.20/0.39  # Proof object simplifying inferences  : 38
% 0.20/0.39  # Parsed axioms                        : 18
% 0.20/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.39  # Initial clauses                      : 24
% 0.20/0.39  # Removed in clause preprocessing      : 11
% 0.20/0.39  # Initial clauses in saturation        : 13
% 0.20/0.39  # Processed clauses                    : 342
% 0.20/0.39  # ...of these trivial                  : 0
% 0.20/0.39  # ...subsumed                          : 261
% 0.20/0.39  # ...remaining for further processing  : 81
% 0.20/0.39  # Other redundant clauses eliminated   : 0
% 0.20/0.39  # Clauses deleted for lack of memory   : 0
% 0.20/0.39  # Backward-subsumed                    : 2
% 0.20/0.39  # Backward-rewritten                   : 3
% 0.20/0.39  # Generated clauses                    : 354
% 0.20/0.39  # ...of the previous two non-trivial   : 318
% 0.20/0.39  # Contextual simplify-reflections      : 2
% 0.20/0.39  # Paramodulations                      : 354
% 0.20/0.39  # Factorizations                       : 0
% 0.20/0.39  # Equation resolutions                 : 0
% 0.20/0.39  # Propositional unsat checks           : 0
% 0.20/0.39  #    Propositional check models        : 0
% 0.20/0.39  #    Propositional check unsatisfiable : 0
% 0.20/0.39  #    Propositional clauses             : 0
% 0.20/0.39  #    Propositional clauses after purity: 0
% 0.20/0.39  #    Propositional unsat core size     : 0
% 0.20/0.39  #    Propositional preprocessing time  : 0.000
% 0.20/0.39  #    Propositional encoding time       : 0.000
% 0.20/0.39  #    Propositional solver time         : 0.000
% 0.20/0.39  #    Success case prop preproc time    : 0.000
% 0.20/0.39  #    Success case prop encoding time   : 0.000
% 0.20/0.39  #    Success case prop solver time     : 0.000
% 0.20/0.39  # Current number of processed clauses  : 63
% 0.20/0.39  #    Positive orientable unit clauses  : 11
% 0.20/0.39  #    Positive unorientable unit clauses: 0
% 0.20/0.39  #    Negative unit clauses             : 0
% 0.20/0.39  #    Non-unit-clauses                  : 52
% 0.20/0.39  # Current number of unprocessed clauses: 0
% 0.20/0.39  # ...number of literals in the above   : 0
% 0.20/0.39  # Current number of archived formulas  : 0
% 0.20/0.39  # Current number of archived clauses   : 27
% 0.20/0.39  # Clause-clause subsumption calls (NU) : 1310
% 0.20/0.39  # Rec. Clause-clause subsumption calls : 481
% 0.20/0.39  # Non-unit clause-clause subsumptions  : 265
% 0.20/0.39  # Unit Clause-clause subsumption calls : 0
% 0.20/0.39  # Rewrite failures with RHS unbound    : 0
% 0.20/0.39  # BW rewrite match attempts            : 12
% 0.20/0.39  # BW rewrite match successes           : 3
% 0.20/0.39  # Condensation attempts                : 0
% 0.20/0.39  # Condensation successes               : 0
% 0.20/0.39  # Termbank termtop insertions          : 13072
% 0.20/0.39  
% 0.20/0.39  # -------------------------------------------------
% 0.20/0.39  # User time                : 0.041 s
% 0.20/0.39  # System time              : 0.008 s
% 0.20/0.39  # Total time               : 0.049 s
% 0.20/0.39  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
