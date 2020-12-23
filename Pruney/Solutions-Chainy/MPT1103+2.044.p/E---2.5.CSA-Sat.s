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
% DateTime   : Thu Dec  3 11:08:41 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 697 expanded)
%              Number of clauses        :   76 ( 323 expanded)
%              Number of leaves         :   18 ( 183 expanded)
%              Depth                    :    8
%              Number of atoms          :  278 (1885 expanded)
%              Number of equality atoms :  137 ( 929 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

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

fof(redefinition_k7_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k7_subset_1(X1,X2,X3) = k4_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(dt_k2_subset_1,axiom,(
    ! [X1] : m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(fc1_subset_1,axiom,(
    ! [X1] : ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(t92_xboole_1,axiom,(
    ! [X1] : k5_xboole_0(X1,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(involutiveness_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,k3_subset_1(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(t22_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = k3_subset_1(X1,k1_subset_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).

fof(d3_subset_1,axiom,(
    ! [X1] : k1_subset_1(X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

fof(c_0_18,plain,(
    ! [X35,X36] : k1_setfam_1(k2_tarski(X35,X36)) = k3_xboole_0(X35,X36) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_19,plain,(
    ! [X11,X12] : k1_enumset1(X11,X11,X12) = k2_tarski(X11,X12) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_20,plain,(
    ! [X16,X17,X18,X19,X20,X21] :
      ( ( ~ r2_hidden(X18,X17)
        | r1_tarski(X18,X16)
        | X17 != k1_zfmisc_1(X16) )
      & ( ~ r1_tarski(X19,X16)
        | r2_hidden(X19,X17)
        | X17 != k1_zfmisc_1(X16) )
      & ( ~ r2_hidden(esk1_2(X20,X21),X21)
        | ~ r1_tarski(esk1_2(X20,X21),X20)
        | X21 = k1_zfmisc_1(X20) )
      & ( r2_hidden(esk1_2(X20,X21),X21)
        | r1_tarski(esk1_2(X20,X21),X20)
        | X21 = k1_zfmisc_1(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

fof(c_0_21,plain,(
    ! [X6,X7] : k4_xboole_0(X6,X7) = k5_xboole_0(X6,k3_xboole_0(X6,X7)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_22,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_24,negated_conjecture,(
    ~ ! [X1] :
        ( l1_struct_0(X1)
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( ~ ( X2 != k2_struct_0(X1)
                  & k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2) = k1_xboole_0 )
              & ~ ( k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2) != k1_xboole_0
                  & X2 = k2_struct_0(X1) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t23_pre_topc])).

cnf(c_0_25,plain,
    ( r2_hidden(X1,X3)
    | ~ r1_tarski(X1,X2)
    | X3 != k1_zfmisc_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20]),
    [final]).

cnf(c_0_26,plain,
    ( r2_hidden(esk1_2(X1,X2),X2)
    | r1_tarski(esk1_2(X1,X2),X1)
    | X2 = k1_zfmisc_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20]),
    [final]).

fof(c_0_27,plain,(
    ! [X31,X32,X33] :
      ( ~ m1_subset_1(X32,k1_zfmisc_1(X31))
      | k7_subset_1(X31,X32,X33) = k4_xboole_0(X32,X33) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).

cnf(c_0_28,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_22,c_0_23])).

fof(c_0_30,plain,(
    ! [X13,X14,X15] : k2_enumset1(X13,X13,X14,X15) = k1_enumset1(X13,X14,X15) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_31,plain,(
    ! [X8,X9] :
      ( ~ r1_tarski(X8,X9)
      | k3_xboole_0(X8,X9) = X8 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

fof(c_0_32,plain,(
    ! [X25,X26] :
      ( ~ m1_subset_1(X26,k1_zfmisc_1(X25))
      | k3_subset_1(X25,X26) = k4_xboole_0(X25,X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

fof(c_0_33,plain,(
    ! [X27] : m1_subset_1(k2_subset_1(X27),k1_zfmisc_1(X27)) ),
    inference(variable_rename,[status(thm)],[dt_k2_subset_1])).

fof(c_0_34,plain,(
    ! [X24] : k2_subset_1(X24) = X24 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

fof(c_0_35,plain,(
    ! [X37,X38] :
      ( ~ m1_subset_1(X37,X38)
      | v1_xboole_0(X38)
      | r2_hidden(X37,X38) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_36,negated_conjecture,
    ( l1_struct_0(esk2_0)
    & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
    & ( k7_subset_1(u1_struct_0(esk2_0),k2_struct_0(esk2_0),esk3_0) != k1_xboole_0
      | esk3_0 != k2_struct_0(esk2_0) )
    & ( esk3_0 = k2_struct_0(esk2_0)
      | esk3_0 != k2_struct_0(esk2_0) )
    & ( k7_subset_1(u1_struct_0(esk2_0),k2_struct_0(esk2_0),esk3_0) != k1_xboole_0
      | k7_subset_1(u1_struct_0(esk2_0),k2_struct_0(esk2_0),esk3_0) = k1_xboole_0 )
    & ( esk3_0 = k2_struct_0(esk2_0)
      | k7_subset_1(u1_struct_0(esk2_0),k2_struct_0(esk2_0),esk3_0) = k1_xboole_0 ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_24])])])])).

fof(c_0_37,plain,(
    ! [X28] : ~ v1_xboole_0(k1_zfmisc_1(X28)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).

cnf(c_0_38,plain,
    ( X1 = k1_zfmisc_1(X2)
    | r2_hidden(esk1_2(X2,X1),X1)
    | r2_hidden(esk1_2(X2,X1),X3)
    | X3 != k1_zfmisc_1(X2) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26]),
    [final]).

cnf(c_0_39,plain,
    ( r1_tarski(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_20]),
    [final]).

cnf(c_0_40,plain,
    ( k7_subset_1(X2,X1,X3) = k4_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_41,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2))) ),
    inference(rw,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_42,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_43,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_44,plain,(
    ! [X10] : k5_xboole_0(X10,X10) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t92_xboole_1])).

cnf(c_0_45,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_46,plain,(
    ! [X4,X5] :
      ( ( r1_tarski(X4,X5)
        | X4 != X5 )
      & ( r1_tarski(X5,X4)
        | X4 != X5 )
      & ( ~ r1_tarski(X4,X5)
        | ~ r1_tarski(X5,X4)
        | X4 = X5 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_47,plain,
    ( m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_48,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_49,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35]),
    [final]).

cnf(c_0_50,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_36]),
    [final]).

cnf(c_0_51,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_37]),
    [final]).

cnf(c_0_52,plain,
    ( X2 = k1_zfmisc_1(X1)
    | ~ r2_hidden(esk1_2(X1,X2),X2)
    | ~ r1_tarski(esk1_2(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20]),
    [final]).

cnf(c_0_53,plain,
    ( X1 = k1_zfmisc_1(X2)
    | r2_hidden(esk1_2(X2,X1),k1_zfmisc_1(X2))
    | r2_hidden(esk1_2(X2,X1),X1) ),
    inference(er,[status(thm)],[c_0_38]),
    [final]).

cnf(c_0_54,plain,
    ( X1 = k1_zfmisc_1(X2)
    | r1_tarski(esk1_2(X2,X1),X2)
    | r1_tarski(esk1_2(X2,X1),X3)
    | X1 != k1_zfmisc_1(X3) ),
    inference(spm,[status(thm)],[c_0_39,c_0_26]),
    [final]).

cnf(c_0_55,plain,
    ( k7_subset_1(X2,X1,X3) = k5_xboole_0(X1,k1_setfam_1(k2_enumset1(X1,X1,X1,X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_41]),c_0_42]),
    [final]).

cnf(c_0_56,plain,
    ( k1_setfam_1(k2_enumset1(X1,X1,X1,X2)) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_29]),c_0_42]),
    [final]).

cnf(c_0_57,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_44]),
    [final]).

fof(c_0_58,plain,(
    ! [X29,X30] :
      ( ~ m1_subset_1(X30,k1_zfmisc_1(X29))
      | k3_subset_1(X29,k3_subset_1(X29,X30)) = X30 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).

cnf(c_0_59,plain,
    ( k3_subset_1(X2,X1) = k5_xboole_0(X2,k1_setfam_1(k2_enumset1(X2,X2,X2,X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_41]),c_0_42]),
    [final]).

cnf(c_0_60,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_61,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_47,c_0_48]),
    [final]).

fof(c_0_62,plain,(
    ! [X34] : k2_subset_1(X34) = k3_subset_1(X34,k1_subset_1(X34)) ),
    inference(variable_rename,[status(thm)],[t22_subset_1])).

fof(c_0_63,plain,(
    ! [X23] : k1_subset_1(X23) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[d3_subset_1])).

cnf(c_0_64,negated_conjecture,
    ( r2_hidden(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_51]),
    [final]).

cnf(c_0_65,plain,
    ( X1 = k1_zfmisc_1(X2)
    | r2_hidden(esk1_2(X2,X1),k1_zfmisc_1(X2))
    | ~ r1_tarski(esk1_2(X2,X1),X2) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53]),
    [final]).

cnf(c_0_66,plain,
    ( k1_zfmisc_1(X1) = k1_zfmisc_1(X2)
    | r1_tarski(esk1_2(X2,k1_zfmisc_1(X1)),X1)
    | r1_tarski(esk1_2(X2,k1_zfmisc_1(X1)),X2) ),
    inference(er,[status(thm)],[c_0_54]),
    [final]).

cnf(c_0_67,plain,
    ( k7_subset_1(X1,X2,X3) = k1_xboole_0
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_tarski(X2,X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_57]),
    [final]).

cnf(c_0_68,plain,
    ( k3_subset_1(X2,k3_subset_1(X2,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_58]),
    [final]).

cnf(c_0_69,plain,
    ( k3_subset_1(X1,X2) = k1_xboole_0
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_56]),c_0_57]),
    [final]).

cnf(c_0_70,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_60]),
    [final]).

cnf(c_0_71,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X1)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_61]),c_0_51]),
    [final]).

cnf(c_0_72,plain,
    ( k2_subset_1(X1) = k3_subset_1(X1,k1_subset_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_73,plain,
    ( k1_subset_1(X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_74,negated_conjecture,
    ( r1_tarski(esk3_0,X1)
    | k1_zfmisc_1(u1_struct_0(esk2_0)) != k1_zfmisc_1(X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_64]),
    [final]).

cnf(c_0_75,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46]),
    [final]).

cnf(c_0_76,plain,
    ( k1_zfmisc_1(X1) = k1_zfmisc_1(X2)
    | r2_hidden(esk1_2(X2,k1_zfmisc_1(X1)),k1_zfmisc_1(X2))
    | r1_tarski(esk1_2(X2,k1_zfmisc_1(X1)),X1) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66]),
    [final]).

cnf(c_0_77,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))) = k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_55,c_0_67])).

cnf(c_0_78,plain,
    ( k1_xboole_0 = X1
    | ~ m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X2,k3_subset_1(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69]),
    [final]).

cnf(c_0_79,negated_conjecture,
    ( esk3_0 = k2_struct_0(esk2_0)
    | k7_subset_1(u1_struct_0(esk2_0),k2_struct_0(esk2_0),esk3_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_36]),
    [final]).

cnf(c_0_80,plain,
    ( k7_subset_1(X1,X2,X3) = k7_subset_1(X4,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X4)) ),
    inference(spm,[status(thm)],[c_0_55,c_0_55]),
    [final]).

cnf(c_0_81,plain,
    ( r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_70]),
    [final]).

cnf(c_0_82,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk2_0),k2_struct_0(esk2_0),esk3_0) != k1_xboole_0
    | esk3_0 != k2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_36]),
    [final]).

cnf(c_0_83,plain,
    ( k7_subset_1(X1,X2,X3) = k3_subset_1(X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_55]),
    [final]).

cnf(c_0_84,plain,
    ( r1_tarski(X1,X2)
    | k1_zfmisc_1(X1) != k1_zfmisc_1(X2) ),
    inference(spm,[status(thm)],[c_0_39,c_0_71]),
    [final]).

cnf(c_0_85,plain,
    ( X1 = k3_subset_1(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_72,c_0_48]),c_0_73]),
    [final]).

cnf(c_0_86,negated_conjecture,
    ( r1_tarski(esk3_0,u1_struct_0(esk2_0)) ),
    inference(er,[status(thm)],[c_0_74]),
    [final]).

cnf(c_0_87,plain,
    ( esk1_2(X1,k1_zfmisc_1(X2)) = X2
    | k1_zfmisc_1(X2) = k1_zfmisc_1(X1)
    | r2_hidden(esk1_2(X1,k1_zfmisc_1(X2)),k1_zfmisc_1(X1))
    | ~ r1_tarski(X2,esk1_2(X1,k1_zfmisc_1(X2))) ),
    inference(spm,[status(thm)],[c_0_75,c_0_76]),
    [final]).

cnf(c_0_88,plain,
    ( k1_zfmisc_1(X1) = k1_zfmisc_1(X2)
    | r2_hidden(esk1_2(X2,k1_zfmisc_1(X1)),k1_zfmisc_1(X2))
    | r2_hidden(esk1_2(X2,k1_zfmisc_1(X1)),X3)
    | X3 != k1_zfmisc_1(X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_76]),
    [final]).

cnf(c_0_89,plain,
    ( k1_zfmisc_1(X1) = k1_zfmisc_1(X2)
    | r2_hidden(esk1_2(X2,k1_zfmisc_1(X1)),X3)
    | r1_tarski(esk1_2(X2,k1_zfmisc_1(X1)),X2)
    | X3 != k1_zfmisc_1(X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_66]),
    [final]).

cnf(c_0_90,plain,
    ( k1_zfmisc_1(X1) = k1_zfmisc_1(X2)
    | r1_tarski(esk1_2(X2,k1_zfmisc_1(X1)),X1)
    | r1_tarski(esk1_2(X2,k1_zfmisc_1(X1)),X3)
    | k1_zfmisc_1(X2) != k1_zfmisc_1(X3) ),
    inference(spm,[status(thm)],[c_0_39,c_0_76]),
    [final]).

cnf(c_0_91,plain,
    ( esk1_2(X1,k1_zfmisc_1(X2)) = X2
    | k1_zfmisc_1(X2) = k1_zfmisc_1(X1)
    | r1_tarski(esk1_2(X1,k1_zfmisc_1(X2)),X1)
    | ~ r1_tarski(X2,esk1_2(X1,k1_zfmisc_1(X2))) ),
    inference(spm,[status(thm)],[c_0_75,c_0_66]),
    [final]).

cnf(c_0_92,plain,
    ( esk1_2(X1,k1_zfmisc_1(X2)) = X1
    | k1_zfmisc_1(X2) = k1_zfmisc_1(X1)
    | r1_tarski(esk1_2(X1,k1_zfmisc_1(X2)),X2)
    | ~ r1_tarski(X1,esk1_2(X1,k1_zfmisc_1(X2))) ),
    inference(spm,[status(thm)],[c_0_75,c_0_66]),
    [final]).

cnf(c_0_93,plain,
    ( k1_zfmisc_1(X1) = k1_zfmisc_1(X2)
    | r2_hidden(esk1_2(X2,k1_zfmisc_1(X1)),X3)
    | r1_tarski(esk1_2(X2,k1_zfmisc_1(X1)),X1)
    | X3 != k1_zfmisc_1(X2) ),
    inference(spm,[status(thm)],[c_0_25,c_0_66]),
    [final]).

cnf(c_0_94,plain,
    ( X1 = k1_zfmisc_1(X2)
    | r2_hidden(esk1_2(X2,X1),k1_zfmisc_1(X2))
    | r1_tarski(esk1_2(X2,X1),X3)
    | X1 != k1_zfmisc_1(X3) ),
    inference(spm,[status(thm)],[c_0_39,c_0_53]),
    [final]).

cnf(c_0_95,plain,
    ( X1 = k1_zfmisc_1(X2)
    | r2_hidden(esk1_2(X2,X1),X1)
    | r1_tarski(esk1_2(X2,X1),X3)
    | k1_zfmisc_1(X2) != k1_zfmisc_1(X3) ),
    inference(spm,[status(thm)],[c_0_39,c_0_53]),
    [final]).

cnf(c_0_96,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_77,c_0_61]),
    [final]).

cnf(c_0_97,plain,
    ( k1_xboole_0 = X1
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X2,k1_xboole_0)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_78,c_0_69]),
    [final]).

cnf(c_0_98,negated_conjecture,
    ( k7_subset_1(X1,k2_struct_0(esk2_0),esk3_0) = k1_xboole_0
    | k2_struct_0(esk2_0) = esk3_0
    | ~ m1_subset_1(k2_struct_0(esk2_0),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ m1_subset_1(k2_struct_0(esk2_0),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_79,c_0_80]),
    [final]).

cnf(c_0_99,plain,
    ( X1 = k1_zfmisc_1(X2)
    | k1_zfmisc_1(esk1_2(X2,X1)) != X1
    | ~ r1_tarski(esk1_2(X2,X1),X2) ),
    inference(spm,[status(thm)],[c_0_52,c_0_81]),
    [final]).

cnf(c_0_100,negated_conjecture,
    ( k7_subset_1(X1,k2_struct_0(esk2_0),esk3_0) != k1_xboole_0
    | k2_struct_0(esk2_0) != esk3_0
    | ~ m1_subset_1(k2_struct_0(esk2_0),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ m1_subset_1(k2_struct_0(esk2_0),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_82,c_0_80]),
    [final]).

cnf(c_0_101,negated_conjecture,
    ( k3_subset_1(k2_struct_0(esk2_0),esk3_0) = k1_xboole_0
    | k2_struct_0(esk2_0) = esk3_0
    | ~ m1_subset_1(k2_struct_0(esk2_0),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k2_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_79,c_0_83]),
    [final]).

cnf(c_0_102,negated_conjecture,
    ( k3_subset_1(k2_struct_0(esk2_0),esk3_0) != k1_xboole_0
    | k2_struct_0(esk2_0) != esk3_0
    | ~ m1_subset_1(k2_struct_0(esk2_0),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k2_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_82,c_0_83]),
    [final]).

cnf(c_0_103,plain,
    ( r2_hidden(X1,X2)
    | k1_zfmisc_1(X1) != k1_zfmisc_1(X3)
    | X2 != k1_zfmisc_1(X3) ),
    inference(spm,[status(thm)],[c_0_25,c_0_84]),
    [final]).

cnf(c_0_104,plain,
    ( X1 = X2
    | k1_zfmisc_1(X2) != k1_zfmisc_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_84]),c_0_84]),
    [final]).

cnf(c_0_105,plain,
    ( X1 = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_85]),
    [final]).

cnf(c_0_106,negated_conjecture,
    ( r2_hidden(esk3_0,X1)
    | X1 != k1_zfmisc_1(u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_86]),
    [final]).

cnf(c_0_107,plain,
    ( r1_tarski(X1,X2)
    | X3 != k1_zfmisc_1(X2)
    | X3 != k1_zfmisc_1(X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_81]),
    [final]).

cnf(c_0_108,plain,
    ( esk1_2(X1,X2) = X1
    | X2 = k1_zfmisc_1(X1)
    | r2_hidden(esk1_2(X1,X2),X2)
    | ~ r1_tarski(X1,esk1_2(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_75,c_0_26]),
    [final]).

cnf(c_0_109,negated_conjecture,
    ( u1_struct_0(esk2_0) = esk3_0
    | ~ r1_tarski(u1_struct_0(esk2_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_75,c_0_86]),
    [final]).

cnf(c_0_110,negated_conjecture,
    ( k2_struct_0(esk2_0) != esk3_0
    | ~ m1_subset_1(k2_struct_0(esk2_0),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ r1_tarski(k2_struct_0(esk2_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_82,c_0_67]),
    [final]).

cnf(c_0_111,plain,
    ( k3_subset_1(X1,X1) = k1_xboole_0
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_68,c_0_85]),
    [final]).

cnf(c_0_112,negated_conjecture,
    ( l1_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_36]),
    [final]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:55:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.38  # AutoSched0-Mode selected heuristic G_E___302_C18_F1_URBAN_RG_S04BN
% 0.20/0.38  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.20/0.38  #
% 0.20/0.38  # Preprocessing time       : 0.027 s
% 0.20/0.38  
% 0.20/0.38  # No proof found!
% 0.20/0.38  # SZS status CounterSatisfiable
% 0.20/0.38  # SZS output start Saturation
% 0.20/0.38  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.20/0.38  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.20/0.38  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 0.20/0.38  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.20/0.38  fof(t23_pre_topc, conjecture, ![X1]:(l1_struct_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(~((X2!=k2_struct_0(X1)&k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2)=k1_xboole_0))&~((k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2)!=k1_xboole_0&X2=k2_struct_0(X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_pre_topc)).
% 0.20/0.38  fof(redefinition_k7_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k7_subset_1(X1,X2,X3)=k4_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 0.20/0.38  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.20/0.38  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.20/0.38  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 0.20/0.38  fof(dt_k2_subset_1, axiom, ![X1]:m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 0.20/0.38  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 0.20/0.38  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 0.20/0.38  fof(fc1_subset_1, axiom, ![X1]:~(v1_xboole_0(k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 0.20/0.38  fof(t92_xboole_1, axiom, ![X1]:k5_xboole_0(X1,X1)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 0.20/0.38  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.20/0.38  fof(involutiveness_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,k3_subset_1(X1,X2))=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 0.20/0.38  fof(t22_subset_1, axiom, ![X1]:k2_subset_1(X1)=k3_subset_1(X1,k1_subset_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_subset_1)).
% 0.20/0.38  fof(d3_subset_1, axiom, ![X1]:k1_subset_1(X1)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_subset_1)).
% 0.20/0.38  fof(c_0_18, plain, ![X35, X36]:k1_setfam_1(k2_tarski(X35,X36))=k3_xboole_0(X35,X36), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.20/0.38  fof(c_0_19, plain, ![X11, X12]:k1_enumset1(X11,X11,X12)=k2_tarski(X11,X12), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.20/0.38  fof(c_0_20, plain, ![X16, X17, X18, X19, X20, X21]:(((~r2_hidden(X18,X17)|r1_tarski(X18,X16)|X17!=k1_zfmisc_1(X16))&(~r1_tarski(X19,X16)|r2_hidden(X19,X17)|X17!=k1_zfmisc_1(X16)))&((~r2_hidden(esk1_2(X20,X21),X21)|~r1_tarski(esk1_2(X20,X21),X20)|X21=k1_zfmisc_1(X20))&(r2_hidden(esk1_2(X20,X21),X21)|r1_tarski(esk1_2(X20,X21),X20)|X21=k1_zfmisc_1(X20)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 0.20/0.38  fof(c_0_21, plain, ![X6, X7]:k4_xboole_0(X6,X7)=k5_xboole_0(X6,k3_xboole_0(X6,X7)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.20/0.38  cnf(c_0_22, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.38  cnf(c_0_23, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.38  fof(c_0_24, negated_conjecture, ~(![X1]:(l1_struct_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(~((X2!=k2_struct_0(X1)&k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2)=k1_xboole_0))&~((k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2)!=k1_xboole_0&X2=k2_struct_0(X1))))))), inference(assume_negation,[status(cth)],[t23_pre_topc])).
% 0.20/0.38  cnf(c_0_25, plain, (r2_hidden(X1,X3)|~r1_tarski(X1,X2)|X3!=k1_zfmisc_1(X2)), inference(split_conjunct,[status(thm)],[c_0_20]), ['final']).
% 0.20/0.38  cnf(c_0_26, plain, (r2_hidden(esk1_2(X1,X2),X2)|r1_tarski(esk1_2(X1,X2),X1)|X2=k1_zfmisc_1(X1)), inference(split_conjunct,[status(thm)],[c_0_20]), ['final']).
% 0.20/0.38  fof(c_0_27, plain, ![X31, X32, X33]:(~m1_subset_1(X32,k1_zfmisc_1(X31))|k7_subset_1(X31,X32,X33)=k4_xboole_0(X32,X33)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).
% 0.20/0.38  cnf(c_0_28, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.38  cnf(c_0_29, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_22, c_0_23])).
% 0.20/0.38  fof(c_0_30, plain, ![X13, X14, X15]:k2_enumset1(X13,X13,X14,X15)=k1_enumset1(X13,X14,X15), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.20/0.38  fof(c_0_31, plain, ![X8, X9]:(~r1_tarski(X8,X9)|k3_xboole_0(X8,X9)=X8), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.20/0.38  fof(c_0_32, plain, ![X25, X26]:(~m1_subset_1(X26,k1_zfmisc_1(X25))|k3_subset_1(X25,X26)=k4_xboole_0(X25,X26)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 0.20/0.38  fof(c_0_33, plain, ![X27]:m1_subset_1(k2_subset_1(X27),k1_zfmisc_1(X27)), inference(variable_rename,[status(thm)],[dt_k2_subset_1])).
% 0.20/0.38  fof(c_0_34, plain, ![X24]:k2_subset_1(X24)=X24, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 0.20/0.38  fof(c_0_35, plain, ![X37, X38]:(~m1_subset_1(X37,X38)|(v1_xboole_0(X38)|r2_hidden(X37,X38))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.20/0.38  fof(c_0_36, negated_conjecture, (l1_struct_0(esk2_0)&(m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))&(((k7_subset_1(u1_struct_0(esk2_0),k2_struct_0(esk2_0),esk3_0)!=k1_xboole_0|esk3_0!=k2_struct_0(esk2_0))&(esk3_0=k2_struct_0(esk2_0)|esk3_0!=k2_struct_0(esk2_0)))&((k7_subset_1(u1_struct_0(esk2_0),k2_struct_0(esk2_0),esk3_0)!=k1_xboole_0|k7_subset_1(u1_struct_0(esk2_0),k2_struct_0(esk2_0),esk3_0)=k1_xboole_0)&(esk3_0=k2_struct_0(esk2_0)|k7_subset_1(u1_struct_0(esk2_0),k2_struct_0(esk2_0),esk3_0)=k1_xboole_0))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_24])])])])).
% 0.20/0.38  fof(c_0_37, plain, ![X28]:~v1_xboole_0(k1_zfmisc_1(X28)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).
% 0.20/0.38  cnf(c_0_38, plain, (X1=k1_zfmisc_1(X2)|r2_hidden(esk1_2(X2,X1),X1)|r2_hidden(esk1_2(X2,X1),X3)|X3!=k1_zfmisc_1(X2)), inference(spm,[status(thm)],[c_0_25, c_0_26]), ['final']).
% 0.20/0.38  cnf(c_0_39, plain, (r1_tarski(X1,X3)|~r2_hidden(X1,X2)|X2!=k1_zfmisc_1(X3)), inference(split_conjunct,[status(thm)],[c_0_20]), ['final']).
% 0.20/0.38  cnf(c_0_40, plain, (k7_subset_1(X2,X1,X3)=k4_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.38  cnf(c_0_41, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2)))), inference(rw,[status(thm)],[c_0_28, c_0_29])).
% 0.20/0.38  cnf(c_0_42, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.38  cnf(c_0_43, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.20/0.38  fof(c_0_44, plain, ![X10]:k5_xboole_0(X10,X10)=k1_xboole_0, inference(variable_rename,[status(thm)],[t92_xboole_1])).
% 0.20/0.38  cnf(c_0_45, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.38  fof(c_0_46, plain, ![X4, X5]:(((r1_tarski(X4,X5)|X4!=X5)&(r1_tarski(X5,X4)|X4!=X5))&(~r1_tarski(X4,X5)|~r1_tarski(X5,X4)|X4=X5)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.20/0.38  cnf(c_0_47, plain, (m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.20/0.38  cnf(c_0_48, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.20/0.38  cnf(c_0_49, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_35]), ['final']).
% 0.20/0.38  cnf(c_0_50, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_36]), ['final']).
% 0.20/0.38  cnf(c_0_51, plain, (~v1_xboole_0(k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_37]), ['final']).
% 0.20/0.38  cnf(c_0_52, plain, (X2=k1_zfmisc_1(X1)|~r2_hidden(esk1_2(X1,X2),X2)|~r1_tarski(esk1_2(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_20]), ['final']).
% 0.20/0.38  cnf(c_0_53, plain, (X1=k1_zfmisc_1(X2)|r2_hidden(esk1_2(X2,X1),k1_zfmisc_1(X2))|r2_hidden(esk1_2(X2,X1),X1)), inference(er,[status(thm)],[c_0_38]), ['final']).
% 0.20/0.38  cnf(c_0_54, plain, (X1=k1_zfmisc_1(X2)|r1_tarski(esk1_2(X2,X1),X2)|r1_tarski(esk1_2(X2,X1),X3)|X1!=k1_zfmisc_1(X3)), inference(spm,[status(thm)],[c_0_39, c_0_26]), ['final']).
% 0.20/0.38  cnf(c_0_55, plain, (k7_subset_1(X2,X1,X3)=k5_xboole_0(X1,k1_setfam_1(k2_enumset1(X1,X1,X1,X3)))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_41]), c_0_42]), ['final']).
% 0.20/0.38  cnf(c_0_56, plain, (k1_setfam_1(k2_enumset1(X1,X1,X1,X2))=X1|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43, c_0_29]), c_0_42]), ['final']).
% 0.20/0.38  cnf(c_0_57, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_44]), ['final']).
% 0.20/0.38  fof(c_0_58, plain, ![X29, X30]:(~m1_subset_1(X30,k1_zfmisc_1(X29))|k3_subset_1(X29,k3_subset_1(X29,X30))=X30), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).
% 0.20/0.38  cnf(c_0_59, plain, (k3_subset_1(X2,X1)=k5_xboole_0(X2,k1_setfam_1(k2_enumset1(X2,X2,X2,X1)))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45, c_0_41]), c_0_42]), ['final']).
% 0.20/0.38  cnf(c_0_60, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.20/0.38  cnf(c_0_61, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_47, c_0_48]), ['final']).
% 0.20/0.38  fof(c_0_62, plain, ![X34]:k2_subset_1(X34)=k3_subset_1(X34,k1_subset_1(X34)), inference(variable_rename,[status(thm)],[t22_subset_1])).
% 0.20/0.38  fof(c_0_63, plain, ![X23]:k1_subset_1(X23)=k1_xboole_0, inference(variable_rename,[status(thm)],[d3_subset_1])).
% 0.20/0.38  cnf(c_0_64, negated_conjecture, (r2_hidden(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_51]), ['final']).
% 0.20/0.38  cnf(c_0_65, plain, (X1=k1_zfmisc_1(X2)|r2_hidden(esk1_2(X2,X1),k1_zfmisc_1(X2))|~r1_tarski(esk1_2(X2,X1),X2)), inference(spm,[status(thm)],[c_0_52, c_0_53]), ['final']).
% 0.20/0.38  cnf(c_0_66, plain, (k1_zfmisc_1(X1)=k1_zfmisc_1(X2)|r1_tarski(esk1_2(X2,k1_zfmisc_1(X1)),X1)|r1_tarski(esk1_2(X2,k1_zfmisc_1(X1)),X2)), inference(er,[status(thm)],[c_0_54]), ['final']).
% 0.20/0.38  cnf(c_0_67, plain, (k7_subset_1(X1,X2,X3)=k1_xboole_0|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_tarski(X2,X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_57]), ['final']).
% 0.20/0.38  cnf(c_0_68, plain, (k3_subset_1(X2,k3_subset_1(X2,X1))=X1|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_58]), ['final']).
% 0.20/0.38  cnf(c_0_69, plain, (k3_subset_1(X1,X2)=k1_xboole_0|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_56]), c_0_57]), ['final']).
% 0.20/0.38  cnf(c_0_70, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_60]), ['final']).
% 0.20/0.38  cnf(c_0_71, plain, (r2_hidden(X1,k1_zfmisc_1(X1))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_61]), c_0_51]), ['final']).
% 0.20/0.38  cnf(c_0_72, plain, (k2_subset_1(X1)=k3_subset_1(X1,k1_subset_1(X1))), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.20/0.38  cnf(c_0_73, plain, (k1_subset_1(X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.20/0.38  cnf(c_0_74, negated_conjecture, (r1_tarski(esk3_0,X1)|k1_zfmisc_1(u1_struct_0(esk2_0))!=k1_zfmisc_1(X1)), inference(spm,[status(thm)],[c_0_39, c_0_64]), ['final']).
% 0.20/0.38  cnf(c_0_75, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_46]), ['final']).
% 0.20/0.38  cnf(c_0_76, plain, (k1_zfmisc_1(X1)=k1_zfmisc_1(X2)|r2_hidden(esk1_2(X2,k1_zfmisc_1(X1)),k1_zfmisc_1(X2))|r1_tarski(esk1_2(X2,k1_zfmisc_1(X1)),X1)), inference(spm,[status(thm)],[c_0_65, c_0_66]), ['final']).
% 0.20/0.38  cnf(c_0_77, plain, (k5_xboole_0(X1,k1_setfam_1(k2_enumset1(X1,X1,X1,X2)))=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(X3))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_55, c_0_67])).
% 0.20/0.38  cnf(c_0_78, plain, (k1_xboole_0=X1|~m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X2,k3_subset_1(X2,X1))), inference(spm,[status(thm)],[c_0_68, c_0_69]), ['final']).
% 0.20/0.38  cnf(c_0_79, negated_conjecture, (esk3_0=k2_struct_0(esk2_0)|k7_subset_1(u1_struct_0(esk2_0),k2_struct_0(esk2_0),esk3_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_36]), ['final']).
% 0.20/0.38  cnf(c_0_80, plain, (k7_subset_1(X1,X2,X3)=k7_subset_1(X4,X2,X3)|~m1_subset_1(X2,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X4))), inference(spm,[status(thm)],[c_0_55, c_0_55]), ['final']).
% 0.20/0.38  cnf(c_0_81, plain, (r2_hidden(X1,X2)|X2!=k1_zfmisc_1(X1)), inference(spm,[status(thm)],[c_0_25, c_0_70]), ['final']).
% 0.20/0.38  cnf(c_0_82, negated_conjecture, (k7_subset_1(u1_struct_0(esk2_0),k2_struct_0(esk2_0),esk3_0)!=k1_xboole_0|esk3_0!=k2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_36]), ['final']).
% 0.20/0.38  cnf(c_0_83, plain, (k7_subset_1(X1,X2,X3)=k3_subset_1(X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(X2))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_59, c_0_55]), ['final']).
% 0.20/0.38  cnf(c_0_84, plain, (r1_tarski(X1,X2)|k1_zfmisc_1(X1)!=k1_zfmisc_1(X2)), inference(spm,[status(thm)],[c_0_39, c_0_71]), ['final']).
% 0.20/0.38  cnf(c_0_85, plain, (X1=k3_subset_1(X1,k1_xboole_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_72, c_0_48]), c_0_73]), ['final']).
% 0.20/0.38  cnf(c_0_86, negated_conjecture, (r1_tarski(esk3_0,u1_struct_0(esk2_0))), inference(er,[status(thm)],[c_0_74]), ['final']).
% 0.20/0.38  cnf(c_0_87, plain, (esk1_2(X1,k1_zfmisc_1(X2))=X2|k1_zfmisc_1(X2)=k1_zfmisc_1(X1)|r2_hidden(esk1_2(X1,k1_zfmisc_1(X2)),k1_zfmisc_1(X1))|~r1_tarski(X2,esk1_2(X1,k1_zfmisc_1(X2)))), inference(spm,[status(thm)],[c_0_75, c_0_76]), ['final']).
% 0.20/0.38  cnf(c_0_88, plain, (k1_zfmisc_1(X1)=k1_zfmisc_1(X2)|r2_hidden(esk1_2(X2,k1_zfmisc_1(X1)),k1_zfmisc_1(X2))|r2_hidden(esk1_2(X2,k1_zfmisc_1(X1)),X3)|X3!=k1_zfmisc_1(X1)), inference(spm,[status(thm)],[c_0_25, c_0_76]), ['final']).
% 0.20/0.38  cnf(c_0_89, plain, (k1_zfmisc_1(X1)=k1_zfmisc_1(X2)|r2_hidden(esk1_2(X2,k1_zfmisc_1(X1)),X3)|r1_tarski(esk1_2(X2,k1_zfmisc_1(X1)),X2)|X3!=k1_zfmisc_1(X1)), inference(spm,[status(thm)],[c_0_25, c_0_66]), ['final']).
% 0.20/0.38  cnf(c_0_90, plain, (k1_zfmisc_1(X1)=k1_zfmisc_1(X2)|r1_tarski(esk1_2(X2,k1_zfmisc_1(X1)),X1)|r1_tarski(esk1_2(X2,k1_zfmisc_1(X1)),X3)|k1_zfmisc_1(X2)!=k1_zfmisc_1(X3)), inference(spm,[status(thm)],[c_0_39, c_0_76]), ['final']).
% 0.20/0.38  cnf(c_0_91, plain, (esk1_2(X1,k1_zfmisc_1(X2))=X2|k1_zfmisc_1(X2)=k1_zfmisc_1(X1)|r1_tarski(esk1_2(X1,k1_zfmisc_1(X2)),X1)|~r1_tarski(X2,esk1_2(X1,k1_zfmisc_1(X2)))), inference(spm,[status(thm)],[c_0_75, c_0_66]), ['final']).
% 0.20/0.38  cnf(c_0_92, plain, (esk1_2(X1,k1_zfmisc_1(X2))=X1|k1_zfmisc_1(X2)=k1_zfmisc_1(X1)|r1_tarski(esk1_2(X1,k1_zfmisc_1(X2)),X2)|~r1_tarski(X1,esk1_2(X1,k1_zfmisc_1(X2)))), inference(spm,[status(thm)],[c_0_75, c_0_66]), ['final']).
% 0.20/0.38  cnf(c_0_93, plain, (k1_zfmisc_1(X1)=k1_zfmisc_1(X2)|r2_hidden(esk1_2(X2,k1_zfmisc_1(X1)),X3)|r1_tarski(esk1_2(X2,k1_zfmisc_1(X1)),X1)|X3!=k1_zfmisc_1(X2)), inference(spm,[status(thm)],[c_0_25, c_0_66]), ['final']).
% 0.20/0.38  cnf(c_0_94, plain, (X1=k1_zfmisc_1(X2)|r2_hidden(esk1_2(X2,X1),k1_zfmisc_1(X2))|r1_tarski(esk1_2(X2,X1),X3)|X1!=k1_zfmisc_1(X3)), inference(spm,[status(thm)],[c_0_39, c_0_53]), ['final']).
% 0.20/0.38  cnf(c_0_95, plain, (X1=k1_zfmisc_1(X2)|r2_hidden(esk1_2(X2,X1),X1)|r1_tarski(esk1_2(X2,X1),X3)|k1_zfmisc_1(X2)!=k1_zfmisc_1(X3)), inference(spm,[status(thm)],[c_0_39, c_0_53]), ['final']).
% 0.20/0.38  cnf(c_0_96, plain, (k5_xboole_0(X1,k1_setfam_1(k2_enumset1(X1,X1,X1,X2)))=k1_xboole_0|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_77, c_0_61]), ['final']).
% 0.20/0.38  cnf(c_0_97, plain, (k1_xboole_0=X1|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X2,k1_xboole_0)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_78, c_0_69]), ['final']).
% 0.20/0.38  cnf(c_0_98, negated_conjecture, (k7_subset_1(X1,k2_struct_0(esk2_0),esk3_0)=k1_xboole_0|k2_struct_0(esk2_0)=esk3_0|~m1_subset_1(k2_struct_0(esk2_0),k1_zfmisc_1(u1_struct_0(esk2_0)))|~m1_subset_1(k2_struct_0(esk2_0),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_79, c_0_80]), ['final']).
% 0.20/0.38  cnf(c_0_99, plain, (X1=k1_zfmisc_1(X2)|k1_zfmisc_1(esk1_2(X2,X1))!=X1|~r1_tarski(esk1_2(X2,X1),X2)), inference(spm,[status(thm)],[c_0_52, c_0_81]), ['final']).
% 0.20/0.38  cnf(c_0_100, negated_conjecture, (k7_subset_1(X1,k2_struct_0(esk2_0),esk3_0)!=k1_xboole_0|k2_struct_0(esk2_0)!=esk3_0|~m1_subset_1(k2_struct_0(esk2_0),k1_zfmisc_1(u1_struct_0(esk2_0)))|~m1_subset_1(k2_struct_0(esk2_0),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_82, c_0_80]), ['final']).
% 0.20/0.38  cnf(c_0_101, negated_conjecture, (k3_subset_1(k2_struct_0(esk2_0),esk3_0)=k1_xboole_0|k2_struct_0(esk2_0)=esk3_0|~m1_subset_1(k2_struct_0(esk2_0),k1_zfmisc_1(u1_struct_0(esk2_0)))|~m1_subset_1(esk3_0,k1_zfmisc_1(k2_struct_0(esk2_0)))), inference(spm,[status(thm)],[c_0_79, c_0_83]), ['final']).
% 0.20/0.38  cnf(c_0_102, negated_conjecture, (k3_subset_1(k2_struct_0(esk2_0),esk3_0)!=k1_xboole_0|k2_struct_0(esk2_0)!=esk3_0|~m1_subset_1(k2_struct_0(esk2_0),k1_zfmisc_1(u1_struct_0(esk2_0)))|~m1_subset_1(esk3_0,k1_zfmisc_1(k2_struct_0(esk2_0)))), inference(spm,[status(thm)],[c_0_82, c_0_83]), ['final']).
% 0.20/0.38  cnf(c_0_103, plain, (r2_hidden(X1,X2)|k1_zfmisc_1(X1)!=k1_zfmisc_1(X3)|X2!=k1_zfmisc_1(X3)), inference(spm,[status(thm)],[c_0_25, c_0_84]), ['final']).
% 0.20/0.38  cnf(c_0_104, plain, (X1=X2|k1_zfmisc_1(X2)!=k1_zfmisc_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_84]), c_0_84]), ['final']).
% 0.20/0.38  cnf(c_0_105, plain, (X1=X2|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_85]), ['final']).
% 0.20/0.38  cnf(c_0_106, negated_conjecture, (r2_hidden(esk3_0,X1)|X1!=k1_zfmisc_1(u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_25, c_0_86]), ['final']).
% 0.20/0.38  cnf(c_0_107, plain, (r1_tarski(X1,X2)|X3!=k1_zfmisc_1(X2)|X3!=k1_zfmisc_1(X1)), inference(spm,[status(thm)],[c_0_39, c_0_81]), ['final']).
% 0.20/0.38  cnf(c_0_108, plain, (esk1_2(X1,X2)=X1|X2=k1_zfmisc_1(X1)|r2_hidden(esk1_2(X1,X2),X2)|~r1_tarski(X1,esk1_2(X1,X2))), inference(spm,[status(thm)],[c_0_75, c_0_26]), ['final']).
% 0.20/0.38  cnf(c_0_109, negated_conjecture, (u1_struct_0(esk2_0)=esk3_0|~r1_tarski(u1_struct_0(esk2_0),esk3_0)), inference(spm,[status(thm)],[c_0_75, c_0_86]), ['final']).
% 0.20/0.38  cnf(c_0_110, negated_conjecture, (k2_struct_0(esk2_0)!=esk3_0|~m1_subset_1(k2_struct_0(esk2_0),k1_zfmisc_1(u1_struct_0(esk2_0)))|~r1_tarski(k2_struct_0(esk2_0),esk3_0)), inference(spm,[status(thm)],[c_0_82, c_0_67]), ['final']).
% 0.20/0.38  cnf(c_0_111, plain, (k3_subset_1(X1,X1)=k1_xboole_0|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_68, c_0_85]), ['final']).
% 0.20/0.38  cnf(c_0_112, negated_conjecture, (l1_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_36]), ['final']).
% 0.20/0.38  # SZS output end Saturation
% 0.20/0.38  # Proof object total steps             : 113
% 0.20/0.38  # Proof object clause steps            : 76
% 0.20/0.38  # Proof object formula steps           : 37
% 0.20/0.38  # Proof object conjectures             : 17
% 0.20/0.38  # Proof object clause conjectures      : 14
% 0.20/0.38  # Proof object formula conjectures     : 3
% 0.20/0.38  # Proof object initial clauses used    : 25
% 0.20/0.38  # Proof object initial formulas used   : 18
% 0.20/0.38  # Proof object generating inferences   : 43
% 0.20/0.38  # Proof object simplifying inferences  : 18
% 0.20/0.38  # Parsed axioms                        : 18
% 0.20/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.38  # Initial clauses                      : 28
% 0.20/0.38  # Removed in clause preprocessing      : 8
% 0.20/0.38  # Initial clauses in saturation        : 20
% 0.20/0.38  # Processed clauses                    : 107
% 0.20/0.38  # ...of these trivial                  : 2
% 0.20/0.38  # ...subsumed                          : 38
% 0.20/0.38  # ...remaining for further processing  : 67
% 0.20/0.38  # Other redundant clauses eliminated   : 2
% 0.20/0.38  # Clauses deleted for lack of memory   : 0
% 0.20/0.38  # Backward-subsumed                    : 4
% 0.20/0.38  # Backward-rewritten                   : 0
% 0.20/0.38  # Generated clauses                    : 107
% 0.20/0.38  # ...of the previous two non-trivial   : 87
% 0.20/0.38  # Contextual simplify-reflections      : 1
% 0.20/0.38  # Paramodulations                      : 80
% 0.20/0.38  # Factorizations                       : 12
% 0.20/0.38  # Equation resolutions                 : 15
% 0.20/0.38  # Propositional unsat checks           : 0
% 0.20/0.38  #    Propositional check models        : 0
% 0.20/0.38  #    Propositional check unsatisfiable : 0
% 0.20/0.38  #    Propositional clauses             : 0
% 0.20/0.38  #    Propositional clauses after purity: 0
% 0.20/0.38  #    Propositional unsat core size     : 0
% 0.20/0.38  #    Propositional preprocessing time  : 0.000
% 0.20/0.38  #    Propositional encoding time       : 0.000
% 0.20/0.38  #    Propositional solver time         : 0.000
% 0.20/0.38  #    Success case prop preproc time    : 0.000
% 0.20/0.38  #    Success case prop encoding time   : 0.000
% 0.20/0.38  #    Success case prop solver time     : 0.000
% 0.20/0.38  # Current number of processed clauses  : 61
% 0.20/0.38  #    Positive orientable unit clauses  : 9
% 0.20/0.38  #    Positive unorientable unit clauses: 0
% 0.20/0.38  #    Negative unit clauses             : 1
% 0.20/0.38  #    Non-unit-clauses                  : 51
% 0.20/0.38  # Current number of unprocessed clauses: 0
% 0.20/0.38  # ...number of literals in the above   : 0
% 0.20/0.38  # Current number of archived formulas  : 0
% 0.20/0.38  # Current number of archived clauses   : 10
% 0.20/0.38  # Clause-clause subsumption calls (NU) : 608
% 0.20/0.38  # Rec. Clause-clause subsumption calls : 409
% 0.20/0.38  # Non-unit clause-clause subsumptions  : 43
% 0.20/0.38  # Unit Clause-clause subsumption calls : 3
% 0.20/0.38  # Rewrite failures with RHS unbound    : 0
% 0.20/0.38  # BW rewrite match attempts            : 6
% 0.20/0.38  # BW rewrite match successes           : 0
% 0.20/0.38  # Condensation attempts                : 0
% 0.20/0.38  # Condensation successes               : 0
% 0.20/0.38  # Termbank termtop insertions          : 3003
% 0.20/0.38  
% 0.20/0.38  # -------------------------------------------------
% 0.20/0.38  # User time                : 0.034 s
% 0.20/0.38  # System time              : 0.003 s
% 0.20/0.38  # Total time               : 0.037 s
% 0.20/0.38  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
