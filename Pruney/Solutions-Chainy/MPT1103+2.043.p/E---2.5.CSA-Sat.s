%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:08:41 EST 2020

% Result     : CounterSatisfiable 0.12s
% Output     : Saturation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 981 expanded)
%              Number of clauses        :   70 ( 470 expanded)
%              Number of leaves         :   13 ( 247 expanded)
%              Depth                    :   10
%              Number of atoms          :  266 (2218 expanded)
%              Number of equality atoms :   79 ( 939 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   10 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t69_xboole_1,axiom,(
    ! [X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ~ ( r1_tarski(X2,X1)
          & r1_xboole_0(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

fof(t65_xboole_1,axiom,(
    ! [X1] : r1_xboole_0(X1,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(redefinition_k7_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k7_subset_1(X1,X2,X3) = k4_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(t5_boole,axiom,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

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

fof(c_0_13,plain,(
    ! [X16,X17] : k4_xboole_0(X16,X17) = k5_xboole_0(X16,k3_xboole_0(X16,X17)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_14,plain,(
    ! [X26,X27] : k1_setfam_1(k2_tarski(X26,X27)) = k3_xboole_0(X26,X27) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_15,plain,(
    ! [X4,X5,X6] :
      ( ( ~ v1_xboole_0(X4)
        | ~ r2_hidden(X5,X4) )
      & ( r2_hidden(esk1_1(X6),X6)
        | v1_xboole_0(X6) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_16,plain,(
    ! [X8,X9,X10,X11,X12] :
      ( ( ~ r1_tarski(X8,X9)
        | ~ r2_hidden(X10,X8)
        | r2_hidden(X10,X9) )
      & ( r2_hidden(esk2_2(X11,X12),X11)
        | r1_tarski(X11,X12) )
      & ( ~ r2_hidden(esk2_2(X11,X12),X12)
        | r1_tarski(X11,X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_17,plain,(
    ! [X21,X22] :
      ( v1_xboole_0(X22)
      | ~ r1_tarski(X22,X21)
      | ~ r1_xboole_0(X22,X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t69_xboole_1])])])).

fof(c_0_18,plain,(
    ! [X20] : r1_xboole_0(X20,k1_xboole_0) ),
    inference(variable_rename,[status(thm)],[t65_xboole_1])).

fof(c_0_19,plain,(
    ! [X23,X24,X25] :
      ( ~ m1_subset_1(X24,k1_zfmisc_1(X23))
      | k7_subset_1(X23,X24,X25) = k4_xboole_0(X24,X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).

cnf(c_0_20,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15]),
    [final]).

cnf(c_0_23,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16]),
    [final]).

cnf(c_0_24,plain,
    ( v1_xboole_0(X1)
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17]),
    [final]).

cnf(c_0_25,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18]),
    [final]).

fof(c_0_26,plain,(
    ! [X14,X15] :
      ( ( r1_tarski(X14,X15)
        | X14 != X15 )
      & ( r1_tarski(X15,X14)
        | X14 != X15 )
      & ( ~ r1_tarski(X14,X15)
        | ~ r1_tarski(X15,X14)
        | X14 = X15 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_27,plain,
    ( k7_subset_1(X2,X1,X3) = k4_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_28,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_20,c_0_21])).

fof(c_0_29,plain,(
    ! [X28,X29] :
      ( ( ~ m1_subset_1(X28,k1_zfmisc_1(X29))
        | r1_tarski(X28,X29) )
      & ( ~ r1_tarski(X28,X29)
        | m1_subset_1(X28,k1_zfmisc_1(X29)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_30,plain,(
    ! [X18] : k3_xboole_0(X18,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

cnf(c_0_31,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23]),
    [final]).

cnf(c_0_32,plain,
    ( v1_xboole_0(X1)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25]),
    [final]).

cnf(c_0_33,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_34,plain,
    ( k7_subset_1(X2,X1,X3) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_27,c_0_28]),
    [final]).

cnf(c_0_35,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29]),
    [final]).

cnf(c_0_36,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_37,plain,(
    ! [X19] : k5_xboole_0(X19,k1_xboole_0) = X19 ),
    inference(variable_rename,[status(thm)],[t5_boole])).

fof(c_0_38,negated_conjecture,(
    ~ ! [X1] :
        ( l1_struct_0(X1)
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( ~ ( X2 != k2_struct_0(X1)
                  & k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2) = k1_xboole_0 )
              & ~ ( k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2) != k1_xboole_0
                  & X2 = k2_struct_0(X1) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t23_pre_topc])).

cnf(c_0_39,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32]),
    [final]).

cnf(c_0_40,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_33]),
    [final]).

fof(c_0_41,plain,(
    ! [X30,X31] :
      ( ~ l1_struct_0(X30)
      | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))
      | k7_subset_1(u1_struct_0(X30),k2_struct_0(X30),k7_subset_1(u1_struct_0(X30),k2_struct_0(X30),X31)) = X31 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t22_pre_topc])])])).

cnf(c_0_42,plain,
    ( k7_subset_1(X1,X2,X3) = k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X3)))
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35]),
    [final]).

cnf(c_0_43,plain,
    ( k1_setfam_1(k2_tarski(X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_36,c_0_21]),
    [final]).

cnf(c_0_44,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_37]),
    [final]).

fof(c_0_45,negated_conjecture,
    ( l1_struct_0(esk3_0)
    & m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))
    & ( k7_subset_1(u1_struct_0(esk3_0),k2_struct_0(esk3_0),esk4_0) != k1_xboole_0
      | esk4_0 != k2_struct_0(esk3_0) )
    & ( esk4_0 = k2_struct_0(esk3_0)
      | esk4_0 != k2_struct_0(esk3_0) )
    & ( k7_subset_1(u1_struct_0(esk3_0),k2_struct_0(esk3_0),esk4_0) != k1_xboole_0
      | k7_subset_1(u1_struct_0(esk3_0),k2_struct_0(esk3_0),esk4_0) = k1_xboole_0 )
    & ( esk4_0 = k2_struct_0(esk3_0)
      | k7_subset_1(u1_struct_0(esk3_0),k2_struct_0(esk3_0),esk4_0) = k1_xboole_0 ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_38])])])])).

cnf(c_0_46,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16]),
    [final]).

cnf(c_0_47,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40]),
    [final]).

cnf(c_0_48,plain,
    ( k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2)) = X2
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_41]),
    [final]).

cnf(c_0_49,plain,
    ( k7_subset_1(X1,X2,X3) = k7_subset_1(X4,X2,X3)
    | ~ r1_tarski(X2,X1)
    | ~ r1_tarski(X2,X4) ),
    inference(spm,[status(thm)],[c_0_42,c_0_42]),
    [final]).

cnf(c_0_50,plain,
    ( k7_subset_1(X1,X2,k1_xboole_0) = X2
    | ~ r1_tarski(X2,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_44]),
    [final]).

cnf(c_0_51,negated_conjecture,
    ( esk4_0 = k2_struct_0(esk3_0)
    | k7_subset_1(u1_struct_0(esk3_0),k2_struct_0(esk3_0),esk4_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_45]),
    [final]).

cnf(c_0_52,negated_conjecture,
    ( l1_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_45]),
    [final]).

cnf(c_0_53,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_45]),
    [final]).

cnf(c_0_54,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_29]),
    [final]).

cnf(c_0_55,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47]),
    [final]).

cnf(c_0_56,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15]),
    [final]).

cnf(c_0_57,plain,
    ( k7_subset_1(X1,k2_struct_0(X2),k7_subset_1(u1_struct_0(X2),k2_struct_0(X2),X3)) = X3
    | ~ l1_struct_0(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r1_tarski(k2_struct_0(X2),u1_struct_0(X2))
    | ~ r1_tarski(k2_struct_0(X2),X1) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49]),
    [final]).

cnf(c_0_58,plain,
    ( k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k2_struct_0(X1)) = k1_xboole_0
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(k2_struct_0(X1),u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_50]),
    [final]).

cnf(c_0_59,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk3_0),k2_struct_0(esk3_0),k1_xboole_0) = esk4_0
    | k2_struct_0(esk3_0) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_51]),c_0_52]),c_0_53])]),
    [final]).

cnf(c_0_60,negated_conjecture,
    ( r1_tarski(esk4_0,u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_53]),
    [final]).

cnf(c_0_61,plain,
    ( r2_hidden(esk1_1(k1_xboole_0),X1)
    | v1_xboole_0(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_62,plain,
    ( k7_subset_1(X1,k2_struct_0(X2),k7_subset_1(X3,k2_struct_0(X2),X4)) = X4
    | ~ l1_struct_0(X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r1_tarski(k2_struct_0(X2),u1_struct_0(X2))
    | ~ r1_tarski(k2_struct_0(X2),X1)
    | ~ r1_tarski(k2_struct_0(X2),X3) ),
    inference(spm,[status(thm)],[c_0_57,c_0_49]),
    [final]).

cnf(c_0_63,plain,
    ( k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(X2,k2_struct_0(X1),X3)) = X3
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(k2_struct_0(X1),u1_struct_0(X1))
    | ~ r1_tarski(k2_struct_0(X1),X2) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49]),
    [final]).

cnf(c_0_64,plain,
    ( k7_subset_1(X1,k2_struct_0(X2),k2_struct_0(X2)) = k1_xboole_0
    | ~ l1_struct_0(X2)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r1_tarski(k2_struct_0(X2),u1_struct_0(X2))
    | ~ r1_tarski(k2_struct_0(X2),X1) ),
    inference(spm,[status(thm)],[c_0_49,c_0_58]),
    [final]).

cnf(c_0_65,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk3_0),k2_struct_0(esk3_0),esk4_0) != k1_xboole_0
    | esk4_0 != k2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_45]),
    [final]).

cnf(c_0_66,negated_conjecture,
    ( k2_struct_0(esk3_0) = esk4_0
    | ~ r1_tarski(k2_struct_0(esk3_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_50]),
    [final]).

cnf(c_0_67,negated_conjecture,
    ( r2_hidden(X1,u1_struct_0(esk3_0))
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_60]),
    [final]).

cnf(c_0_68,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_61])).

cnf(c_0_69,plain,
    ( k7_subset_1(X1,k2_struct_0(X2),k5_xboole_0(k2_struct_0(X2),k1_setfam_1(k2_tarski(k2_struct_0(X2),X3)))) = X3
    | ~ l1_struct_0(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r1_tarski(k2_struct_0(X2),u1_struct_0(X2))
    | ~ r1_tarski(k2_struct_0(X2),X1)
    | ~ r1_tarski(k2_struct_0(X2),X4) ),
    inference(spm,[status(thm)],[c_0_62,c_0_42]),
    [final]).

cnf(c_0_70,plain,
    ( k5_xboole_0(k2_struct_0(X1),k1_setfam_1(k2_tarski(k2_struct_0(X1),k7_subset_1(X2,k2_struct_0(X1),X3)))) = X3
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(k2_struct_0(X1),u1_struct_0(X1))
    | ~ r1_tarski(k2_struct_0(X1),X4)
    | ~ r1_tarski(k2_struct_0(X1),X2) ),
    inference(spm,[status(thm)],[c_0_42,c_0_62]),
    [final]).

cnf(c_0_71,plain,
    ( k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k5_xboole_0(k2_struct_0(X1),k1_setfam_1(k2_tarski(k2_struct_0(X1),X2)))) = X2
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(k2_struct_0(X1),u1_struct_0(X1))
    | ~ r1_tarski(k2_struct_0(X1),X3) ),
    inference(spm,[status(thm)],[c_0_63,c_0_42]),
    [final]).

cnf(c_0_72,plain,
    ( k5_xboole_0(k2_struct_0(X1),k1_setfam_1(k2_tarski(k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2)))) = X2
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(k2_struct_0(X1),u1_struct_0(X1))
    | ~ r1_tarski(k2_struct_0(X1),X3) ),
    inference(spm,[status(thm)],[c_0_42,c_0_57]),
    [final]).

cnf(c_0_73,plain,
    ( k5_xboole_0(k2_struct_0(X1),k1_setfam_1(k2_tarski(k2_struct_0(X1),k2_struct_0(X1)))) = k1_xboole_0
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(k2_struct_0(X1),u1_struct_0(X1))
    | ~ r1_tarski(k2_struct_0(X1),X2) ),
    inference(spm,[status(thm)],[c_0_42,c_0_64])).

cnf(c_0_74,negated_conjecture,
    ( k7_subset_1(X1,k2_struct_0(esk3_0),esk4_0) != k1_xboole_0
    | ~ r1_tarski(k2_struct_0(esk3_0),u1_struct_0(esk3_0))
    | ~ r1_tarski(k2_struct_0(esk3_0),X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_49]),c_0_66]),
    [final]).

cnf(c_0_75,negated_conjecture,
    ( k5_xboole_0(esk4_0,k1_setfam_1(k2_tarski(esk4_0,X1))) = k7_subset_1(u1_struct_0(esk3_0),esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_53]),
    [final]).

cnf(c_0_76,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk2_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16]),
    [final]).

cnf(c_0_77,negated_conjecture,
    ( ~ r2_hidden(X1,esk4_0)
    | ~ v1_xboole_0(u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_67]),
    [final]).

cnf(c_0_78,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26]),
    [final]).

cnf(c_0_79,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_68,c_0_32])).

cnf(c_0_80,plain,
    ( k7_subset_1(X1,k2_struct_0(X2),k5_xboole_0(k2_struct_0(X2),k1_setfam_1(k2_tarski(k2_struct_0(X2),X3)))) = X3
    | ~ l1_struct_0(X2)
    | ~ r1_tarski(k2_struct_0(X2),u1_struct_0(X2))
    | ~ r1_tarski(k2_struct_0(X2),X1)
    | ~ r1_tarski(k2_struct_0(X2),X4)
    | ~ r1_tarski(X3,u1_struct_0(X2)) ),
    inference(spm,[status(thm)],[c_0_69,c_0_35]),
    [final]).

cnf(c_0_81,plain,
    ( k5_xboole_0(k2_struct_0(X1),k1_setfam_1(k2_tarski(k2_struct_0(X1),k7_subset_1(X2,k2_struct_0(X1),X3)))) = X3
    | ~ l1_struct_0(X1)
    | ~ r1_tarski(k2_struct_0(X1),u1_struct_0(X1))
    | ~ r1_tarski(k2_struct_0(X1),X4)
    | ~ r1_tarski(k2_struct_0(X1),X2)
    | ~ r1_tarski(X3,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_70,c_0_35]),
    [final]).

cnf(c_0_82,negated_conjecture,
    ( k7_subset_1(X1,k2_struct_0(esk3_0),k5_xboole_0(k2_struct_0(esk3_0),k1_setfam_1(k2_tarski(k2_struct_0(esk3_0),esk4_0)))) = esk4_0
    | ~ r1_tarski(k2_struct_0(esk3_0),u1_struct_0(esk3_0))
    | ~ r1_tarski(k2_struct_0(esk3_0),X1)
    | ~ r1_tarski(k2_struct_0(esk3_0),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_53]),c_0_52])]),
    [final]).

cnf(c_0_83,negated_conjecture,
    ( k5_xboole_0(k2_struct_0(esk3_0),k1_setfam_1(k2_tarski(k2_struct_0(esk3_0),k7_subset_1(X1,k2_struct_0(esk3_0),esk4_0)))) = esk4_0
    | ~ r1_tarski(k2_struct_0(esk3_0),u1_struct_0(esk3_0))
    | ~ r1_tarski(k2_struct_0(esk3_0),X2)
    | ~ r1_tarski(k2_struct_0(esk3_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_53]),c_0_52])]),
    [final]).

cnf(c_0_84,plain,
    ( k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k5_xboole_0(k2_struct_0(X1),k1_setfam_1(k2_tarski(k2_struct_0(X1),X2)))) = X2
    | ~ l1_struct_0(X1)
    | ~ r1_tarski(k2_struct_0(X1),u1_struct_0(X1))
    | ~ r1_tarski(k2_struct_0(X1),X3)
    | ~ r1_tarski(X2,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_71,c_0_35]),
    [final]).

cnf(c_0_85,plain,
    ( k5_xboole_0(k2_struct_0(X1),k1_setfam_1(k2_tarski(k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2)))) = X2
    | ~ l1_struct_0(X1)
    | ~ r1_tarski(k2_struct_0(X1),u1_struct_0(X1))
    | ~ r1_tarski(k2_struct_0(X1),X3)
    | ~ r1_tarski(X2,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_72,c_0_35]),
    [final]).

cnf(c_0_86,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk3_0),k2_struct_0(esk3_0),k5_xboole_0(k2_struct_0(esk3_0),k1_setfam_1(k2_tarski(k2_struct_0(esk3_0),esk4_0)))) = esk4_0
    | ~ r1_tarski(k2_struct_0(esk3_0),u1_struct_0(esk3_0))
    | ~ r1_tarski(k2_struct_0(esk3_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_53]),c_0_52])]),
    [final]).

cnf(c_0_87,negated_conjecture,
    ( k5_xboole_0(k2_struct_0(esk3_0),k1_setfam_1(k2_tarski(k2_struct_0(esk3_0),k7_subset_1(u1_struct_0(esk3_0),k2_struct_0(esk3_0),esk4_0)))) = esk4_0
    | ~ r1_tarski(k2_struct_0(esk3_0),u1_struct_0(esk3_0))
    | ~ r1_tarski(k2_struct_0(esk3_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_53]),c_0_52])]),
    [final]).

cnf(c_0_88,plain,
    ( k5_xboole_0(k2_struct_0(X1),k1_setfam_1(k2_tarski(k2_struct_0(X1),k2_struct_0(X1)))) = k1_xboole_0
    | ~ l1_struct_0(X1)
    | ~ r1_tarski(k2_struct_0(X1),u1_struct_0(X1))
    | ~ r1_tarski(k2_struct_0(X1),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_35]),c_0_47])]),
    [final]).

cnf(c_0_89,negated_conjecture,
    ( k5_xboole_0(k2_struct_0(esk3_0),k1_setfam_1(k2_tarski(k2_struct_0(esk3_0),esk4_0))) != k1_xboole_0
    | ~ r1_tarski(k2_struct_0(esk3_0),u1_struct_0(esk3_0))
    | ~ r1_tarski(k2_struct_0(esk3_0),X1) ),
    inference(spm,[status(thm)],[c_0_74,c_0_42]),
    [final]).

cnf(c_0_90,negated_conjecture,
    ( k7_subset_1(X1,esk4_0,X2) = k7_subset_1(u1_struct_0(esk3_0),esk4_0,X2)
    | ~ r1_tarski(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_75,c_0_42]),
    [final]).

cnf(c_0_91,negated_conjecture,
    ( r1_tarski(X1,u1_struct_0(esk3_0))
    | ~ r2_hidden(esk2_2(X1,u1_struct_0(esk3_0)),esk4_0) ),
    inference(spm,[status(thm)],[c_0_76,c_0_67]),
    [final]).

cnf(c_0_92,negated_conjecture,
    ( ~ r1_tarski(u1_struct_0(esk3_0),k1_xboole_0)
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_77,c_0_32]),
    [final]).

cnf(c_0_93,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_78,c_0_47]),
    [final]).

cnf(c_0_94,negated_conjecture,
    ( u1_struct_0(esk3_0) = esk4_0
    | ~ r1_tarski(u1_struct_0(esk3_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_78,c_0_60]),
    [final]).

cnf(c_0_95,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk3_0),esk4_0,k1_xboole_0) = esk4_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_43]),c_0_44]),
    [final]).

cnf(c_0_96,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_79,c_0_47]),
    [final]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 12:53:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.12/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.12/0.38  #
% 0.12/0.38  # Preprocessing time       : 0.027 s
% 0.12/0.38  # Presaturation interreduction done
% 0.12/0.38  
% 0.12/0.38  # No proof found!
% 0.12/0.38  # SZS status CounterSatisfiable
% 0.12/0.38  # SZS output start Saturation
% 0.12/0.38  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.12/0.38  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.12/0.38  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.12/0.38  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.12/0.38  fof(t69_xboole_1, axiom, ![X1, X2]:(~(v1_xboole_0(X2))=>~((r1_tarski(X2,X1)&r1_xboole_0(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_xboole_1)).
% 0.12/0.38  fof(t65_xboole_1, axiom, ![X1]:r1_xboole_0(X1,k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 0.12/0.38  fof(redefinition_k7_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k7_subset_1(X1,X2,X3)=k4_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 0.12/0.38  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.12/0.38  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.12/0.38  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 0.12/0.38  fof(t5_boole, axiom, ![X1]:k5_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 0.12/0.38  fof(t23_pre_topc, conjecture, ![X1]:(l1_struct_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(~((X2!=k2_struct_0(X1)&k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2)=k1_xboole_0))&~((k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2)!=k1_xboole_0&X2=k2_struct_0(X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_pre_topc)).
% 0.12/0.38  fof(t22_pre_topc, axiom, ![X1]:(l1_struct_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2))=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_pre_topc)).
% 0.12/0.38  fof(c_0_13, plain, ![X16, X17]:k4_xboole_0(X16,X17)=k5_xboole_0(X16,k3_xboole_0(X16,X17)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.12/0.38  fof(c_0_14, plain, ![X26, X27]:k1_setfam_1(k2_tarski(X26,X27))=k3_xboole_0(X26,X27), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.12/0.38  fof(c_0_15, plain, ![X4, X5, X6]:((~v1_xboole_0(X4)|~r2_hidden(X5,X4))&(r2_hidden(esk1_1(X6),X6)|v1_xboole_0(X6))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.12/0.38  fof(c_0_16, plain, ![X8, X9, X10, X11, X12]:((~r1_tarski(X8,X9)|(~r2_hidden(X10,X8)|r2_hidden(X10,X9)))&((r2_hidden(esk2_2(X11,X12),X11)|r1_tarski(X11,X12))&(~r2_hidden(esk2_2(X11,X12),X12)|r1_tarski(X11,X12)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.12/0.38  fof(c_0_17, plain, ![X21, X22]:(v1_xboole_0(X22)|(~r1_tarski(X22,X21)|~r1_xboole_0(X22,X21))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t69_xboole_1])])])).
% 0.12/0.38  fof(c_0_18, plain, ![X20]:r1_xboole_0(X20,k1_xboole_0), inference(variable_rename,[status(thm)],[t65_xboole_1])).
% 0.12/0.38  fof(c_0_19, plain, ![X23, X24, X25]:(~m1_subset_1(X24,k1_zfmisc_1(X23))|k7_subset_1(X23,X24,X25)=k4_xboole_0(X24,X25)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).
% 0.12/0.38  cnf(c_0_20, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.12/0.38  cnf(c_0_21, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.12/0.38  cnf(c_0_22, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_15]), ['final']).
% 0.12/0.38  cnf(c_0_23, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16]), ['final']).
% 0.12/0.38  cnf(c_0_24, plain, (v1_xboole_0(X1)|~r1_tarski(X1,X2)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17]), ['final']).
% 0.12/0.38  cnf(c_0_25, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_18]), ['final']).
% 0.12/0.38  fof(c_0_26, plain, ![X14, X15]:(((r1_tarski(X14,X15)|X14!=X15)&(r1_tarski(X15,X14)|X14!=X15))&(~r1_tarski(X14,X15)|~r1_tarski(X15,X14)|X14=X15)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.12/0.38  cnf(c_0_27, plain, (k7_subset_1(X2,X1,X3)=k4_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.12/0.38  cnf(c_0_28, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))), inference(rw,[status(thm)],[c_0_20, c_0_21])).
% 0.12/0.38  fof(c_0_29, plain, ![X28, X29]:((~m1_subset_1(X28,k1_zfmisc_1(X29))|r1_tarski(X28,X29))&(~r1_tarski(X28,X29)|m1_subset_1(X28,k1_zfmisc_1(X29)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.12/0.38  fof(c_0_30, plain, ![X18]:k3_xboole_0(X18,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 0.12/0.38  cnf(c_0_31, plain, (r1_tarski(X1,X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_22, c_0_23]), ['final']).
% 0.12/0.38  cnf(c_0_32, plain, (v1_xboole_0(X1)|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_24, c_0_25]), ['final']).
% 0.12/0.38  cnf(c_0_33, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.12/0.38  cnf(c_0_34, plain, (k7_subset_1(X2,X1,X3)=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X3)))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_27, c_0_28]), ['final']).
% 0.12/0.38  cnf(c_0_35, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_29]), ['final']).
% 0.12/0.38  cnf(c_0_36, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.12/0.38  fof(c_0_37, plain, ![X19]:k5_xboole_0(X19,k1_xboole_0)=X19, inference(variable_rename,[status(thm)],[t5_boole])).
% 0.12/0.38  fof(c_0_38, negated_conjecture, ~(![X1]:(l1_struct_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(~((X2!=k2_struct_0(X1)&k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2)=k1_xboole_0))&~((k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2)!=k1_xboole_0&X2=k2_struct_0(X1))))))), inference(assume_negation,[status(cth)],[t23_pre_topc])).
% 0.12/0.38  cnf(c_0_39, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_31, c_0_32]), ['final']).
% 0.12/0.38  cnf(c_0_40, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_33]), ['final']).
% 0.12/0.38  fof(c_0_41, plain, ![X30, X31]:(~l1_struct_0(X30)|(~m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))|k7_subset_1(u1_struct_0(X30),k2_struct_0(X30),k7_subset_1(u1_struct_0(X30),k2_struct_0(X30),X31))=X31)), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t22_pre_topc])])])).
% 0.12/0.38  cnf(c_0_42, plain, (k7_subset_1(X1,X2,X3)=k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X3)))|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_34, c_0_35]), ['final']).
% 0.12/0.38  cnf(c_0_43, plain, (k1_setfam_1(k2_tarski(X1,k1_xboole_0))=k1_xboole_0), inference(rw,[status(thm)],[c_0_36, c_0_21]), ['final']).
% 0.12/0.38  cnf(c_0_44, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_37]), ['final']).
% 0.12/0.38  fof(c_0_45, negated_conjecture, (l1_struct_0(esk3_0)&(m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))&(((k7_subset_1(u1_struct_0(esk3_0),k2_struct_0(esk3_0),esk4_0)!=k1_xboole_0|esk4_0!=k2_struct_0(esk3_0))&(esk4_0=k2_struct_0(esk3_0)|esk4_0!=k2_struct_0(esk3_0)))&((k7_subset_1(u1_struct_0(esk3_0),k2_struct_0(esk3_0),esk4_0)!=k1_xboole_0|k7_subset_1(u1_struct_0(esk3_0),k2_struct_0(esk3_0),esk4_0)=k1_xboole_0)&(esk4_0=k2_struct_0(esk3_0)|k7_subset_1(u1_struct_0(esk3_0),k2_struct_0(esk3_0),esk4_0)=k1_xboole_0))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_38])])])])).
% 0.12/0.38  cnf(c_0_46, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_16]), ['final']).
% 0.12/0.38  cnf(c_0_47, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_39, c_0_40]), ['final']).
% 0.12/0.38  cnf(c_0_48, plain, (k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2))=X2|~l1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_41]), ['final']).
% 0.12/0.38  cnf(c_0_49, plain, (k7_subset_1(X1,X2,X3)=k7_subset_1(X4,X2,X3)|~r1_tarski(X2,X1)|~r1_tarski(X2,X4)), inference(spm,[status(thm)],[c_0_42, c_0_42]), ['final']).
% 0.12/0.38  cnf(c_0_50, plain, (k7_subset_1(X1,X2,k1_xboole_0)=X2|~r1_tarski(X2,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_44]), ['final']).
% 0.12/0.38  cnf(c_0_51, negated_conjecture, (esk4_0=k2_struct_0(esk3_0)|k7_subset_1(u1_struct_0(esk3_0),k2_struct_0(esk3_0),esk4_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_45]), ['final']).
% 0.12/0.38  cnf(c_0_52, negated_conjecture, (l1_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_45]), ['final']).
% 0.12/0.38  cnf(c_0_53, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_45]), ['final']).
% 0.12/0.38  cnf(c_0_54, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_29]), ['final']).
% 0.12/0.38  cnf(c_0_55, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_46, c_0_47]), ['final']).
% 0.12/0.38  cnf(c_0_56, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_15]), ['final']).
% 0.12/0.38  cnf(c_0_57, plain, (k7_subset_1(X1,k2_struct_0(X2),k7_subset_1(u1_struct_0(X2),k2_struct_0(X2),X3))=X3|~l1_struct_0(X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~r1_tarski(k2_struct_0(X2),u1_struct_0(X2))|~r1_tarski(k2_struct_0(X2),X1)), inference(spm,[status(thm)],[c_0_48, c_0_49]), ['final']).
% 0.12/0.38  cnf(c_0_58, plain, (k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k2_struct_0(X1))=k1_xboole_0|~l1_struct_0(X1)|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(k2_struct_0(X1),u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_48, c_0_50]), ['final']).
% 0.12/0.38  cnf(c_0_59, negated_conjecture, (k7_subset_1(u1_struct_0(esk3_0),k2_struct_0(esk3_0),k1_xboole_0)=esk4_0|k2_struct_0(esk3_0)=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_51]), c_0_52]), c_0_53])]), ['final']).
% 0.12/0.38  cnf(c_0_60, negated_conjecture, (r1_tarski(esk4_0,u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_54, c_0_53]), ['final']).
% 0.12/0.38  cnf(c_0_61, plain, (r2_hidden(esk1_1(k1_xboole_0),X1)|v1_xboole_0(k1_xboole_0)), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.12/0.38  cnf(c_0_62, plain, (k7_subset_1(X1,k2_struct_0(X2),k7_subset_1(X3,k2_struct_0(X2),X4))=X4|~l1_struct_0(X2)|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))|~r1_tarski(k2_struct_0(X2),u1_struct_0(X2))|~r1_tarski(k2_struct_0(X2),X1)|~r1_tarski(k2_struct_0(X2),X3)), inference(spm,[status(thm)],[c_0_57, c_0_49]), ['final']).
% 0.12/0.38  cnf(c_0_63, plain, (k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(X2,k2_struct_0(X1),X3))=X3|~l1_struct_0(X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(k2_struct_0(X1),u1_struct_0(X1))|~r1_tarski(k2_struct_0(X1),X2)), inference(spm,[status(thm)],[c_0_48, c_0_49]), ['final']).
% 0.12/0.38  cnf(c_0_64, plain, (k7_subset_1(X1,k2_struct_0(X2),k2_struct_0(X2))=k1_xboole_0|~l1_struct_0(X2)|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X2)))|~r1_tarski(k2_struct_0(X2),u1_struct_0(X2))|~r1_tarski(k2_struct_0(X2),X1)), inference(spm,[status(thm)],[c_0_49, c_0_58]), ['final']).
% 0.12/0.38  cnf(c_0_65, negated_conjecture, (k7_subset_1(u1_struct_0(esk3_0),k2_struct_0(esk3_0),esk4_0)!=k1_xboole_0|esk4_0!=k2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_45]), ['final']).
% 0.12/0.38  cnf(c_0_66, negated_conjecture, (k2_struct_0(esk3_0)=esk4_0|~r1_tarski(k2_struct_0(esk3_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_59, c_0_50]), ['final']).
% 0.12/0.38  cnf(c_0_67, negated_conjecture, (r2_hidden(X1,u1_struct_0(esk3_0))|~r2_hidden(X1,esk4_0)), inference(spm,[status(thm)],[c_0_46, c_0_60]), ['final']).
% 0.12/0.38  cnf(c_0_68, plain, (v1_xboole_0(k1_xboole_0)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_22, c_0_61])).
% 0.12/0.38  cnf(c_0_69, plain, (k7_subset_1(X1,k2_struct_0(X2),k5_xboole_0(k2_struct_0(X2),k1_setfam_1(k2_tarski(k2_struct_0(X2),X3))))=X3|~l1_struct_0(X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~r1_tarski(k2_struct_0(X2),u1_struct_0(X2))|~r1_tarski(k2_struct_0(X2),X1)|~r1_tarski(k2_struct_0(X2),X4)), inference(spm,[status(thm)],[c_0_62, c_0_42]), ['final']).
% 0.12/0.38  cnf(c_0_70, plain, (k5_xboole_0(k2_struct_0(X1),k1_setfam_1(k2_tarski(k2_struct_0(X1),k7_subset_1(X2,k2_struct_0(X1),X3))))=X3|~l1_struct_0(X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(k2_struct_0(X1),u1_struct_0(X1))|~r1_tarski(k2_struct_0(X1),X4)|~r1_tarski(k2_struct_0(X1),X2)), inference(spm,[status(thm)],[c_0_42, c_0_62]), ['final']).
% 0.12/0.38  cnf(c_0_71, plain, (k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k5_xboole_0(k2_struct_0(X1),k1_setfam_1(k2_tarski(k2_struct_0(X1),X2))))=X2|~l1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(k2_struct_0(X1),u1_struct_0(X1))|~r1_tarski(k2_struct_0(X1),X3)), inference(spm,[status(thm)],[c_0_63, c_0_42]), ['final']).
% 0.12/0.38  cnf(c_0_72, plain, (k5_xboole_0(k2_struct_0(X1),k1_setfam_1(k2_tarski(k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2))))=X2|~l1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(k2_struct_0(X1),u1_struct_0(X1))|~r1_tarski(k2_struct_0(X1),X3)), inference(spm,[status(thm)],[c_0_42, c_0_57]), ['final']).
% 0.12/0.38  cnf(c_0_73, plain, (k5_xboole_0(k2_struct_0(X1),k1_setfam_1(k2_tarski(k2_struct_0(X1),k2_struct_0(X1))))=k1_xboole_0|~l1_struct_0(X1)|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(k2_struct_0(X1),u1_struct_0(X1))|~r1_tarski(k2_struct_0(X1),X2)), inference(spm,[status(thm)],[c_0_42, c_0_64])).
% 0.12/0.38  cnf(c_0_74, negated_conjecture, (k7_subset_1(X1,k2_struct_0(esk3_0),esk4_0)!=k1_xboole_0|~r1_tarski(k2_struct_0(esk3_0),u1_struct_0(esk3_0))|~r1_tarski(k2_struct_0(esk3_0),X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_49]), c_0_66]), ['final']).
% 0.12/0.38  cnf(c_0_75, negated_conjecture, (k5_xboole_0(esk4_0,k1_setfam_1(k2_tarski(esk4_0,X1)))=k7_subset_1(u1_struct_0(esk3_0),esk4_0,X1)), inference(spm,[status(thm)],[c_0_34, c_0_53]), ['final']).
% 0.12/0.38  cnf(c_0_76, plain, (r1_tarski(X1,X2)|~r2_hidden(esk2_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_16]), ['final']).
% 0.12/0.38  cnf(c_0_77, negated_conjecture, (~r2_hidden(X1,esk4_0)|~v1_xboole_0(u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_22, c_0_67]), ['final']).
% 0.12/0.38  cnf(c_0_78, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_26]), ['final']).
% 0.12/0.38  cnf(c_0_79, plain, (v1_xboole_0(k1_xboole_0)|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_68, c_0_32])).
% 0.12/0.38  cnf(c_0_80, plain, (k7_subset_1(X1,k2_struct_0(X2),k5_xboole_0(k2_struct_0(X2),k1_setfam_1(k2_tarski(k2_struct_0(X2),X3))))=X3|~l1_struct_0(X2)|~r1_tarski(k2_struct_0(X2),u1_struct_0(X2))|~r1_tarski(k2_struct_0(X2),X1)|~r1_tarski(k2_struct_0(X2),X4)|~r1_tarski(X3,u1_struct_0(X2))), inference(spm,[status(thm)],[c_0_69, c_0_35]), ['final']).
% 0.12/0.38  cnf(c_0_81, plain, (k5_xboole_0(k2_struct_0(X1),k1_setfam_1(k2_tarski(k2_struct_0(X1),k7_subset_1(X2,k2_struct_0(X1),X3))))=X3|~l1_struct_0(X1)|~r1_tarski(k2_struct_0(X1),u1_struct_0(X1))|~r1_tarski(k2_struct_0(X1),X4)|~r1_tarski(k2_struct_0(X1),X2)|~r1_tarski(X3,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_70, c_0_35]), ['final']).
% 0.12/0.38  cnf(c_0_82, negated_conjecture, (k7_subset_1(X1,k2_struct_0(esk3_0),k5_xboole_0(k2_struct_0(esk3_0),k1_setfam_1(k2_tarski(k2_struct_0(esk3_0),esk4_0))))=esk4_0|~r1_tarski(k2_struct_0(esk3_0),u1_struct_0(esk3_0))|~r1_tarski(k2_struct_0(esk3_0),X1)|~r1_tarski(k2_struct_0(esk3_0),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_53]), c_0_52])]), ['final']).
% 0.12/0.38  cnf(c_0_83, negated_conjecture, (k5_xboole_0(k2_struct_0(esk3_0),k1_setfam_1(k2_tarski(k2_struct_0(esk3_0),k7_subset_1(X1,k2_struct_0(esk3_0),esk4_0))))=esk4_0|~r1_tarski(k2_struct_0(esk3_0),u1_struct_0(esk3_0))|~r1_tarski(k2_struct_0(esk3_0),X2)|~r1_tarski(k2_struct_0(esk3_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_53]), c_0_52])]), ['final']).
% 0.12/0.38  cnf(c_0_84, plain, (k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k5_xboole_0(k2_struct_0(X1),k1_setfam_1(k2_tarski(k2_struct_0(X1),X2))))=X2|~l1_struct_0(X1)|~r1_tarski(k2_struct_0(X1),u1_struct_0(X1))|~r1_tarski(k2_struct_0(X1),X3)|~r1_tarski(X2,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_71, c_0_35]), ['final']).
% 0.12/0.38  cnf(c_0_85, plain, (k5_xboole_0(k2_struct_0(X1),k1_setfam_1(k2_tarski(k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2))))=X2|~l1_struct_0(X1)|~r1_tarski(k2_struct_0(X1),u1_struct_0(X1))|~r1_tarski(k2_struct_0(X1),X3)|~r1_tarski(X2,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_72, c_0_35]), ['final']).
% 0.12/0.38  cnf(c_0_86, negated_conjecture, (k7_subset_1(u1_struct_0(esk3_0),k2_struct_0(esk3_0),k5_xboole_0(k2_struct_0(esk3_0),k1_setfam_1(k2_tarski(k2_struct_0(esk3_0),esk4_0))))=esk4_0|~r1_tarski(k2_struct_0(esk3_0),u1_struct_0(esk3_0))|~r1_tarski(k2_struct_0(esk3_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_53]), c_0_52])]), ['final']).
% 0.12/0.38  cnf(c_0_87, negated_conjecture, (k5_xboole_0(k2_struct_0(esk3_0),k1_setfam_1(k2_tarski(k2_struct_0(esk3_0),k7_subset_1(u1_struct_0(esk3_0),k2_struct_0(esk3_0),esk4_0))))=esk4_0|~r1_tarski(k2_struct_0(esk3_0),u1_struct_0(esk3_0))|~r1_tarski(k2_struct_0(esk3_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_53]), c_0_52])]), ['final']).
% 0.12/0.38  cnf(c_0_88, plain, (k5_xboole_0(k2_struct_0(X1),k1_setfam_1(k2_tarski(k2_struct_0(X1),k2_struct_0(X1))))=k1_xboole_0|~l1_struct_0(X1)|~r1_tarski(k2_struct_0(X1),u1_struct_0(X1))|~r1_tarski(k2_struct_0(X1),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_35]), c_0_47])]), ['final']).
% 0.12/0.38  cnf(c_0_89, negated_conjecture, (k5_xboole_0(k2_struct_0(esk3_0),k1_setfam_1(k2_tarski(k2_struct_0(esk3_0),esk4_0)))!=k1_xboole_0|~r1_tarski(k2_struct_0(esk3_0),u1_struct_0(esk3_0))|~r1_tarski(k2_struct_0(esk3_0),X1)), inference(spm,[status(thm)],[c_0_74, c_0_42]), ['final']).
% 0.12/0.38  cnf(c_0_90, negated_conjecture, (k7_subset_1(X1,esk4_0,X2)=k7_subset_1(u1_struct_0(esk3_0),esk4_0,X2)|~r1_tarski(esk4_0,X1)), inference(spm,[status(thm)],[c_0_75, c_0_42]), ['final']).
% 0.12/0.38  cnf(c_0_91, negated_conjecture, (r1_tarski(X1,u1_struct_0(esk3_0))|~r2_hidden(esk2_2(X1,u1_struct_0(esk3_0)),esk4_0)), inference(spm,[status(thm)],[c_0_76, c_0_67]), ['final']).
% 0.12/0.38  cnf(c_0_92, negated_conjecture, (~r1_tarski(u1_struct_0(esk3_0),k1_xboole_0)|~r2_hidden(X1,esk4_0)), inference(spm,[status(thm)],[c_0_77, c_0_32]), ['final']).
% 0.12/0.38  cnf(c_0_93, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_78, c_0_47]), ['final']).
% 0.12/0.38  cnf(c_0_94, negated_conjecture, (u1_struct_0(esk3_0)=esk4_0|~r1_tarski(u1_struct_0(esk3_0),esk4_0)), inference(spm,[status(thm)],[c_0_78, c_0_60]), ['final']).
% 0.12/0.38  cnf(c_0_95, negated_conjecture, (k7_subset_1(u1_struct_0(esk3_0),esk4_0,k1_xboole_0)=esk4_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_43]), c_0_44]), ['final']).
% 0.12/0.38  cnf(c_0_96, plain, (v1_xboole_0(k1_xboole_0)), inference(spm,[status(thm)],[c_0_79, c_0_47]), ['final']).
% 0.12/0.38  # SZS output end Saturation
% 0.12/0.38  # Proof object total steps             : 97
% 0.12/0.38  # Proof object clause steps            : 70
% 0.12/0.38  # Proof object formula steps           : 27
% 0.12/0.38  # Proof object conjectures             : 24
% 0.12/0.38  # Proof object clause conjectures      : 21
% 0.12/0.38  # Proof object formula conjectures     : 3
% 0.12/0.38  # Proof object initial clauses used    : 21
% 0.12/0.38  # Proof object initial formulas used   : 13
% 0.12/0.38  # Proof object generating inferences   : 45
% 0.12/0.38  # Proof object simplifying inferences  : 20
% 0.12/0.38  # Parsed axioms                        : 13
% 0.12/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.38  # Initial clauses                      : 24
% 0.12/0.38  # Removed in clause preprocessing      : 4
% 0.12/0.38  # Initial clauses in saturation        : 20
% 0.12/0.38  # Processed clauses                    : 158
% 0.12/0.38  # ...of these trivial                  : 0
% 0.12/0.38  # ...subsumed                          : 73
% 0.12/0.38  # ...remaining for further processing  : 85
% 0.12/0.38  # Other redundant clauses eliminated   : 2
% 0.12/0.38  # Clauses deleted for lack of memory   : 0
% 0.12/0.38  # Backward-subsumed                    : 1
% 0.12/0.38  # Backward-rewritten                   : 3
% 0.12/0.38  # Generated clauses                    : 135
% 0.12/0.38  # ...of the previous two non-trivial   : 121
% 0.12/0.38  # Contextual simplify-reflections      : 1
% 0.12/0.38  # Paramodulations                      : 133
% 0.12/0.38  # Factorizations                       : 0
% 0.12/0.38  # Equation resolutions                 : 2
% 0.12/0.38  # Propositional unsat checks           : 0
% 0.12/0.38  #    Propositional check models        : 0
% 0.12/0.38  #    Propositional check unsatisfiable : 0
% 0.12/0.38  #    Propositional clauses             : 0
% 0.12/0.38  #    Propositional clauses after purity: 0
% 0.12/0.38  #    Propositional unsat core size     : 0
% 0.12/0.38  #    Propositional preprocessing time  : 0.000
% 0.12/0.38  #    Propositional encoding time       : 0.000
% 0.12/0.38  #    Propositional solver time         : 0.000
% 0.12/0.38  #    Success case prop preproc time    : 0.000
% 0.12/0.38  #    Success case prop encoding time   : 0.000
% 0.12/0.38  #    Success case prop solver time     : 0.000
% 0.12/0.38  # Current number of processed clauses  : 60
% 0.12/0.38  #    Positive orientable unit clauses  : 11
% 0.12/0.38  #    Positive unorientable unit clauses: 0
% 0.12/0.38  #    Negative unit clauses             : 0
% 0.12/0.38  #    Non-unit-clauses                  : 49
% 0.12/0.38  # Current number of unprocessed clauses: 0
% 0.12/0.38  # ...number of literals in the above   : 0
% 0.12/0.38  # Current number of archived formulas  : 0
% 0.12/0.38  # Current number of archived clauses   : 25
% 0.12/0.38  # Clause-clause subsumption calls (NU) : 1447
% 0.12/0.38  # Rec. Clause-clause subsumption calls : 609
% 0.12/0.38  # Non-unit clause-clause subsumptions  : 75
% 0.12/0.38  # Unit Clause-clause subsumption calls : 8
% 0.12/0.38  # Rewrite failures with RHS unbound    : 0
% 0.12/0.38  # BW rewrite match attempts            : 2
% 0.12/0.38  # BW rewrite match successes           : 1
% 0.12/0.38  # Condensation attempts                : 0
% 0.12/0.38  # Condensation successes               : 0
% 0.12/0.38  # Termbank termtop insertions          : 4650
% 0.12/0.38  
% 0.12/0.38  # -------------------------------------------------
% 0.12/0.38  # User time                : 0.035 s
% 0.12/0.38  # System time              : 0.004 s
% 0.12/0.38  # Total time               : 0.039 s
% 0.12/0.38  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
