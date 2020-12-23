%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:08:43 EST 2020

% Result     : CounterSatisfiable 0.13s
% Output     : Saturation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 936 expanded)
%              Number of clauses        :   50 ( 388 expanded)
%              Number of leaves         :   17 ( 271 expanded)
%              Depth                    :    9
%              Number of atoms          :  195 (1355 expanded)
%              Number of equality atoms :   87 ( 979 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    6 (   2 average)

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

fof(redefinition_k7_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k7_subset_1(X1,X2,X3) = k4_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

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

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(t22_pre_topc,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2)) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_pre_topc)).

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

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(c_0_17,plain,(
    ! [X45,X46] : k1_setfam_1(k2_tarski(X45,X46)) = k3_xboole_0(X45,X46) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_18,plain,(
    ! [X14,X15] : k1_enumset1(X14,X14,X15) = k2_tarski(X14,X15) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_19,plain,(
    ! [X10,X11] : k4_xboole_0(X10,X11) = k5_xboole_0(X10,k3_xboole_0(X10,X11)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_20,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_21,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_22,plain,(
    ! [X41,X42,X43] :
      ( ~ m1_subset_1(X42,k1_zfmisc_1(X41))
      | k7_subset_1(X41,X42,X43) = k4_xboole_0(X42,X43) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).

cnf(c_0_23,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_20,c_0_21])).

fof(c_0_25,plain,(
    ! [X16,X17,X18] : k2_enumset1(X16,X16,X17,X18) = k1_enumset1(X16,X17,X18) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_26,plain,(
    ! [X19,X20,X21,X22] : k3_enumset1(X19,X19,X20,X21,X22) = k2_enumset1(X19,X20,X21,X22) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_27,plain,(
    ! [X23,X24,X25,X26,X27] : k4_enumset1(X23,X23,X24,X25,X26,X27) = k3_enumset1(X23,X24,X25,X26,X27) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_28,plain,(
    ! [X28,X29,X30,X31,X32,X33] : k5_enumset1(X28,X28,X29,X30,X31,X32,X33) = k4_enumset1(X28,X29,X30,X31,X32,X33) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_29,plain,(
    ! [X34,X35,X36,X37,X38,X39,X40] : k6_enumset1(X34,X34,X35,X36,X37,X38,X39,X40) = k5_enumset1(X34,X35,X36,X37,X38,X39,X40) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

cnf(c_0_30,plain,
    ( k7_subset_1(X2,X1,X3) = k4_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_31,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2))) ),
    inference(rw,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_32,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_33,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_34,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_35,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_36,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_37,plain,(
    ! [X12] : k3_xboole_0(X12,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

fof(c_0_38,plain,(
    ! [X52,X53] :
      ( ~ l1_struct_0(X52)
      | ~ m1_subset_1(X53,k1_zfmisc_1(u1_struct_0(X52)))
      | k7_subset_1(u1_struct_0(X52),k2_struct_0(X52),k7_subset_1(u1_struct_0(X52),k2_struct_0(X52),X53)) = X53 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t22_pre_topc])])])).

cnf(c_0_39,plain,
    ( k7_subset_1(X2,X1,X3) = k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_31]),c_0_32]),c_0_33]),c_0_34]),c_0_35]),c_0_36]),
    [final]).

cnf(c_0_40,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

fof(c_0_41,plain,(
    ! [X13] : k5_xboole_0(X13,k1_xboole_0) = X13 ),
    inference(variable_rename,[status(thm)],[t5_boole])).

fof(c_0_42,negated_conjecture,(
    ~ ! [X1] :
        ( l1_struct_0(X1)
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( ~ ( X2 != k2_struct_0(X1)
                  & k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2) = k1_xboole_0 )
              & ~ ( k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2) != k1_xboole_0
                  & X2 = k2_struct_0(X1) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t23_pre_topc])).

fof(c_0_43,plain,(
    ! [X8,X9] :
      ( ( r1_tarski(X8,X9)
        | X8 != X9 )
      & ( r1_tarski(X9,X8)
        | X8 != X9 )
      & ( ~ r1_tarski(X8,X9)
        | ~ r1_tarski(X9,X8)
        | X8 = X9 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_44,plain,(
    ! [X47,X48] :
      ( ( ~ m1_subset_1(X47,k1_zfmisc_1(X48))
        | r1_tarski(X47,X48) )
      & ( ~ r1_tarski(X47,X48)
        | m1_subset_1(X47,k1_zfmisc_1(X48)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_45,plain,
    ( k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2)) = X2
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_38]),
    [final]).

cnf(c_0_46,plain,
    ( k7_subset_1(X1,X2,X3) = k7_subset_1(X4,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X4)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_39]),
    [final]).

cnf(c_0_47,plain,
    ( k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_24]),c_0_32]),c_0_33]),c_0_34]),c_0_35]),c_0_36]),
    [final]).

cnf(c_0_48,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_41]),
    [final]).

fof(c_0_49,plain,(
    ! [X44] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X44)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

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
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_42])])])])).

cnf(c_0_51,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43]),
    [final]).

cnf(c_0_52,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_44]),
    [final]).

cnf(c_0_53,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_54,plain,
    ( k7_subset_1(X1,k2_struct_0(X2),k7_subset_1(u1_struct_0(X2),k2_struct_0(X2),X3)) = X3
    | ~ l1_struct_0(X2)
    | ~ m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46]),
    [final]).

cnf(c_0_55,plain,
    ( k7_subset_1(X1,X2,k1_xboole_0) = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_47]),c_0_48]),
    [final]).

cnf(c_0_56,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_49]),
    [final]).

cnf(c_0_57,negated_conjecture,
    ( esk2_0 = k2_struct_0(esk1_0)
    | k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_50]),
    [final]).

cnf(c_0_58,negated_conjecture,
    ( l1_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_50]),
    [final]).

cnf(c_0_59,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_50]),
    [final]).

cnf(c_0_60,plain,
    ( X1 = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52]),
    [final]).

fof(c_0_61,plain,(
    ! [X49,X50,X51] :
      ( ~ r2_hidden(X49,X50)
      | ~ m1_subset_1(X50,k1_zfmisc_1(X51))
      | m1_subset_1(X49,X51) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_62,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_44]),
    [final]).

cnf(c_0_63,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_53]),
    [final]).

cnf(c_0_64,plain,
    ( k7_subset_1(X1,k2_struct_0(X2),k7_subset_1(X3,k2_struct_0(X2),X4)) = X4
    | ~ l1_struct_0(X2)
    | ~ m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_46]),
    [final]).

cnf(c_0_65,plain,
    ( k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(X2,k2_struct_0(X1),X3)) = X3
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46]),
    [final]).

cnf(c_0_66,plain,
    ( k7_subset_1(X1,k2_struct_0(X2),k2_struct_0(X2)) = k1_xboole_0
    | ~ l1_struct_0(X2)
    | ~ m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_56])]),
    [final]).

cnf(c_0_67,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),k1_xboole_0) = esk2_0
    | k2_struct_0(esk1_0) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_57]),c_0_58]),c_0_59])]),
    [final]).

cnf(c_0_68,plain,
    ( X1 = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_52]),
    [final]).

cnf(c_0_69,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0) != k1_xboole_0
    | esk2_0 != k2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_50]),
    [final]).

cnf(c_0_70,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_61]),
    [final]).

cnf(c_0_71,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63]),
    [final]).

cnf(c_0_72,plain,
    ( k7_subset_1(X1,k2_struct_0(X2),k5_xboole_0(k2_struct_0(X2),k1_setfam_1(k6_enumset1(k2_struct_0(X2),k2_struct_0(X2),k2_struct_0(X2),k2_struct_0(X2),k2_struct_0(X2),k2_struct_0(X2),k2_struct_0(X2),X3)))) = X3
    | ~ l1_struct_0(X2)
    | ~ m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(X4)) ),
    inference(spm,[status(thm)],[c_0_64,c_0_39]),
    [final]).

cnf(c_0_73,plain,
    ( k5_xboole_0(k2_struct_0(X1),k1_setfam_1(k6_enumset1(k2_struct_0(X1),k2_struct_0(X1),k2_struct_0(X1),k2_struct_0(X1),k2_struct_0(X1),k2_struct_0(X1),k2_struct_0(X1),k7_subset_1(X2,k2_struct_0(X1),X3)))) = X3
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(X4))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_64]),
    [final]).

cnf(c_0_74,plain,
    ( k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k5_xboole_0(k2_struct_0(X1),k1_setfam_1(k6_enumset1(k2_struct_0(X1),k2_struct_0(X1),k2_struct_0(X1),k2_struct_0(X1),k2_struct_0(X1),k2_struct_0(X1),k2_struct_0(X1),X2)))) = X2
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_65,c_0_39]),
    [final]).

cnf(c_0_75,plain,
    ( k5_xboole_0(k2_struct_0(X1),k1_setfam_1(k6_enumset1(k2_struct_0(X1),k2_struct_0(X1),k2_struct_0(X1),k2_struct_0(X1),k2_struct_0(X1),k2_struct_0(X1),k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2)))) = X2
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_39,c_0_54]),
    [final]).

cnf(c_0_76,plain,
    ( k5_xboole_0(k2_struct_0(X1),k1_setfam_1(k6_enumset1(k2_struct_0(X1),k2_struct_0(X1),k2_struct_0(X1),k2_struct_0(X1),k2_struct_0(X1),k2_struct_0(X1),k2_struct_0(X1),k2_struct_0(X1)))) = k1_xboole_0
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_66]),
    [final]).

cnf(c_0_77,plain,
    ( k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k2_struct_0(X1)) = k1_xboole_0
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_55]),c_0_56])]),
    [final]).

cnf(c_0_78,negated_conjecture,
    ( k2_struct_0(esk1_0) = esk2_0
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_67,c_0_55]),
    [final]).

cnf(c_0_79,plain,
    ( X1 = k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_68,c_0_56]),
    [final]).

cnf(c_0_80,negated_conjecture,
    ( k7_subset_1(X1,k2_struct_0(esk1_0),esk2_0) != k1_xboole_0
    | k2_struct_0(esk1_0) != esk2_0
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_69,c_0_46]),
    [final]).

cnf(c_0_81,negated_conjecture,
    ( u1_struct_0(esk1_0) = esk2_0
    | ~ m1_subset_1(u1_struct_0(esk1_0),k1_zfmisc_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_68,c_0_59]),
    [final]).

cnf(c_0_82,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_70,c_0_56]),
    [final]).

cnf(c_0_83,negated_conjecture,
    ( m1_subset_1(X1,u1_struct_0(esk1_0))
    | ~ r2_hidden(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_70,c_0_59]),
    [final]).

cnf(c_0_84,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_70,c_0_71]),
    [final]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:31:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.13/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.028 s
% 0.13/0.38  # Presaturation interreduction done
% 0.13/0.38  
% 0.13/0.38  # No proof found!
% 0.13/0.38  # SZS status CounterSatisfiable
% 0.13/0.38  # SZS output start Saturation
% 0.13/0.38  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.13/0.38  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.13/0.38  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.13/0.38  fof(redefinition_k7_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k7_subset_1(X1,X2,X3)=k4_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 0.13/0.38  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.13/0.38  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.13/0.38  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 0.13/0.38  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 0.13/0.38  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 0.13/0.38  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 0.13/0.38  fof(t22_pre_topc, axiom, ![X1]:(l1_struct_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2))=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_pre_topc)).
% 0.13/0.38  fof(t5_boole, axiom, ![X1]:k5_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 0.13/0.38  fof(t23_pre_topc, conjecture, ![X1]:(l1_struct_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(~((X2!=k2_struct_0(X1)&k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2)=k1_xboole_0))&~((k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2)!=k1_xboole_0&X2=k2_struct_0(X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_pre_topc)).
% 0.13/0.38  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.13/0.38  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.13/0.38  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 0.13/0.38  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 0.13/0.38  fof(c_0_17, plain, ![X45, X46]:k1_setfam_1(k2_tarski(X45,X46))=k3_xboole_0(X45,X46), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.13/0.38  fof(c_0_18, plain, ![X14, X15]:k1_enumset1(X14,X14,X15)=k2_tarski(X14,X15), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.13/0.38  fof(c_0_19, plain, ![X10, X11]:k4_xboole_0(X10,X11)=k5_xboole_0(X10,k3_xboole_0(X10,X11)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.13/0.38  cnf(c_0_20, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.38  cnf(c_0_21, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.38  fof(c_0_22, plain, ![X41, X42, X43]:(~m1_subset_1(X42,k1_zfmisc_1(X41))|k7_subset_1(X41,X42,X43)=k4_xboole_0(X42,X43)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).
% 0.13/0.38  cnf(c_0_23, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.38  cnf(c_0_24, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_20, c_0_21])).
% 0.13/0.38  fof(c_0_25, plain, ![X16, X17, X18]:k2_enumset1(X16,X16,X17,X18)=k1_enumset1(X16,X17,X18), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.13/0.38  fof(c_0_26, plain, ![X19, X20, X21, X22]:k3_enumset1(X19,X19,X20,X21,X22)=k2_enumset1(X19,X20,X21,X22), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.13/0.38  fof(c_0_27, plain, ![X23, X24, X25, X26, X27]:k4_enumset1(X23,X23,X24,X25,X26,X27)=k3_enumset1(X23,X24,X25,X26,X27), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.13/0.38  fof(c_0_28, plain, ![X28, X29, X30, X31, X32, X33]:k5_enumset1(X28,X28,X29,X30,X31,X32,X33)=k4_enumset1(X28,X29,X30,X31,X32,X33), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.13/0.38  fof(c_0_29, plain, ![X34, X35, X36, X37, X38, X39, X40]:k6_enumset1(X34,X34,X35,X36,X37,X38,X39,X40)=k5_enumset1(X34,X35,X36,X37,X38,X39,X40), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.13/0.38  cnf(c_0_30, plain, (k7_subset_1(X2,X1,X3)=k4_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.38  cnf(c_0_31, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2)))), inference(rw,[status(thm)],[c_0_23, c_0_24])).
% 0.13/0.38  cnf(c_0_32, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.13/0.38  cnf(c_0_33, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.13/0.38  cnf(c_0_34, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.13/0.38  cnf(c_0_35, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.13/0.38  cnf(c_0_36, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.13/0.38  fof(c_0_37, plain, ![X12]:k3_xboole_0(X12,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 0.13/0.38  fof(c_0_38, plain, ![X52, X53]:(~l1_struct_0(X52)|(~m1_subset_1(X53,k1_zfmisc_1(u1_struct_0(X52)))|k7_subset_1(u1_struct_0(X52),k2_struct_0(X52),k7_subset_1(u1_struct_0(X52),k2_struct_0(X52),X53))=X53)), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t22_pre_topc])])])).
% 0.13/0.38  cnf(c_0_39, plain, (k7_subset_1(X2,X1,X3)=k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X3)))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_31]), c_0_32]), c_0_33]), c_0_34]), c_0_35]), c_0_36]), ['final']).
% 0.13/0.38  cnf(c_0_40, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.13/0.38  fof(c_0_41, plain, ![X13]:k5_xboole_0(X13,k1_xboole_0)=X13, inference(variable_rename,[status(thm)],[t5_boole])).
% 0.13/0.38  fof(c_0_42, negated_conjecture, ~(![X1]:(l1_struct_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(~((X2!=k2_struct_0(X1)&k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2)=k1_xboole_0))&~((k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2)!=k1_xboole_0&X2=k2_struct_0(X1))))))), inference(assume_negation,[status(cth)],[t23_pre_topc])).
% 0.13/0.38  fof(c_0_43, plain, ![X8, X9]:(((r1_tarski(X8,X9)|X8!=X9)&(r1_tarski(X9,X8)|X8!=X9))&(~r1_tarski(X8,X9)|~r1_tarski(X9,X8)|X8=X9)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.13/0.38  fof(c_0_44, plain, ![X47, X48]:((~m1_subset_1(X47,k1_zfmisc_1(X48))|r1_tarski(X47,X48))&(~r1_tarski(X47,X48)|m1_subset_1(X47,k1_zfmisc_1(X48)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.13/0.38  cnf(c_0_45, plain, (k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2))=X2|~l1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_38]), ['final']).
% 0.13/0.38  cnf(c_0_46, plain, (k7_subset_1(X1,X2,X3)=k7_subset_1(X4,X2,X3)|~m1_subset_1(X2,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X4))), inference(spm,[status(thm)],[c_0_39, c_0_39]), ['final']).
% 0.13/0.38  cnf(c_0_47, plain, (k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k1_xboole_0))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_24]), c_0_32]), c_0_33]), c_0_34]), c_0_35]), c_0_36]), ['final']).
% 0.13/0.38  cnf(c_0_48, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_41]), ['final']).
% 0.13/0.38  fof(c_0_49, plain, ![X44]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X44)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.13/0.38  fof(c_0_50, negated_conjecture, (l1_struct_0(esk1_0)&(m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&(((k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)!=k1_xboole_0|esk2_0!=k2_struct_0(esk1_0))&(esk2_0=k2_struct_0(esk1_0)|esk2_0!=k2_struct_0(esk1_0)))&((k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)!=k1_xboole_0|k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)=k1_xboole_0)&(esk2_0=k2_struct_0(esk1_0)|k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)=k1_xboole_0))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_42])])])])).
% 0.13/0.38  cnf(c_0_51, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_43]), ['final']).
% 0.13/0.38  cnf(c_0_52, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_44]), ['final']).
% 0.13/0.38  cnf(c_0_53, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.13/0.38  cnf(c_0_54, plain, (k7_subset_1(X1,k2_struct_0(X2),k7_subset_1(u1_struct_0(X2),k2_struct_0(X2),X3))=X3|~l1_struct_0(X2)|~m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_45, c_0_46]), ['final']).
% 0.13/0.38  cnf(c_0_55, plain, (k7_subset_1(X1,X2,k1_xboole_0)=X2|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_47]), c_0_48]), ['final']).
% 0.13/0.38  cnf(c_0_56, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_49]), ['final']).
% 0.13/0.38  cnf(c_0_57, negated_conjecture, (esk2_0=k2_struct_0(esk1_0)|k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_50]), ['final']).
% 0.13/0.38  cnf(c_0_58, negated_conjecture, (l1_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_50]), ['final']).
% 0.13/0.38  cnf(c_0_59, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_50]), ['final']).
% 0.13/0.38  cnf(c_0_60, plain, (X1=X2|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_51, c_0_52]), ['final']).
% 0.13/0.38  fof(c_0_61, plain, ![X49, X50, X51]:(~r2_hidden(X49,X50)|~m1_subset_1(X50,k1_zfmisc_1(X51))|m1_subset_1(X49,X51)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.13/0.38  cnf(c_0_62, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_44]), ['final']).
% 0.13/0.38  cnf(c_0_63, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_53]), ['final']).
% 0.13/0.38  cnf(c_0_64, plain, (k7_subset_1(X1,k2_struct_0(X2),k7_subset_1(X3,k2_struct_0(X2),X4))=X4|~l1_struct_0(X2)|~m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(X1))|~m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(X3))), inference(spm,[status(thm)],[c_0_54, c_0_46]), ['final']).
% 0.13/0.38  cnf(c_0_65, plain, (k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(X2,k2_struct_0(X1),X3))=X3|~l1_struct_0(X1)|~m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_45, c_0_46]), ['final']).
% 0.13/0.38  cnf(c_0_66, plain, (k7_subset_1(X1,k2_struct_0(X2),k2_struct_0(X2))=k1_xboole_0|~l1_struct_0(X2)|~m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_56])]), ['final']).
% 0.13/0.38  cnf(c_0_67, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),k1_xboole_0)=esk2_0|k2_struct_0(esk1_0)=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_57]), c_0_58]), c_0_59])]), ['final']).
% 0.13/0.38  cnf(c_0_68, plain, (X1=X2|~m1_subset_1(X2,k1_zfmisc_1(X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_60, c_0_52]), ['final']).
% 0.13/0.38  cnf(c_0_69, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)!=k1_xboole_0|esk2_0!=k2_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_50]), ['final']).
% 0.13/0.38  cnf(c_0_70, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_61]), ['final']).
% 0.13/0.38  cnf(c_0_71, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_62, c_0_63]), ['final']).
% 0.13/0.38  cnf(c_0_72, plain, (k7_subset_1(X1,k2_struct_0(X2),k5_xboole_0(k2_struct_0(X2),k1_setfam_1(k6_enumset1(k2_struct_0(X2),k2_struct_0(X2),k2_struct_0(X2),k2_struct_0(X2),k2_struct_0(X2),k2_struct_0(X2),k2_struct_0(X2),X3))))=X3|~l1_struct_0(X2)|~m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(X1))|~m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(X4))), inference(spm,[status(thm)],[c_0_64, c_0_39]), ['final']).
% 0.13/0.38  cnf(c_0_73, plain, (k5_xboole_0(k2_struct_0(X1),k1_setfam_1(k6_enumset1(k2_struct_0(X1),k2_struct_0(X1),k2_struct_0(X1),k2_struct_0(X1),k2_struct_0(X1),k2_struct_0(X1),k2_struct_0(X1),k7_subset_1(X2,k2_struct_0(X1),X3))))=X3|~l1_struct_0(X1)|~m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(X4))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_39, c_0_64]), ['final']).
% 0.13/0.38  cnf(c_0_74, plain, (k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k5_xboole_0(k2_struct_0(X1),k1_setfam_1(k6_enumset1(k2_struct_0(X1),k2_struct_0(X1),k2_struct_0(X1),k2_struct_0(X1),k2_struct_0(X1),k2_struct_0(X1),k2_struct_0(X1),X2))))=X2|~l1_struct_0(X1)|~m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(X3))), inference(spm,[status(thm)],[c_0_65, c_0_39]), ['final']).
% 0.13/0.38  cnf(c_0_75, plain, (k5_xboole_0(k2_struct_0(X1),k1_setfam_1(k6_enumset1(k2_struct_0(X1),k2_struct_0(X1),k2_struct_0(X1),k2_struct_0(X1),k2_struct_0(X1),k2_struct_0(X1),k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2))))=X2|~l1_struct_0(X1)|~m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(X3))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_39, c_0_54]), ['final']).
% 0.13/0.38  cnf(c_0_76, plain, (k5_xboole_0(k2_struct_0(X1),k1_setfam_1(k6_enumset1(k2_struct_0(X1),k2_struct_0(X1),k2_struct_0(X1),k2_struct_0(X1),k2_struct_0(X1),k2_struct_0(X1),k2_struct_0(X1),k2_struct_0(X1))))=k1_xboole_0|~l1_struct_0(X1)|~m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_39, c_0_66]), ['final']).
% 0.13/0.38  cnf(c_0_77, plain, (k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k2_struct_0(X1))=k1_xboole_0|~l1_struct_0(X1)|~m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_55]), c_0_56])]), ['final']).
% 0.13/0.38  cnf(c_0_78, negated_conjecture, (k2_struct_0(esk1_0)=esk2_0|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_67, c_0_55]), ['final']).
% 0.13/0.38  cnf(c_0_79, plain, (X1=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_68, c_0_56]), ['final']).
% 0.13/0.38  cnf(c_0_80, negated_conjecture, (k7_subset_1(X1,k2_struct_0(esk1_0),esk2_0)!=k1_xboole_0|k2_struct_0(esk1_0)!=esk2_0|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_69, c_0_46]), ['final']).
% 0.13/0.38  cnf(c_0_81, negated_conjecture, (u1_struct_0(esk1_0)=esk2_0|~m1_subset_1(u1_struct_0(esk1_0),k1_zfmisc_1(esk2_0))), inference(spm,[status(thm)],[c_0_68, c_0_59]), ['final']).
% 0.13/0.38  cnf(c_0_82, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_70, c_0_56]), ['final']).
% 0.13/0.38  cnf(c_0_83, negated_conjecture, (m1_subset_1(X1,u1_struct_0(esk1_0))|~r2_hidden(X1,esk2_0)), inference(spm,[status(thm)],[c_0_70, c_0_59]), ['final']).
% 0.13/0.38  cnf(c_0_84, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_70, c_0_71]), ['final']).
% 0.13/0.38  # SZS output end Saturation
% 0.13/0.38  # Proof object total steps             : 85
% 0.13/0.38  # Proof object clause steps            : 50
% 0.13/0.38  # Proof object formula steps           : 35
% 0.13/0.38  # Proof object conjectures             : 12
% 0.13/0.38  # Proof object clause conjectures      : 9
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 22
% 0.13/0.38  # Proof object initial formulas used   : 17
% 0.13/0.38  # Proof object generating inferences   : 23
% 0.13/0.38  # Proof object simplifying inferences  : 23
% 0.13/0.38  # Parsed axioms                        : 17
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 25
% 0.13/0.38  # Removed in clause preprocessing      : 10
% 0.13/0.38  # Initial clauses in saturation        : 15
% 0.13/0.38  # Processed clauses                    : 112
% 0.13/0.38  # ...of these trivial                  : 0
% 0.13/0.38  # ...subsumed                          : 59
% 0.13/0.38  # ...remaining for further processing  : 53
% 0.13/0.38  # Other redundant clauses eliminated   : 2
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 0
% 0.13/0.38  # Backward-rewritten                   : 0
% 0.13/0.38  # Generated clauses                    : 87
% 0.13/0.38  # ...of the previous two non-trivial   : 83
% 0.13/0.38  # Contextual simplify-reflections      : 0
% 0.13/0.38  # Paramodulations                      : 85
% 0.13/0.38  # Factorizations                       : 0
% 0.13/0.38  # Equation resolutions                 : 2
% 0.13/0.38  # Propositional unsat checks           : 0
% 0.13/0.38  #    Propositional check models        : 0
% 0.13/0.38  #    Propositional check unsatisfiable : 0
% 0.13/0.38  #    Propositional clauses             : 0
% 0.13/0.38  #    Propositional clauses after purity: 0
% 0.13/0.38  #    Propositional unsat core size     : 0
% 0.13/0.38  #    Propositional preprocessing time  : 0.000
% 0.13/0.38  #    Propositional encoding time       : 0.000
% 0.13/0.38  #    Propositional solver time         : 0.000
% 0.13/0.38  #    Success case prop preproc time    : 0.000
% 0.13/0.38  #    Success case prop encoding time   : 0.000
% 0.13/0.38  #    Success case prop solver time     : 0.000
% 0.13/0.38  # Current number of processed clauses  : 37
% 0.13/0.38  #    Positive orientable unit clauses  : 7
% 0.13/0.38  #    Positive unorientable unit clauses: 0
% 0.13/0.38  #    Negative unit clauses             : 0
% 0.13/0.38  #    Non-unit-clauses                  : 30
% 0.13/0.38  # Current number of unprocessed clauses: 0
% 0.13/0.38  # ...number of literals in the above   : 0
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 22
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 444
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 203
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 59
% 0.13/0.38  # Unit Clause-clause subsumption calls : 4
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 3
% 0.13/0.38  # BW rewrite match successes           : 0
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 3941
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.034 s
% 0.13/0.38  # System time              : 0.003 s
% 0.13/0.38  # Total time               : 0.037 s
% 0.13/0.38  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
