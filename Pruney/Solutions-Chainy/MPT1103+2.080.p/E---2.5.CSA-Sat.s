%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:08:45 EST 2020

% Result     : CounterSatisfiable 0.19s
% Output     : Saturation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  127 (1594 expanded)
%              Number of clauses        :   80 ( 682 expanded)
%              Number of leaves         :   23 ( 446 expanded)
%              Depth                    :   11
%              Number of atoms          :  187 (2290 expanded)
%              Number of equality atoms :  124 (1609 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :   10 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(redefinition_k7_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k7_subset_1(X1,X2,X3) = k4_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(t75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(dt_k2_subset_1,axiom,(
    ! [X1] : m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

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

fof(redefinition_k4_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => k4_subset_1(X1,X2,X3) = k2_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(t33_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => k3_subset_1(X1,k7_subset_1(X1,X2,X3)) = k4_subset_1(X1,k3_subset_1(X1,X2),X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_subset_1)).

fof(t22_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = k3_subset_1(X1,k1_subset_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).

fof(d3_subset_1,axiom,(
    ! [X1] : k1_subset_1(X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

fof(t92_xboole_1,axiom,(
    ! [X1] : k5_xboole_0(X1,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(involutiveness_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,k3_subset_1(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(c_0_23,plain,(
    ! [X58,X59] : k1_setfam_1(k2_tarski(X58,X59)) = k3_xboole_0(X58,X59) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_24,plain,(
    ! [X15,X16] : k1_enumset1(X15,X15,X16) = k2_tarski(X15,X16) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_25,plain,(
    ! [X9,X10] : k4_xboole_0(X9,X10) = k5_xboole_0(X9,k3_xboole_0(X9,X10)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_26,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_27,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_28,plain,(
    ! [X50,X51,X52] :
      ( ~ m1_subset_1(X51,k1_zfmisc_1(X50))
      | k7_subset_1(X50,X51,X52) = k4_xboole_0(X51,X52) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).

cnf(c_0_29,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_30,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_26,c_0_27])).

fof(c_0_31,plain,(
    ! [X17,X18,X19] : k2_enumset1(X17,X17,X18,X19) = k1_enumset1(X17,X18,X19) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_32,plain,(
    ! [X20,X21,X22,X23] : k3_enumset1(X20,X20,X21,X22,X23) = k2_enumset1(X20,X21,X22,X23) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_33,plain,(
    ! [X24,X25,X26,X27,X28] : k4_enumset1(X24,X24,X25,X26,X27,X28) = k3_enumset1(X24,X25,X26,X27,X28) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_34,plain,(
    ! [X29,X30,X31,X32,X33,X34] : k5_enumset1(X29,X29,X30,X31,X32,X33,X34) = k4_enumset1(X29,X30,X31,X32,X33,X34) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_35,plain,(
    ! [X35,X36,X37,X38,X39,X40,X41] : k6_enumset1(X35,X35,X36,X37,X38,X39,X40,X41) = k5_enumset1(X35,X36,X37,X38,X39,X40,X41) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_36,plain,(
    ! [X44] : m1_subset_1(k2_subset_1(X44),k1_zfmisc_1(X44)) ),
    inference(variable_rename,[status(thm)],[dt_k2_subset_1])).

fof(c_0_37,plain,(
    ! [X43] : k2_subset_1(X43) = X43 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

cnf(c_0_38,plain,
    ( k7_subset_1(X2,X1,X3) = k4_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_39,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2))) ),
    inference(rw,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_40,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_41,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_42,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_43,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_44,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_45,plain,
    ( m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_46,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

fof(c_0_47,negated_conjecture,(
    ~ ! [X1] :
        ( l1_struct_0(X1)
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( ~ ( X2 != k2_struct_0(X1)
                  & k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2) = k1_xboole_0 )
              & ~ ( k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2) != k1_xboole_0
                  & X2 = k2_struct_0(X1) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t23_pre_topc])).

fof(c_0_48,plain,(
    ! [X47,X48,X49] :
      ( ~ m1_subset_1(X48,k1_zfmisc_1(X47))
      | ~ m1_subset_1(X49,k1_zfmisc_1(X47))
      | k4_subset_1(X47,X48,X49) = k2_xboole_0(X48,X49) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).

fof(c_0_49,plain,(
    ! [X57] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X57)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

fof(c_0_50,plain,(
    ! [X8] : k3_xboole_0(X8,X8) = X8 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

cnf(c_0_51,plain,
    ( k7_subset_1(X2,X1,X3) = k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_39]),c_0_40]),c_0_41]),c_0_42]),c_0_43]),c_0_44])).

cnf(c_0_52,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_45,c_0_46]),
    [final]).

fof(c_0_53,negated_conjecture,
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
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_47])])])])).

fof(c_0_54,plain,(
    ! [X54,X55,X56] :
      ( ~ m1_subset_1(X55,k1_zfmisc_1(X54))
      | ~ m1_subset_1(X56,k1_zfmisc_1(X54))
      | k3_subset_1(X54,k7_subset_1(X54,X55,X56)) = k4_subset_1(X54,k3_subset_1(X54,X55),X56) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t33_subset_1])])])).

fof(c_0_55,plain,(
    ! [X53] : k2_subset_1(X53) = k3_subset_1(X53,k1_subset_1(X53)) ),
    inference(variable_rename,[status(thm)],[t22_subset_1])).

fof(c_0_56,plain,(
    ! [X42] : k1_subset_1(X42) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[d3_subset_1])).

cnf(c_0_57,plain,
    ( k4_subset_1(X2,X1,X3) = k2_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_48]),
    [final]).

cnf(c_0_58,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_49]),
    [final]).

cnf(c_0_59,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

fof(c_0_60,plain,(
    ! [X14] : k5_xboole_0(X14,X14) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t92_xboole_1])).

cnf(c_0_61,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) = k7_subset_1(X1,X1,X2) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52]),
    [final]).

cnf(c_0_62,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_53]),
    [final]).

cnf(c_0_63,plain,
    ( k3_subset_1(X2,k7_subset_1(X2,X1,X3)) = k4_subset_1(X2,k3_subset_1(X2,X1),X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_54]),
    [final]).

cnf(c_0_64,plain,
    ( k2_subset_1(X1) = k3_subset_1(X1,k1_subset_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_65,plain,
    ( k1_subset_1(X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_66,plain,
    ( k4_subset_1(X1,X2,k1_xboole_0) = k2_xboole_0(X2,k1_xboole_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_67,plain,
    ( k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59,c_0_30]),c_0_40]),c_0_41]),c_0_42]),c_0_43]),c_0_44]),
    [final]).

cnf(c_0_68,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_60]),
    [final]).

cnf(c_0_69,plain,
    ( k7_subset_1(X1,X2,X3) = k7_subset_1(X2,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_51,c_0_61]),
    [final]).

cnf(c_0_70,plain,
    ( k4_subset_1(X1,X2,X1) = k2_xboole_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_57,c_0_52]),
    [final]).

cnf(c_0_71,negated_conjecture,
    ( k4_subset_1(u1_struct_0(esk1_0),X1,esk2_0) = k2_xboole_0(X1,esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_57,c_0_62]),
    [final]).

fof(c_0_72,plain,(
    ! [X11,X12] :
      ( ~ r1_tarski(X11,X12)
      | k2_xboole_0(X11,X12) = X12 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

fof(c_0_73,plain,(
    ! [X13] : r1_tarski(k1_xboole_0,X13) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_74,plain,
    ( k4_subset_1(X1,k3_subset_1(X1,X2),k1_xboole_0) = k3_subset_1(X1,k7_subset_1(X1,X2,k1_xboole_0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_63,c_0_58]),
    [final]).

cnf(c_0_75,plain,
    ( X1 = k3_subset_1(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_64,c_0_46]),c_0_65]),
    [final]).

cnf(c_0_76,plain,
    ( k4_subset_1(X1,X1,k1_xboole_0) = k2_xboole_0(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_66,c_0_52])).

cnf(c_0_77,plain,
    ( k7_subset_1(X1,X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_67]),c_0_68]),
    [final]).

cnf(c_0_78,plain,
    ( k7_subset_1(X1,k1_xboole_0,X2) = k7_subset_1(k1_xboole_0,k1_xboole_0,X2) ),
    inference(spm,[status(thm)],[c_0_69,c_0_58])).

cnf(c_0_79,plain,
    ( k4_subset_1(X1,k3_subset_1(X1,X2),X1) = k3_subset_1(X1,k7_subset_1(X1,X2,X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_63,c_0_52]),
    [final]).

cnf(c_0_80,plain,
    ( k4_subset_1(X1,X1,X1) = k2_xboole_0(X1,X1) ),
    inference(spm,[status(thm)],[c_0_70,c_0_52]),
    [final]).

cnf(c_0_81,negated_conjecture,
    ( k4_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),X1),esk2_0) = k3_subset_1(u1_struct_0(esk1_0),k7_subset_1(u1_struct_0(esk1_0),X1,esk2_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_63,c_0_62]),
    [final]).

cnf(c_0_82,negated_conjecture,
    ( k4_subset_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0),esk2_0) = k2_xboole_0(u1_struct_0(esk1_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_71,c_0_52]),
    [final]).

fof(c_0_83,plain,(
    ! [X45,X46] :
      ( ~ m1_subset_1(X46,k1_zfmisc_1(X45))
      | k3_subset_1(X45,k3_subset_1(X45,X46)) = X46 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).

cnf(c_0_84,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_72]),
    [final]).

cnf(c_0_85,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_73]),
    [final]).

cnf(c_0_86,plain,
    ( k3_subset_1(X1,k7_subset_1(X1,k1_xboole_0,k1_xboole_0)) = k2_xboole_0(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_58]),c_0_75]),c_0_76])).

cnf(c_0_87,plain,
    ( k7_subset_1(X1,k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_77,c_0_78]),
    [final]).

fof(c_0_88,plain,(
    ! [X60,X61,X62] :
      ( ~ r2_hidden(X60,X61)
      | ~ m1_subset_1(X61,k1_zfmisc_1(X62))
      | m1_subset_1(X60,X62) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_89,plain,
    ( k3_subset_1(X1,k7_subset_1(X1,k1_xboole_0,X1)) = k2_xboole_0(X1,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_58]),c_0_75]),c_0_80])).

cnf(c_0_90,negated_conjecture,
    ( k3_subset_1(u1_struct_0(esk1_0),k7_subset_1(u1_struct_0(esk1_0),k1_xboole_0,esk2_0)) = k2_xboole_0(u1_struct_0(esk1_0),esk2_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_58]),c_0_75]),c_0_82])).

cnf(c_0_91,negated_conjecture,
    ( k5_xboole_0(esk2_0,k1_setfam_1(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,X1))) = k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_51,c_0_62])).

cnf(c_0_92,plain,
    ( k3_subset_1(X2,k3_subset_1(X2,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_83]),
    [final]).

cnf(c_0_93,plain,
    ( k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_84,c_0_85]),
    [final]).

cnf(c_0_94,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_86,c_0_87]),c_0_75]),
    [final]).

cnf(c_0_95,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_88]),
    [final]).

cnf(c_0_96,plain,
    ( k3_subset_1(X1,k7_subset_1(k1_xboole_0,k1_xboole_0,X1)) = k2_xboole_0(X1,X1) ),
    inference(spm,[status(thm)],[c_0_89,c_0_78])).

cnf(c_0_97,negated_conjecture,
    ( k3_subset_1(u1_struct_0(esk1_0),k7_subset_1(k1_xboole_0,k1_xboole_0,esk2_0)) = k2_xboole_0(u1_struct_0(esk1_0),esk2_0) ),
    inference(rw,[status(thm)],[c_0_90,c_0_78])).

cnf(c_0_98,negated_conjecture,
    ( k4_subset_1(u1_struct_0(esk1_0),esk2_0,k1_xboole_0) = k2_xboole_0(esk2_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_66,c_0_62])).

cnf(c_0_99,negated_conjecture,
    ( k4_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0),u1_struct_0(esk1_0)) = k3_subset_1(u1_struct_0(esk1_0),k7_subset_1(u1_struct_0(esk1_0),esk2_0,u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_79,c_0_62])).

cnf(c_0_100,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1) = k7_subset_1(esk2_0,esk2_0,X1) ),
    inference(rw,[status(thm)],[c_0_91,c_0_61]),
    [final]).

cnf(c_0_101,negated_conjecture,
    ( k4_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0),esk2_0) = k3_subset_1(u1_struct_0(esk1_0),k7_subset_1(u1_struct_0(esk1_0),esk2_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_81,c_0_62])).

cnf(c_0_102,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),esk2_0,esk2_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_67]),c_0_68])).

cnf(c_0_103,plain,
    ( k3_subset_1(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_58]),c_0_75]),
    [final]).

cnf(c_0_104,plain,
    ( k4_subset_1(X1,k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_58]),c_0_93]),
    [final]).

cnf(c_0_105,negated_conjecture,
    ( k4_subset_1(u1_struct_0(esk1_0),k1_xboole_0,esk2_0) = esk2_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_58]),c_0_93]),
    [final]).

cnf(c_0_106,plain,
    ( k4_subset_1(X1,X2,k1_xboole_0) = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_66,c_0_94]),
    [final]).

cnf(c_0_107,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_95,c_0_52]),
    [final]).

cnf(c_0_108,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_95,c_0_58]),
    [final]).

cnf(c_0_109,negated_conjecture,
    ( m1_subset_1(X1,u1_struct_0(esk1_0))
    | ~ r2_hidden(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_95,c_0_62]),
    [final]).

cnf(c_0_110,negated_conjecture,
    ( esk2_0 = k2_struct_0(esk1_0)
    | k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_53]),
    [final]).

cnf(c_0_111,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0) != k1_xboole_0
    | esk2_0 != k2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_53]),
    [final]).

cnf(c_0_112,plain,
    ( k7_subset_1(X1,k1_xboole_0,X2) = k7_subset_1(X3,k1_xboole_0,X2) ),
    inference(spm,[status(thm)],[c_0_78,c_0_78]),
    [final]).

cnf(c_0_113,plain,
    ( k3_subset_1(X1,k7_subset_1(X2,k1_xboole_0,X1)) = k2_xboole_0(X1,X1) ),
    inference(spm,[status(thm)],[c_0_96,c_0_78]),
    [final]).

cnf(c_0_114,negated_conjecture,
    ( k3_subset_1(u1_struct_0(esk1_0),k7_subset_1(X1,k1_xboole_0,esk2_0)) = k2_xboole_0(u1_struct_0(esk1_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_97,c_0_78]),
    [final]).

cnf(c_0_115,negated_conjecture,
    ( k4_subset_1(u1_struct_0(esk1_0),esk2_0,k1_xboole_0) = esk2_0 ),
    inference(rw,[status(thm)],[c_0_98,c_0_94]),
    [final]).

cnf(c_0_116,plain,
    ( k4_subset_1(X1,X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[c_0_76,c_0_94]),
    [final]).

cnf(c_0_117,negated_conjecture,
    ( k4_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0),u1_struct_0(esk1_0)) = k3_subset_1(u1_struct_0(esk1_0),k7_subset_1(esk2_0,esk2_0,u1_struct_0(esk1_0))) ),
    inference(rw,[status(thm)],[c_0_99,c_0_100]),
    [final]).

cnf(c_0_118,negated_conjecture,
    ( k4_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0),k1_xboole_0) = k3_subset_1(u1_struct_0(esk1_0),k7_subset_1(esk2_0,esk2_0,k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_62]),c_0_100]),
    [final]).

cnf(c_0_119,negated_conjecture,
    ( k4_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0),esk2_0) = u1_struct_0(esk1_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_101,c_0_102]),c_0_75]),
    [final]).

cnf(c_0_120,plain,
    ( k3_subset_1(X1,k7_subset_1(X1,X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_52]),c_0_103]),c_0_104]),
    [final]).

cnf(c_0_121,negated_conjecture,
    ( k3_subset_1(u1_struct_0(esk1_0),k7_subset_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0),esk2_0)) = esk2_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_52]),c_0_103]),c_0_105]),
    [final]).

cnf(c_0_122,negated_conjecture,
    ( k4_subset_1(u1_struct_0(esk1_0),esk2_0,u1_struct_0(esk1_0)) = k2_xboole_0(esk2_0,u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_70,c_0_62]),
    [final]).

cnf(c_0_123,negated_conjecture,
    ( k4_subset_1(u1_struct_0(esk1_0),esk2_0,esk2_0) = k2_xboole_0(esk2_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_71,c_0_62]),
    [final]).

cnf(c_0_124,plain,
    ( k4_subset_1(X1,k1_xboole_0,X1) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_58]),c_0_93]),
    [final]).

cnf(c_0_125,negated_conjecture,
    ( k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)) = esk2_0 ),
    inference(spm,[status(thm)],[c_0_92,c_0_62]),
    [final]).

cnf(c_0_126,negated_conjecture,
    ( l1_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_53]),
    [final]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:13:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_S2mI
% 0.19/0.37  # and selection function SelectCQArNTNpEqFirst.
% 0.19/0.37  #
% 0.19/0.37  # Preprocessing time       : 0.028 s
% 0.19/0.37  # Presaturation interreduction done
% 0.19/0.37  
% 0.19/0.37  # No proof found!
% 0.19/0.37  # SZS status CounterSatisfiable
% 0.19/0.37  # SZS output start Saturation
% 0.19/0.37  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.19/0.37  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.19/0.37  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.19/0.37  fof(redefinition_k7_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k7_subset_1(X1,X2,X3)=k4_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 0.19/0.37  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.19/0.37  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.19/0.37  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 0.19/0.37  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 0.19/0.37  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 0.19/0.37  fof(dt_k2_subset_1, axiom, ![X1]:m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 0.19/0.37  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 0.19/0.37  fof(t23_pre_topc, conjecture, ![X1]:(l1_struct_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(~((X2!=k2_struct_0(X1)&k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2)=k1_xboole_0))&~((k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2)!=k1_xboole_0&X2=k2_struct_0(X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_pre_topc)).
% 0.19/0.37  fof(redefinition_k4_subset_1, axiom, ![X1, X2, X3]:((m1_subset_1(X2,k1_zfmisc_1(X1))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>k4_subset_1(X1,X2,X3)=k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 0.19/0.37  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 0.19/0.37  fof(idempotence_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 0.19/0.37  fof(t33_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k3_subset_1(X1,k7_subset_1(X1,X2,X3))=k4_subset_1(X1,k3_subset_1(X1,X2),X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_subset_1)).
% 0.19/0.37  fof(t22_subset_1, axiom, ![X1]:k2_subset_1(X1)=k3_subset_1(X1,k1_subset_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_subset_1)).
% 0.19/0.37  fof(d3_subset_1, axiom, ![X1]:k1_subset_1(X1)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 0.19/0.37  fof(t92_xboole_1, axiom, ![X1]:k5_xboole_0(X1,X1)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 0.19/0.37  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.19/0.37  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.19/0.37  fof(involutiveness_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,k3_subset_1(X1,X2))=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 0.19/0.37  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 0.19/0.37  fof(c_0_23, plain, ![X58, X59]:k1_setfam_1(k2_tarski(X58,X59))=k3_xboole_0(X58,X59), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.19/0.37  fof(c_0_24, plain, ![X15, X16]:k1_enumset1(X15,X15,X16)=k2_tarski(X15,X16), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.19/0.37  fof(c_0_25, plain, ![X9, X10]:k4_xboole_0(X9,X10)=k5_xboole_0(X9,k3_xboole_0(X9,X10)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.19/0.37  cnf(c_0_26, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.37  cnf(c_0_27, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.37  fof(c_0_28, plain, ![X50, X51, X52]:(~m1_subset_1(X51,k1_zfmisc_1(X50))|k7_subset_1(X50,X51,X52)=k4_xboole_0(X51,X52)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).
% 0.19/0.37  cnf(c_0_29, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.37  cnf(c_0_30, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_26, c_0_27])).
% 0.19/0.37  fof(c_0_31, plain, ![X17, X18, X19]:k2_enumset1(X17,X17,X18,X19)=k1_enumset1(X17,X18,X19), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.19/0.37  fof(c_0_32, plain, ![X20, X21, X22, X23]:k3_enumset1(X20,X20,X21,X22,X23)=k2_enumset1(X20,X21,X22,X23), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.19/0.37  fof(c_0_33, plain, ![X24, X25, X26, X27, X28]:k4_enumset1(X24,X24,X25,X26,X27,X28)=k3_enumset1(X24,X25,X26,X27,X28), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.19/0.37  fof(c_0_34, plain, ![X29, X30, X31, X32, X33, X34]:k5_enumset1(X29,X29,X30,X31,X32,X33,X34)=k4_enumset1(X29,X30,X31,X32,X33,X34), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.19/0.37  fof(c_0_35, plain, ![X35, X36, X37, X38, X39, X40, X41]:k6_enumset1(X35,X35,X36,X37,X38,X39,X40,X41)=k5_enumset1(X35,X36,X37,X38,X39,X40,X41), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.19/0.37  fof(c_0_36, plain, ![X44]:m1_subset_1(k2_subset_1(X44),k1_zfmisc_1(X44)), inference(variable_rename,[status(thm)],[dt_k2_subset_1])).
% 0.19/0.37  fof(c_0_37, plain, ![X43]:k2_subset_1(X43)=X43, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 0.19/0.37  cnf(c_0_38, plain, (k7_subset_1(X2,X1,X3)=k4_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.37  cnf(c_0_39, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2)))), inference(rw,[status(thm)],[c_0_29, c_0_30])).
% 0.19/0.37  cnf(c_0_40, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.37  cnf(c_0_41, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.37  cnf(c_0_42, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.37  cnf(c_0_43, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.19/0.37  cnf(c_0_44, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.19/0.37  cnf(c_0_45, plain, (m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.19/0.37  cnf(c_0_46, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.19/0.37  fof(c_0_47, negated_conjecture, ~(![X1]:(l1_struct_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(~((X2!=k2_struct_0(X1)&k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2)=k1_xboole_0))&~((k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2)!=k1_xboole_0&X2=k2_struct_0(X1))))))), inference(assume_negation,[status(cth)],[t23_pre_topc])).
% 0.19/0.37  fof(c_0_48, plain, ![X47, X48, X49]:(~m1_subset_1(X48,k1_zfmisc_1(X47))|~m1_subset_1(X49,k1_zfmisc_1(X47))|k4_subset_1(X47,X48,X49)=k2_xboole_0(X48,X49)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).
% 0.19/0.37  fof(c_0_49, plain, ![X57]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X57)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.19/0.37  fof(c_0_50, plain, ![X8]:k3_xboole_0(X8,X8)=X8, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).
% 0.19/0.37  cnf(c_0_51, plain, (k7_subset_1(X2,X1,X3)=k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X3)))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_39]), c_0_40]), c_0_41]), c_0_42]), c_0_43]), c_0_44])).
% 0.19/0.37  cnf(c_0_52, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_45, c_0_46]), ['final']).
% 0.19/0.37  fof(c_0_53, negated_conjecture, (l1_struct_0(esk1_0)&(m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&(((k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)!=k1_xboole_0|esk2_0!=k2_struct_0(esk1_0))&(esk2_0=k2_struct_0(esk1_0)|esk2_0!=k2_struct_0(esk1_0)))&((k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)!=k1_xboole_0|k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)=k1_xboole_0)&(esk2_0=k2_struct_0(esk1_0)|k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)=k1_xboole_0))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_47])])])])).
% 0.19/0.37  fof(c_0_54, plain, ![X54, X55, X56]:(~m1_subset_1(X55,k1_zfmisc_1(X54))|(~m1_subset_1(X56,k1_zfmisc_1(X54))|k3_subset_1(X54,k7_subset_1(X54,X55,X56))=k4_subset_1(X54,k3_subset_1(X54,X55),X56))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t33_subset_1])])])).
% 0.19/0.37  fof(c_0_55, plain, ![X53]:k2_subset_1(X53)=k3_subset_1(X53,k1_subset_1(X53)), inference(variable_rename,[status(thm)],[t22_subset_1])).
% 0.19/0.37  fof(c_0_56, plain, ![X42]:k1_subset_1(X42)=k1_xboole_0, inference(variable_rename,[status(thm)],[d3_subset_1])).
% 0.19/0.37  cnf(c_0_57, plain, (k4_subset_1(X2,X1,X3)=k2_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_48]), ['final']).
% 0.19/0.37  cnf(c_0_58, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_49]), ['final']).
% 0.19/0.37  cnf(c_0_59, plain, (k3_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.19/0.37  fof(c_0_60, plain, ![X14]:k5_xboole_0(X14,X14)=k1_xboole_0, inference(variable_rename,[status(thm)],[t92_xboole_1])).
% 0.19/0.37  cnf(c_0_61, plain, (k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))=k7_subset_1(X1,X1,X2)), inference(spm,[status(thm)],[c_0_51, c_0_52]), ['final']).
% 0.19/0.37  cnf(c_0_62, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_53]), ['final']).
% 0.19/0.37  cnf(c_0_63, plain, (k3_subset_1(X2,k7_subset_1(X2,X1,X3))=k4_subset_1(X2,k3_subset_1(X2,X1),X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_54]), ['final']).
% 0.19/0.37  cnf(c_0_64, plain, (k2_subset_1(X1)=k3_subset_1(X1,k1_subset_1(X1))), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.19/0.37  cnf(c_0_65, plain, (k1_subset_1(X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.19/0.37  cnf(c_0_66, plain, (k4_subset_1(X1,X2,k1_xboole_0)=k2_xboole_0(X2,k1_xboole_0)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 0.19/0.37  cnf(c_0_67, plain, (k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59, c_0_30]), c_0_40]), c_0_41]), c_0_42]), c_0_43]), c_0_44]), ['final']).
% 0.19/0.37  cnf(c_0_68, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_60]), ['final']).
% 0.19/0.37  cnf(c_0_69, plain, (k7_subset_1(X1,X2,X3)=k7_subset_1(X2,X2,X3)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_51, c_0_61]), ['final']).
% 0.19/0.37  cnf(c_0_70, plain, (k4_subset_1(X1,X2,X1)=k2_xboole_0(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_57, c_0_52]), ['final']).
% 0.19/0.37  cnf(c_0_71, negated_conjecture, (k4_subset_1(u1_struct_0(esk1_0),X1,esk2_0)=k2_xboole_0(X1,esk2_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_57, c_0_62]), ['final']).
% 0.19/0.37  fof(c_0_72, plain, ![X11, X12]:(~r1_tarski(X11,X12)|k2_xboole_0(X11,X12)=X12), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.19/0.37  fof(c_0_73, plain, ![X13]:r1_tarski(k1_xboole_0,X13), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.19/0.37  cnf(c_0_74, plain, (k4_subset_1(X1,k3_subset_1(X1,X2),k1_xboole_0)=k3_subset_1(X1,k7_subset_1(X1,X2,k1_xboole_0))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_63, c_0_58]), ['final']).
% 0.19/0.37  cnf(c_0_75, plain, (X1=k3_subset_1(X1,k1_xboole_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_64, c_0_46]), c_0_65]), ['final']).
% 0.19/0.37  cnf(c_0_76, plain, (k4_subset_1(X1,X1,k1_xboole_0)=k2_xboole_0(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_66, c_0_52])).
% 0.19/0.37  cnf(c_0_77, plain, (k7_subset_1(X1,X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_67]), c_0_68]), ['final']).
% 0.19/0.37  cnf(c_0_78, plain, (k7_subset_1(X1,k1_xboole_0,X2)=k7_subset_1(k1_xboole_0,k1_xboole_0,X2)), inference(spm,[status(thm)],[c_0_69, c_0_58])).
% 0.19/0.37  cnf(c_0_79, plain, (k4_subset_1(X1,k3_subset_1(X1,X2),X1)=k3_subset_1(X1,k7_subset_1(X1,X2,X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_63, c_0_52]), ['final']).
% 0.19/0.37  cnf(c_0_80, plain, (k4_subset_1(X1,X1,X1)=k2_xboole_0(X1,X1)), inference(spm,[status(thm)],[c_0_70, c_0_52]), ['final']).
% 0.19/0.37  cnf(c_0_81, negated_conjecture, (k4_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),X1),esk2_0)=k3_subset_1(u1_struct_0(esk1_0),k7_subset_1(u1_struct_0(esk1_0),X1,esk2_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_63, c_0_62]), ['final']).
% 0.19/0.37  cnf(c_0_82, negated_conjecture, (k4_subset_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0),esk2_0)=k2_xboole_0(u1_struct_0(esk1_0),esk2_0)), inference(spm,[status(thm)],[c_0_71, c_0_52]), ['final']).
% 0.19/0.37  fof(c_0_83, plain, ![X45, X46]:(~m1_subset_1(X46,k1_zfmisc_1(X45))|k3_subset_1(X45,k3_subset_1(X45,X46))=X46), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).
% 0.19/0.37  cnf(c_0_84, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_72]), ['final']).
% 0.19/0.37  cnf(c_0_85, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_73]), ['final']).
% 0.19/0.37  cnf(c_0_86, plain, (k3_subset_1(X1,k7_subset_1(X1,k1_xboole_0,k1_xboole_0))=k2_xboole_0(X1,k1_xboole_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_58]), c_0_75]), c_0_76])).
% 0.19/0.37  cnf(c_0_87, plain, (k7_subset_1(X1,k1_xboole_0,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_77, c_0_78]), ['final']).
% 0.19/0.37  fof(c_0_88, plain, ![X60, X61, X62]:(~r2_hidden(X60,X61)|~m1_subset_1(X61,k1_zfmisc_1(X62))|m1_subset_1(X60,X62)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.19/0.37  cnf(c_0_89, plain, (k3_subset_1(X1,k7_subset_1(X1,k1_xboole_0,X1))=k2_xboole_0(X1,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_58]), c_0_75]), c_0_80])).
% 0.19/0.37  cnf(c_0_90, negated_conjecture, (k3_subset_1(u1_struct_0(esk1_0),k7_subset_1(u1_struct_0(esk1_0),k1_xboole_0,esk2_0))=k2_xboole_0(u1_struct_0(esk1_0),esk2_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_58]), c_0_75]), c_0_82])).
% 0.19/0.37  cnf(c_0_91, negated_conjecture, (k5_xboole_0(esk2_0,k1_setfam_1(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,X1)))=k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1)), inference(spm,[status(thm)],[c_0_51, c_0_62])).
% 0.19/0.37  cnf(c_0_92, plain, (k3_subset_1(X2,k3_subset_1(X2,X1))=X1|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_83]), ['final']).
% 0.19/0.37  cnf(c_0_93, plain, (k2_xboole_0(k1_xboole_0,X1)=X1), inference(spm,[status(thm)],[c_0_84, c_0_85]), ['final']).
% 0.19/0.37  cnf(c_0_94, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_86, c_0_87]), c_0_75]), ['final']).
% 0.19/0.37  cnf(c_0_95, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_88]), ['final']).
% 0.19/0.37  cnf(c_0_96, plain, (k3_subset_1(X1,k7_subset_1(k1_xboole_0,k1_xboole_0,X1))=k2_xboole_0(X1,X1)), inference(spm,[status(thm)],[c_0_89, c_0_78])).
% 0.19/0.37  cnf(c_0_97, negated_conjecture, (k3_subset_1(u1_struct_0(esk1_0),k7_subset_1(k1_xboole_0,k1_xboole_0,esk2_0))=k2_xboole_0(u1_struct_0(esk1_0),esk2_0)), inference(rw,[status(thm)],[c_0_90, c_0_78])).
% 0.19/0.37  cnf(c_0_98, negated_conjecture, (k4_subset_1(u1_struct_0(esk1_0),esk2_0,k1_xboole_0)=k2_xboole_0(esk2_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_66, c_0_62])).
% 0.19/0.37  cnf(c_0_99, negated_conjecture, (k4_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0),u1_struct_0(esk1_0))=k3_subset_1(u1_struct_0(esk1_0),k7_subset_1(u1_struct_0(esk1_0),esk2_0,u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_79, c_0_62])).
% 0.19/0.37  cnf(c_0_100, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1)=k7_subset_1(esk2_0,esk2_0,X1)), inference(rw,[status(thm)],[c_0_91, c_0_61]), ['final']).
% 0.19/0.37  cnf(c_0_101, negated_conjecture, (k4_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0),esk2_0)=k3_subset_1(u1_struct_0(esk1_0),k7_subset_1(u1_struct_0(esk1_0),esk2_0,esk2_0))), inference(spm,[status(thm)],[c_0_81, c_0_62])).
% 0.19/0.37  cnf(c_0_102, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),esk2_0,esk2_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_67]), c_0_68])).
% 0.19/0.37  cnf(c_0_103, plain, (k3_subset_1(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_58]), c_0_75]), ['final']).
% 0.19/0.37  cnf(c_0_104, plain, (k4_subset_1(X1,k1_xboole_0,k1_xboole_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_58]), c_0_93]), ['final']).
% 0.19/0.37  cnf(c_0_105, negated_conjecture, (k4_subset_1(u1_struct_0(esk1_0),k1_xboole_0,esk2_0)=esk2_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_58]), c_0_93]), ['final']).
% 0.19/0.37  cnf(c_0_106, plain, (k4_subset_1(X1,X2,k1_xboole_0)=X2|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_66, c_0_94]), ['final']).
% 0.19/0.37  cnf(c_0_107, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_95, c_0_52]), ['final']).
% 0.19/0.37  cnf(c_0_108, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_95, c_0_58]), ['final']).
% 0.19/0.37  cnf(c_0_109, negated_conjecture, (m1_subset_1(X1,u1_struct_0(esk1_0))|~r2_hidden(X1,esk2_0)), inference(spm,[status(thm)],[c_0_95, c_0_62]), ['final']).
% 0.19/0.37  cnf(c_0_110, negated_conjecture, (esk2_0=k2_struct_0(esk1_0)|k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_53]), ['final']).
% 0.19/0.37  cnf(c_0_111, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)!=k1_xboole_0|esk2_0!=k2_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_53]), ['final']).
% 0.19/0.37  cnf(c_0_112, plain, (k7_subset_1(X1,k1_xboole_0,X2)=k7_subset_1(X3,k1_xboole_0,X2)), inference(spm,[status(thm)],[c_0_78, c_0_78]), ['final']).
% 0.19/0.37  cnf(c_0_113, plain, (k3_subset_1(X1,k7_subset_1(X2,k1_xboole_0,X1))=k2_xboole_0(X1,X1)), inference(spm,[status(thm)],[c_0_96, c_0_78]), ['final']).
% 0.19/0.37  cnf(c_0_114, negated_conjecture, (k3_subset_1(u1_struct_0(esk1_0),k7_subset_1(X1,k1_xboole_0,esk2_0))=k2_xboole_0(u1_struct_0(esk1_0),esk2_0)), inference(spm,[status(thm)],[c_0_97, c_0_78]), ['final']).
% 0.19/0.37  cnf(c_0_115, negated_conjecture, (k4_subset_1(u1_struct_0(esk1_0),esk2_0,k1_xboole_0)=esk2_0), inference(rw,[status(thm)],[c_0_98, c_0_94]), ['final']).
% 0.19/0.37  cnf(c_0_116, plain, (k4_subset_1(X1,X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[c_0_76, c_0_94]), ['final']).
% 0.19/0.37  cnf(c_0_117, negated_conjecture, (k4_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0),u1_struct_0(esk1_0))=k3_subset_1(u1_struct_0(esk1_0),k7_subset_1(esk2_0,esk2_0,u1_struct_0(esk1_0)))), inference(rw,[status(thm)],[c_0_99, c_0_100]), ['final']).
% 0.19/0.37  cnf(c_0_118, negated_conjecture, (k4_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0),k1_xboole_0)=k3_subset_1(u1_struct_0(esk1_0),k7_subset_1(esk2_0,esk2_0,k1_xboole_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_62]), c_0_100]), ['final']).
% 0.19/0.37  cnf(c_0_119, negated_conjecture, (k4_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0),esk2_0)=u1_struct_0(esk1_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_101, c_0_102]), c_0_75]), ['final']).
% 0.19/0.37  cnf(c_0_120, plain, (k3_subset_1(X1,k7_subset_1(X1,X1,k1_xboole_0))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_52]), c_0_103]), c_0_104]), ['final']).
% 0.19/0.37  cnf(c_0_121, negated_conjecture, (k3_subset_1(u1_struct_0(esk1_0),k7_subset_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0),esk2_0))=esk2_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_52]), c_0_103]), c_0_105]), ['final']).
% 0.19/0.37  cnf(c_0_122, negated_conjecture, (k4_subset_1(u1_struct_0(esk1_0),esk2_0,u1_struct_0(esk1_0))=k2_xboole_0(esk2_0,u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_70, c_0_62]), ['final']).
% 0.19/0.37  cnf(c_0_123, negated_conjecture, (k4_subset_1(u1_struct_0(esk1_0),esk2_0,esk2_0)=k2_xboole_0(esk2_0,esk2_0)), inference(spm,[status(thm)],[c_0_71, c_0_62]), ['final']).
% 0.19/0.37  cnf(c_0_124, plain, (k4_subset_1(X1,k1_xboole_0,X1)=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_58]), c_0_93]), ['final']).
% 0.19/0.37  cnf(c_0_125, negated_conjecture, (k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0))=esk2_0), inference(spm,[status(thm)],[c_0_92, c_0_62]), ['final']).
% 0.19/0.37  cnf(c_0_126, negated_conjecture, (l1_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_53]), ['final']).
% 0.19/0.37  # SZS output end Saturation
% 0.19/0.37  # Proof object total steps             : 127
% 0.19/0.37  # Proof object clause steps            : 80
% 0.19/0.37  # Proof object formula steps           : 47
% 0.19/0.37  # Proof object conjectures             : 29
% 0.19/0.37  # Proof object clause conjectures      : 26
% 0.19/0.37  # Proof object formula conjectures     : 3
% 0.19/0.37  # Proof object initial clauses used    : 26
% 0.19/0.37  # Proof object initial formulas used   : 23
% 0.19/0.37  # Proof object generating inferences   : 39
% 0.19/0.37  # Proof object simplifying inferences  : 45
% 0.19/0.37  # Parsed axioms                        : 23
% 0.19/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.37  # Initial clauses                      : 28
% 0.19/0.37  # Removed in clause preprocessing      : 12
% 0.19/0.37  # Initial clauses in saturation        : 16
% 0.19/0.37  # Processed clauses                    : 91
% 0.19/0.37  # ...of these trivial                  : 4
% 0.19/0.37  # ...subsumed                          : 6
% 0.19/0.37  # ...remaining for further processing  : 81
% 0.19/0.37  # Other redundant clauses eliminated   : 0
% 0.19/0.37  # Clauses deleted for lack of memory   : 0
% 0.19/0.37  # Backward-subsumed                    : 1
% 0.19/0.37  # Backward-rewritten                   : 14
% 0.19/0.37  # Generated clauses                    : 96
% 0.19/0.37  # ...of the previous two non-trivial   : 62
% 0.19/0.37  # Contextual simplify-reflections      : 0
% 0.19/0.37  # Paramodulations                      : 96
% 0.19/0.37  # Factorizations                       : 0
% 0.19/0.37  # Equation resolutions                 : 0
% 0.19/0.37  # Propositional unsat checks           : 0
% 0.19/0.37  #    Propositional check models        : 0
% 0.19/0.37  #    Propositional check unsatisfiable : 0
% 0.19/0.37  #    Propositional clauses             : 0
% 0.19/0.37  #    Propositional clauses after purity: 0
% 0.19/0.37  #    Propositional unsat core size     : 0
% 0.19/0.37  #    Propositional preprocessing time  : 0.000
% 0.19/0.37  #    Propositional encoding time       : 0.000
% 0.19/0.37  #    Propositional solver time         : 0.000
% 0.19/0.37  #    Success case prop preproc time    : 0.000
% 0.19/0.37  #    Success case prop encoding time   : 0.000
% 0.19/0.37  #    Success case prop solver time     : 0.000
% 0.19/0.37  # Current number of processed clauses  : 50
% 0.19/0.37  #    Positive orientable unit clauses  : 32
% 0.19/0.37  #    Positive unorientable unit clauses: 1
% 0.19/0.37  #    Negative unit clauses             : 0
% 0.19/0.37  #    Non-unit-clauses                  : 17
% 0.19/0.37  # Current number of unprocessed clauses: 0
% 0.19/0.37  # ...number of literals in the above   : 0
% 0.19/0.37  # Current number of archived formulas  : 0
% 0.19/0.37  # Current number of archived clauses   : 41
% 0.19/0.37  # Clause-clause subsumption calls (NU) : 65
% 0.19/0.37  # Rec. Clause-clause subsumption calls : 63
% 0.19/0.37  # Non-unit clause-clause subsumptions  : 0
% 0.19/0.37  # Unit Clause-clause subsumption calls : 26
% 0.19/0.37  # Rewrite failures with RHS unbound    : 28
% 0.19/0.37  # BW rewrite match attempts            : 116
% 0.19/0.37  # BW rewrite match successes           : 26
% 0.19/0.37  # Condensation attempts                : 0
% 0.19/0.37  # Condensation successes               : 0
% 0.19/0.37  # Termbank termtop insertions          : 2710
% 0.19/0.37  
% 0.19/0.37  # -------------------------------------------------
% 0.19/0.37  # User time                : 0.031 s
% 0.19/0.37  # System time              : 0.005 s
% 0.19/0.37  # Total time               : 0.036 s
% 0.19/0.37  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
