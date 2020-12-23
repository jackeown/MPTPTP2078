%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:11:49 EST 2020

% Result     : Theorem 0.47s
% Output     : CNFRefutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :  139 (2658 expanded)
%              Number of clauses        :   82 (1124 expanded)
%              Number of leaves         :   28 ( 740 expanded)
%              Depth                    :   16
%              Number of atoms          :  267 (4095 expanded)
%              Number of equality atoms :  112 (2421 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    9 (   2 average)
%              Maximal term depth       :    4 (   2 average)

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

fof(dt_k2_subset_1,axiom,(
    ! [X1] : m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t77_tops_1,conjecture,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v4_pre_topc(X2,X1)
          <=> k2_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),X2,k1_tops_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tops_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(t44_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => r1_tarski(k1_tops_1(X1,X2),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(t52_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( ( v4_pre_topc(X2,X1)
             => k2_pre_topc(X1,X2) = X2 )
            & ( ( v2_pre_topc(X1)
                & k2_pre_topc(X1,X2) = X2 )
             => v4_pre_topc(X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

fof(involutiveness_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,k3_subset_1(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t33_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => k3_subset_1(X1,k7_subset_1(X1,X2,X3)) = k4_subset_1(X1,k3_subset_1(X1,X2),X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_subset_1)).

fof(dt_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(redefinition_k4_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => k4_subset_1(X1,X2,X3) = k2_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(dt_k2_tops_1,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k2_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(t65_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k2_pre_topc(X1,X2) = k4_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

fof(fc1_tops_1,axiom,(
    ! [X1,X2] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => v4_pre_topc(k2_pre_topc(X1,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_tops_1)).

fof(l78_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k2_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k1_tops_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

fof(c_0_28,plain,(
    ! [X65,X66] : k1_setfam_1(k2_tarski(X65,X66)) = k3_xboole_0(X65,X66) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_29,plain,(
    ! [X16,X17] : k1_enumset1(X16,X16,X17) = k2_tarski(X16,X17) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_30,plain,(
    ! [X12,X13] : k4_xboole_0(X12,X13) = k5_xboole_0(X12,k3_xboole_0(X12,X13)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_31,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_32,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_33,plain,(
    ! [X59,X60,X61] :
      ( ~ m1_subset_1(X60,k1_zfmisc_1(X59))
      | k7_subset_1(X59,X60,X61) = k4_xboole_0(X60,X61) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).

cnf(c_0_34,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_35,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_31,c_0_32])).

fof(c_0_36,plain,(
    ! [X18,X19,X20] : k2_enumset1(X18,X18,X19,X20) = k1_enumset1(X18,X19,X20) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_37,plain,(
    ! [X21,X22,X23,X24] : k3_enumset1(X21,X21,X22,X23,X24) = k2_enumset1(X21,X22,X23,X24) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_38,plain,(
    ! [X25,X26,X27,X28,X29] : k4_enumset1(X25,X25,X26,X27,X28,X29) = k3_enumset1(X25,X26,X27,X28,X29) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_39,plain,(
    ! [X30,X31,X32,X33,X34,X35] : k5_enumset1(X30,X30,X31,X32,X33,X34,X35) = k4_enumset1(X30,X31,X32,X33,X34,X35) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_40,plain,(
    ! [X36,X37,X38,X39,X40,X41,X42] : k6_enumset1(X36,X36,X37,X38,X39,X40,X41,X42) = k5_enumset1(X36,X37,X38,X39,X40,X41,X42) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_41,plain,(
    ! [X51] : m1_subset_1(k2_subset_1(X51),k1_zfmisc_1(X51)) ),
    inference(variable_rename,[status(thm)],[dt_k2_subset_1])).

fof(c_0_42,plain,(
    ! [X48] : k2_subset_1(X48) = X48 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

fof(c_0_43,plain,(
    ! [X10,X11] :
      ( ( k4_xboole_0(X10,X11) != k1_xboole_0
        | r1_tarski(X10,X11) )
      & ( ~ r1_tarski(X10,X11)
        | k4_xboole_0(X10,X11) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

fof(c_0_44,plain,(
    ! [X8,X9] :
      ( ( r1_tarski(X8,X9)
        | X8 != X9 )
      & ( r1_tarski(X9,X8)
        | X8 != X9 )
      & ( ~ r1_tarski(X8,X9)
        | ~ r1_tarski(X9,X8)
        | X8 = X9 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_45,negated_conjecture,(
    ~ ! [X1] :
        ( ( v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( v4_pre_topc(X2,X1)
            <=> k2_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),X2,k1_tops_1(X1,X2)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t77_tops_1])).

fof(c_0_46,plain,(
    ! [X14,X15] : r1_tarski(k4_xboole_0(X14,X15),X14) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

cnf(c_0_47,plain,
    ( k7_subset_1(X2,X1,X3) = k4_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_48,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2))) ),
    inference(rw,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_49,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_50,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_51,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_52,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_53,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_54,plain,
    ( m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_55,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_56,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_57,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

fof(c_0_58,plain,(
    ! [X49,X50] :
      ( ~ m1_subset_1(X50,k1_zfmisc_1(X49))
      | k3_subset_1(X49,X50) = k4_xboole_0(X49,X50) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

fof(c_0_59,plain,(
    ! [X77,X78] :
      ( ~ l1_pre_topc(X77)
      | ~ m1_subset_1(X78,k1_zfmisc_1(u1_struct_0(X77)))
      | r1_tarski(k1_tops_1(X77,X78),X78) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_tops_1])])])).

fof(c_0_60,negated_conjecture,
    ( v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & ( ~ v4_pre_topc(esk2_0,esk1_0)
      | k2_tops_1(esk1_0,esk2_0) != k7_subset_1(u1_struct_0(esk1_0),esk2_0,k1_tops_1(esk1_0,esk2_0)) )
    & ( v4_pre_topc(esk2_0,esk1_0)
      | k2_tops_1(esk1_0,esk2_0) = k7_subset_1(u1_struct_0(esk1_0),esk2_0,k1_tops_1(esk1_0,esk2_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_45])])])).

fof(c_0_61,plain,(
    ! [X67,X68] :
      ( ( ~ m1_subset_1(X67,k1_zfmisc_1(X68))
        | r1_tarski(X67,X68) )
      & ( ~ r1_tarski(X67,X68)
        | m1_subset_1(X67,k1_zfmisc_1(X68)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_62,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_63,plain,
    ( k7_subset_1(X2,X1,X3) = k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_48]),c_0_49]),c_0_50]),c_0_51]),c_0_52]),c_0_53])).

cnf(c_0_64,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_65,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_48]),c_0_49]),c_0_50]),c_0_51]),c_0_52]),c_0_53])).

cnf(c_0_66,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_57])).

fof(c_0_67,plain,(
    ! [X69,X70] :
      ( ( ~ v4_pre_topc(X70,X69)
        | k2_pre_topc(X69,X70) = X70
        | ~ m1_subset_1(X70,k1_zfmisc_1(u1_struct_0(X69)))
        | ~ l1_pre_topc(X69) )
      & ( ~ v2_pre_topc(X69)
        | k2_pre_topc(X69,X70) != X70
        | v4_pre_topc(X70,X69)
        | ~ m1_subset_1(X70,k1_zfmisc_1(u1_struct_0(X69)))
        | ~ l1_pre_topc(X69) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t52_pre_topc])])])])).

cnf(c_0_68,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_69,plain,
    ( r1_tarski(k1_tops_1(X1,X2),X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_70,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_71,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_72,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_73,plain,
    ( r1_tarski(k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_62,c_0_48]),c_0_49]),c_0_50]),c_0_51]),c_0_52]),c_0_53])).

fof(c_0_74,plain,(
    ! [X54,X55] :
      ( ~ m1_subset_1(X55,k1_zfmisc_1(X54))
      | k3_subset_1(X54,k3_subset_1(X54,X55)) = X55 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).

cnf(c_0_75,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) = k7_subset_1(X1,X1,X2) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_76,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_77,plain,
    ( k2_pre_topc(X2,X1) = X1
    | ~ v4_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_78,plain,
    ( k3_subset_1(X2,X1) = k5_xboole_0(X2,k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_68,c_0_48]),c_0_49]),c_0_50]),c_0_51]),c_0_52]),c_0_53])).

cnf(c_0_79,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,esk2_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_71])])).

fof(c_0_80,plain,(
    ! [X43,X44] : k3_tarski(k2_tarski(X43,X44)) = k2_xboole_0(X43,X44) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_81,plain,(
    ! [X62,X63,X64] :
      ( ~ m1_subset_1(X63,k1_zfmisc_1(X62))
      | ~ m1_subset_1(X64,k1_zfmisc_1(X62))
      | k3_subset_1(X62,k7_subset_1(X62,X63,X64)) = k4_subset_1(X62,k3_subset_1(X62,X63),X64) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t33_subset_1])])])).

cnf(c_0_82,plain,
    ( m1_subset_1(k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_83,plain,
    ( k3_subset_1(X2,k3_subset_1(X2,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

cnf(c_0_84,plain,
    ( k7_subset_1(X1,X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_65,c_0_75])).

cnf(c_0_85,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_73,c_0_76])).

fof(c_0_86,plain,(
    ! [X52,X53] :
      ( ~ m1_subset_1(X53,k1_zfmisc_1(X52))
      | m1_subset_1(k3_subset_1(X52,X53),k1_zfmisc_1(X52)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).

cnf(c_0_87,negated_conjecture,
    ( k2_pre_topc(esk1_0,esk2_0) = esk2_0
    | ~ v4_pre_topc(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_70]),c_0_71])])).

cnf(c_0_88,negated_conjecture,
    ( v4_pre_topc(esk2_0,esk1_0)
    | k2_tops_1(esk1_0,esk2_0) = k7_subset_1(u1_struct_0(esk1_0),esk2_0,k1_tops_1(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_89,plain,
    ( k7_subset_1(X1,X2,X3) = k7_subset_1(X2,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_63,c_0_75])).

cnf(c_0_90,plain,
    ( k7_subset_1(X1,X1,X2) = k3_subset_1(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_78,c_0_75])).

cnf(c_0_91,negated_conjecture,
    ( m1_subset_1(k1_tops_1(esk1_0,esk2_0),k1_zfmisc_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_72,c_0_79])).

fof(c_0_92,plain,(
    ! [X56,X57,X58] :
      ( ~ m1_subset_1(X57,k1_zfmisc_1(X56))
      | ~ m1_subset_1(X58,k1_zfmisc_1(X56))
      | k4_subset_1(X56,X57,X58) = k2_xboole_0(X57,X58) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).

cnf(c_0_93,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_80])).

fof(c_0_94,plain,(
    ! [X71,X72] :
      ( ~ l1_pre_topc(X71)
      | ~ m1_subset_1(X72,k1_zfmisc_1(u1_struct_0(X71)))
      | m1_subset_1(k2_tops_1(X71,X72),k1_zfmisc_1(u1_struct_0(X71))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_tops_1])])).

cnf(c_0_95,plain,
    ( k3_subset_1(X2,k7_subset_1(X2,X1,X3)) = k4_subset_1(X2,k3_subset_1(X2,X1),X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_81])).

cnf(c_0_96,plain,
    ( m1_subset_1(k7_subset_1(X1,X1,X2),k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_82,c_0_75])).

cnf(c_0_97,plain,
    ( k3_subset_1(X1,k3_subset_1(X1,X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_83,c_0_64])).

cnf(c_0_98,plain,
    ( k3_subset_1(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_64]),c_0_76])).

cnf(c_0_99,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_82,c_0_76])).

cnf(c_0_100,plain,
    ( k7_subset_1(k1_xboole_0,k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_84,c_0_85])).

cnf(c_0_101,plain,
    ( m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_86])).

cnf(c_0_102,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),esk2_0,k1_tops_1(esk1_0,esk2_0)) = k2_tops_1(esk1_0,esk2_0)
    | k2_pre_topc(esk1_0,esk2_0) = esk2_0 ),
    inference(spm,[status(thm)],[c_0_87,c_0_88])).

cnf(c_0_103,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1) = k7_subset_1(esk2_0,esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_89,c_0_70])).

cnf(c_0_104,negated_conjecture,
    ( k7_subset_1(esk2_0,esk2_0,k1_tops_1(esk1_0,esk2_0)) = k3_subset_1(esk2_0,k1_tops_1(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_90,c_0_91])).

cnf(c_0_105,plain,
    ( k4_subset_1(X2,X1,X3) = k2_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_92])).

cnf(c_0_106,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_93,c_0_32])).

cnf(c_0_107,plain,
    ( m1_subset_1(k2_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_94])).

fof(c_0_108,plain,(
    ! [X79,X80] :
      ( ~ l1_pre_topc(X79)
      | ~ m1_subset_1(X80,k1_zfmisc_1(u1_struct_0(X79)))
      | k2_pre_topc(X79,X80) = k4_subset_1(u1_struct_0(X79),X80,k2_tops_1(X79,X80)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_tops_1])])])).

cnf(c_0_109,plain,
    ( k4_subset_1(X1,k3_subset_1(X1,X2),k7_subset_1(X1,X1,X3)) = k3_subset_1(X1,k7_subset_1(X1,X2,k7_subset_1(X1,X1,X3)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_95,c_0_96])).

cnf(c_0_110,plain,
    ( k3_subset_1(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[c_0_97,c_0_98])).

cnf(c_0_111,plain,
    ( k7_subset_1(X1,k1_xboole_0,X2) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_99]),c_0_100])).

cnf(c_0_112,negated_conjecture,
    ( m1_subset_1(k3_subset_1(esk2_0,k1_tops_1(esk1_0,esk2_0)),k1_zfmisc_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_101,c_0_91])).

cnf(c_0_113,negated_conjecture,
    ( k3_subset_1(esk2_0,k1_tops_1(esk1_0,esk2_0)) = k2_tops_1(esk1_0,esk2_0)
    | k2_pre_topc(esk1_0,esk2_0) = esk2_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_102,c_0_103]),c_0_104])).

cnf(c_0_114,plain,
    ( k4_subset_1(X2,X1,X3) = k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_105,c_0_106]),c_0_49]),c_0_50]),c_0_51]),c_0_52]),c_0_53])).

cnf(c_0_115,negated_conjecture,
    ( m1_subset_1(k2_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_70]),c_0_71])])).

cnf(c_0_116,plain,
    ( k2_pre_topc(X1,X2) = k4_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_108])).

cnf(c_0_117,plain,
    ( k4_subset_1(X1,X1,k7_subset_1(X1,X1,X2)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_99]),c_0_110]),c_0_111]),c_0_110])).

cnf(c_0_118,negated_conjecture,
    ( k2_pre_topc(esk1_0,esk2_0) = esk2_0
    | m1_subset_1(k2_tops_1(esk1_0,esk2_0),k1_zfmisc_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_112,c_0_113])).

cnf(c_0_119,negated_conjecture,
    ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k2_tops_1(esk1_0,esk2_0))) = k4_subset_1(u1_struct_0(esk1_0),X1,k2_tops_1(esk1_0,esk2_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_114,c_0_115])).

cnf(c_0_120,negated_conjecture,
    ( k4_subset_1(u1_struct_0(esk1_0),esk2_0,k2_tops_1(esk1_0,esk2_0)) = k2_pre_topc(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116,c_0_70]),c_0_71])])).

fof(c_0_121,plain,(
    ! [X73,X74] :
      ( ~ v2_pre_topc(X73)
      | ~ l1_pre_topc(X73)
      | ~ m1_subset_1(X74,k1_zfmisc_1(u1_struct_0(X73)))
      | v4_pre_topc(k2_pre_topc(X73,X74),X73) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_tops_1])])).

cnf(c_0_122,negated_conjecture,
    ( k4_subset_1(esk2_0,esk2_0,k3_subset_1(esk2_0,k1_tops_1(esk1_0,esk2_0))) = esk2_0 ),
    inference(spm,[status(thm)],[c_0_117,c_0_104])).

cnf(c_0_123,negated_conjecture,
    ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k2_tops_1(esk1_0,esk2_0))) = k4_subset_1(esk2_0,X1,k2_tops_1(esk1_0,esk2_0))
    | k2_pre_topc(esk1_0,esk2_0) = esk2_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_114,c_0_118])).

cnf(c_0_124,negated_conjecture,
    ( k3_tarski(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,k2_tops_1(esk1_0,esk2_0))) = k2_pre_topc(esk1_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119,c_0_70]),c_0_120])).

cnf(c_0_125,plain,
    ( v4_pre_topc(k2_pre_topc(X1,X2),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_121])).

cnf(c_0_126,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_127,negated_conjecture,
    ( k4_subset_1(esk2_0,esk2_0,k2_tops_1(esk1_0,esk2_0)) = esk2_0
    | k2_pre_topc(esk1_0,esk2_0) = esk2_0 ),
    inference(spm,[status(thm)],[c_0_122,c_0_113])).

cnf(c_0_128,negated_conjecture,
    ( k4_subset_1(esk2_0,esk2_0,k2_tops_1(esk1_0,esk2_0)) = k2_pre_topc(esk1_0,esk2_0)
    | k2_pre_topc(esk1_0,esk2_0) = esk2_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_123,c_0_64]),c_0_124])).

fof(c_0_129,plain,(
    ! [X75,X76] :
      ( ~ l1_pre_topc(X75)
      | ~ m1_subset_1(X76,k1_zfmisc_1(u1_struct_0(X75)))
      | k2_tops_1(X75,X76) = k7_subset_1(u1_struct_0(X75),k2_pre_topc(X75,X76),k1_tops_1(X75,X76)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l78_tops_1])])])).

cnf(c_0_130,negated_conjecture,
    ( ~ v4_pre_topc(esk2_0,esk1_0)
    | k2_tops_1(esk1_0,esk2_0) != k7_subset_1(u1_struct_0(esk1_0),esk2_0,k1_tops_1(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_131,negated_conjecture,
    ( v4_pre_topc(k2_pre_topc(esk1_0,esk2_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_125,c_0_70]),c_0_126]),c_0_71])])).

cnf(c_0_132,negated_conjecture,
    ( k2_pre_topc(esk1_0,esk2_0) = esk2_0 ),
    inference(spm,[status(thm)],[c_0_127,c_0_128])).

cnf(c_0_133,plain,
    ( k2_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k1_tops_1(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_129])).

cnf(c_0_134,negated_conjecture,
    ( k3_subset_1(esk2_0,k1_tops_1(esk1_0,esk2_0)) != k2_tops_1(esk1_0,esk2_0)
    | ~ v4_pre_topc(esk2_0,esk1_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_130,c_0_103]),c_0_104])).

cnf(c_0_135,negated_conjecture,
    ( v4_pre_topc(esk2_0,esk1_0) ),
    inference(rw,[status(thm)],[c_0_131,c_0_132])).

cnf(c_0_136,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),k1_tops_1(esk1_0,esk2_0)) = k2_tops_1(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_133,c_0_70]),c_0_71])])).

cnf(c_0_137,negated_conjecture,
    ( k3_subset_1(esk2_0,k1_tops_1(esk1_0,esk2_0)) != k2_tops_1(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_134,c_0_135])])).

cnf(c_0_138,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_136,c_0_132]),c_0_103]),c_0_104]),c_0_137]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:05:59 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.47/0.70  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_S2mI
% 0.47/0.70  # and selection function SelectCQArNTNpEqFirst.
% 0.47/0.70  #
% 0.47/0.70  # Preprocessing time       : 0.028 s
% 0.47/0.70  # Presaturation interreduction done
% 0.47/0.70  
% 0.47/0.70  # Proof found!
% 0.47/0.70  # SZS status Theorem
% 0.47/0.70  # SZS output start CNFRefutation
% 0.47/0.70  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.47/0.70  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.47/0.70  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.47/0.70  fof(redefinition_k7_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k7_subset_1(X1,X2,X3)=k4_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 0.47/0.70  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.47/0.70  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.47/0.70  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 0.47/0.70  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 0.47/0.70  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 0.47/0.70  fof(dt_k2_subset_1, axiom, ![X1]:m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 0.47/0.70  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 0.47/0.70  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.47/0.70  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.47/0.70  fof(t77_tops_1, conjecture, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v4_pre_topc(X2,X1)<=>k2_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),X2,k1_tops_1(X1,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_tops_1)).
% 0.47/0.70  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.47/0.70  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 0.47/0.70  fof(t44_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>r1_tarski(k1_tops_1(X1,X2),X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_1)).
% 0.47/0.70  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.47/0.70  fof(t52_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>((v4_pre_topc(X2,X1)=>k2_pre_topc(X1,X2)=X2)&((v2_pre_topc(X1)&k2_pre_topc(X1,X2)=X2)=>v4_pre_topc(X2,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 0.47/0.70  fof(involutiveness_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,k3_subset_1(X1,X2))=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 0.47/0.70  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.47/0.70  fof(t33_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k3_subset_1(X1,k7_subset_1(X1,X2,X3))=k4_subset_1(X1,k3_subset_1(X1,X2),X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_subset_1)).
% 0.47/0.70  fof(dt_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 0.47/0.70  fof(redefinition_k4_subset_1, axiom, ![X1, X2, X3]:((m1_subset_1(X2,k1_zfmisc_1(X1))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>k4_subset_1(X1,X2,X3)=k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 0.47/0.70  fof(dt_k2_tops_1, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>m1_subset_1(k2_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 0.47/0.70  fof(t65_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k2_pre_topc(X1,X2)=k4_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tops_1)).
% 0.47/0.70  fof(fc1_tops_1, axiom, ![X1, X2]:(((v2_pre_topc(X1)&l1_pre_topc(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>v4_pre_topc(k2_pre_topc(X1,X2),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_tops_1)).
% 0.47/0.70  fof(l78_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k2_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k1_tops_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l78_tops_1)).
% 0.47/0.70  fof(c_0_28, plain, ![X65, X66]:k1_setfam_1(k2_tarski(X65,X66))=k3_xboole_0(X65,X66), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.47/0.70  fof(c_0_29, plain, ![X16, X17]:k1_enumset1(X16,X16,X17)=k2_tarski(X16,X17), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.47/0.70  fof(c_0_30, plain, ![X12, X13]:k4_xboole_0(X12,X13)=k5_xboole_0(X12,k3_xboole_0(X12,X13)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.47/0.70  cnf(c_0_31, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.47/0.70  cnf(c_0_32, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.47/0.70  fof(c_0_33, plain, ![X59, X60, X61]:(~m1_subset_1(X60,k1_zfmisc_1(X59))|k7_subset_1(X59,X60,X61)=k4_xboole_0(X60,X61)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).
% 0.47/0.70  cnf(c_0_34, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.47/0.70  cnf(c_0_35, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_31, c_0_32])).
% 0.47/0.70  fof(c_0_36, plain, ![X18, X19, X20]:k2_enumset1(X18,X18,X19,X20)=k1_enumset1(X18,X19,X20), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.47/0.70  fof(c_0_37, plain, ![X21, X22, X23, X24]:k3_enumset1(X21,X21,X22,X23,X24)=k2_enumset1(X21,X22,X23,X24), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.47/0.70  fof(c_0_38, plain, ![X25, X26, X27, X28, X29]:k4_enumset1(X25,X25,X26,X27,X28,X29)=k3_enumset1(X25,X26,X27,X28,X29), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.47/0.70  fof(c_0_39, plain, ![X30, X31, X32, X33, X34, X35]:k5_enumset1(X30,X30,X31,X32,X33,X34,X35)=k4_enumset1(X30,X31,X32,X33,X34,X35), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.47/0.70  fof(c_0_40, plain, ![X36, X37, X38, X39, X40, X41, X42]:k6_enumset1(X36,X36,X37,X38,X39,X40,X41,X42)=k5_enumset1(X36,X37,X38,X39,X40,X41,X42), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.47/0.70  fof(c_0_41, plain, ![X51]:m1_subset_1(k2_subset_1(X51),k1_zfmisc_1(X51)), inference(variable_rename,[status(thm)],[dt_k2_subset_1])).
% 0.47/0.70  fof(c_0_42, plain, ![X48]:k2_subset_1(X48)=X48, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 0.47/0.70  fof(c_0_43, plain, ![X10, X11]:((k4_xboole_0(X10,X11)!=k1_xboole_0|r1_tarski(X10,X11))&(~r1_tarski(X10,X11)|k4_xboole_0(X10,X11)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.47/0.70  fof(c_0_44, plain, ![X8, X9]:(((r1_tarski(X8,X9)|X8!=X9)&(r1_tarski(X9,X8)|X8!=X9))&(~r1_tarski(X8,X9)|~r1_tarski(X9,X8)|X8=X9)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.47/0.70  fof(c_0_45, negated_conjecture, ~(![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v4_pre_topc(X2,X1)<=>k2_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),X2,k1_tops_1(X1,X2)))))), inference(assume_negation,[status(cth)],[t77_tops_1])).
% 0.47/0.70  fof(c_0_46, plain, ![X14, X15]:r1_tarski(k4_xboole_0(X14,X15),X14), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.47/0.70  cnf(c_0_47, plain, (k7_subset_1(X2,X1,X3)=k4_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.47/0.70  cnf(c_0_48, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2)))), inference(rw,[status(thm)],[c_0_34, c_0_35])).
% 0.47/0.70  cnf(c_0_49, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.47/0.70  cnf(c_0_50, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.47/0.70  cnf(c_0_51, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.47/0.70  cnf(c_0_52, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.47/0.70  cnf(c_0_53, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.47/0.70  cnf(c_0_54, plain, (m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.47/0.70  cnf(c_0_55, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.47/0.70  cnf(c_0_56, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.47/0.70  cnf(c_0_57, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.47/0.70  fof(c_0_58, plain, ![X49, X50]:(~m1_subset_1(X50,k1_zfmisc_1(X49))|k3_subset_1(X49,X50)=k4_xboole_0(X49,X50)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 0.47/0.70  fof(c_0_59, plain, ![X77, X78]:(~l1_pre_topc(X77)|(~m1_subset_1(X78,k1_zfmisc_1(u1_struct_0(X77)))|r1_tarski(k1_tops_1(X77,X78),X78))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_tops_1])])])).
% 0.47/0.70  fof(c_0_60, negated_conjecture, ((v2_pre_topc(esk1_0)&l1_pre_topc(esk1_0))&(m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&((~v4_pre_topc(esk2_0,esk1_0)|k2_tops_1(esk1_0,esk2_0)!=k7_subset_1(u1_struct_0(esk1_0),esk2_0,k1_tops_1(esk1_0,esk2_0)))&(v4_pre_topc(esk2_0,esk1_0)|k2_tops_1(esk1_0,esk2_0)=k7_subset_1(u1_struct_0(esk1_0),esk2_0,k1_tops_1(esk1_0,esk2_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_45])])])).
% 0.47/0.70  fof(c_0_61, plain, ![X67, X68]:((~m1_subset_1(X67,k1_zfmisc_1(X68))|r1_tarski(X67,X68))&(~r1_tarski(X67,X68)|m1_subset_1(X67,k1_zfmisc_1(X68)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.47/0.70  cnf(c_0_62, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.47/0.70  cnf(c_0_63, plain, (k7_subset_1(X2,X1,X3)=k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X3)))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47, c_0_48]), c_0_49]), c_0_50]), c_0_51]), c_0_52]), c_0_53])).
% 0.47/0.70  cnf(c_0_64, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_54, c_0_55])).
% 0.47/0.70  cnf(c_0_65, plain, (k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))=k1_xboole_0|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56, c_0_48]), c_0_49]), c_0_50]), c_0_51]), c_0_52]), c_0_53])).
% 0.47/0.70  cnf(c_0_66, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_57])).
% 0.47/0.70  fof(c_0_67, plain, ![X69, X70]:((~v4_pre_topc(X70,X69)|k2_pre_topc(X69,X70)=X70|~m1_subset_1(X70,k1_zfmisc_1(u1_struct_0(X69)))|~l1_pre_topc(X69))&(~v2_pre_topc(X69)|k2_pre_topc(X69,X70)!=X70|v4_pre_topc(X70,X69)|~m1_subset_1(X70,k1_zfmisc_1(u1_struct_0(X69)))|~l1_pre_topc(X69))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t52_pre_topc])])])])).
% 0.47/0.70  cnf(c_0_68, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.47/0.70  cnf(c_0_69, plain, (r1_tarski(k1_tops_1(X1,X2),X2)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.47/0.70  cnf(c_0_70, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.47/0.70  cnf(c_0_71, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.47/0.70  cnf(c_0_72, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.47/0.70  cnf(c_0_73, plain, (r1_tarski(k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_62, c_0_48]), c_0_49]), c_0_50]), c_0_51]), c_0_52]), c_0_53])).
% 0.47/0.70  fof(c_0_74, plain, ![X54, X55]:(~m1_subset_1(X55,k1_zfmisc_1(X54))|k3_subset_1(X54,k3_subset_1(X54,X55))=X55), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).
% 0.47/0.70  cnf(c_0_75, plain, (k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))=k7_subset_1(X1,X1,X2)), inference(spm,[status(thm)],[c_0_63, c_0_64])).
% 0.47/0.70  cnf(c_0_76, plain, (k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))=k1_xboole_0), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 0.47/0.70  cnf(c_0_77, plain, (k2_pre_topc(X2,X1)=X1|~v4_pre_topc(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.47/0.70  cnf(c_0_78, plain, (k3_subset_1(X2,X1)=k5_xboole_0(X2,k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1)))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_68, c_0_48]), c_0_49]), c_0_50]), c_0_51]), c_0_52]), c_0_53])).
% 0.47/0.70  cnf(c_0_79, negated_conjecture, (r1_tarski(k1_tops_1(esk1_0,esk2_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_71])])).
% 0.47/0.70  fof(c_0_80, plain, ![X43, X44]:k3_tarski(k2_tarski(X43,X44))=k2_xboole_0(X43,X44), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.47/0.70  fof(c_0_81, plain, ![X62, X63, X64]:(~m1_subset_1(X63,k1_zfmisc_1(X62))|(~m1_subset_1(X64,k1_zfmisc_1(X62))|k3_subset_1(X62,k7_subset_1(X62,X63,X64))=k4_subset_1(X62,k3_subset_1(X62,X63),X64))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t33_subset_1])])])).
% 0.47/0.70  cnf(c_0_82, plain, (m1_subset_1(k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_72, c_0_73])).
% 0.47/0.70  cnf(c_0_83, plain, (k3_subset_1(X2,k3_subset_1(X2,X1))=X1|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_74])).
% 0.47/0.70  cnf(c_0_84, plain, (k7_subset_1(X1,X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_65, c_0_75])).
% 0.47/0.70  cnf(c_0_85, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_73, c_0_76])).
% 0.47/0.70  fof(c_0_86, plain, ![X52, X53]:(~m1_subset_1(X53,k1_zfmisc_1(X52))|m1_subset_1(k3_subset_1(X52,X53),k1_zfmisc_1(X52))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).
% 0.47/0.70  cnf(c_0_87, negated_conjecture, (k2_pre_topc(esk1_0,esk2_0)=esk2_0|~v4_pre_topc(esk2_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_70]), c_0_71])])).
% 0.47/0.70  cnf(c_0_88, negated_conjecture, (v4_pre_topc(esk2_0,esk1_0)|k2_tops_1(esk1_0,esk2_0)=k7_subset_1(u1_struct_0(esk1_0),esk2_0,k1_tops_1(esk1_0,esk2_0))), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.47/0.70  cnf(c_0_89, plain, (k7_subset_1(X1,X2,X3)=k7_subset_1(X2,X2,X3)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_63, c_0_75])).
% 0.47/0.70  cnf(c_0_90, plain, (k7_subset_1(X1,X1,X2)=k3_subset_1(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_78, c_0_75])).
% 0.47/0.70  cnf(c_0_91, negated_conjecture, (m1_subset_1(k1_tops_1(esk1_0,esk2_0),k1_zfmisc_1(esk2_0))), inference(spm,[status(thm)],[c_0_72, c_0_79])).
% 0.47/0.70  fof(c_0_92, plain, ![X56, X57, X58]:(~m1_subset_1(X57,k1_zfmisc_1(X56))|~m1_subset_1(X58,k1_zfmisc_1(X56))|k4_subset_1(X56,X57,X58)=k2_xboole_0(X57,X58)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).
% 0.47/0.70  cnf(c_0_93, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_80])).
% 0.47/0.70  fof(c_0_94, plain, ![X71, X72]:(~l1_pre_topc(X71)|~m1_subset_1(X72,k1_zfmisc_1(u1_struct_0(X71)))|m1_subset_1(k2_tops_1(X71,X72),k1_zfmisc_1(u1_struct_0(X71)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_tops_1])])).
% 0.47/0.70  cnf(c_0_95, plain, (k3_subset_1(X2,k7_subset_1(X2,X1,X3))=k4_subset_1(X2,k3_subset_1(X2,X1),X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_81])).
% 0.47/0.70  cnf(c_0_96, plain, (m1_subset_1(k7_subset_1(X1,X1,X2),k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_82, c_0_75])).
% 0.47/0.70  cnf(c_0_97, plain, (k3_subset_1(X1,k3_subset_1(X1,X1))=X1), inference(spm,[status(thm)],[c_0_83, c_0_64])).
% 0.47/0.70  cnf(c_0_98, plain, (k3_subset_1(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_64]), c_0_76])).
% 0.47/0.70  cnf(c_0_99, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_82, c_0_76])).
% 0.47/0.70  cnf(c_0_100, plain, (k7_subset_1(k1_xboole_0,k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_84, c_0_85])).
% 0.47/0.70  cnf(c_0_101, plain, (m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_86])).
% 0.47/0.70  cnf(c_0_102, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),esk2_0,k1_tops_1(esk1_0,esk2_0))=k2_tops_1(esk1_0,esk2_0)|k2_pre_topc(esk1_0,esk2_0)=esk2_0), inference(spm,[status(thm)],[c_0_87, c_0_88])).
% 0.47/0.70  cnf(c_0_103, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1)=k7_subset_1(esk2_0,esk2_0,X1)), inference(spm,[status(thm)],[c_0_89, c_0_70])).
% 0.47/0.70  cnf(c_0_104, negated_conjecture, (k7_subset_1(esk2_0,esk2_0,k1_tops_1(esk1_0,esk2_0))=k3_subset_1(esk2_0,k1_tops_1(esk1_0,esk2_0))), inference(spm,[status(thm)],[c_0_90, c_0_91])).
% 0.47/0.70  cnf(c_0_105, plain, (k4_subset_1(X2,X1,X3)=k2_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_92])).
% 0.47/0.70  cnf(c_0_106, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_93, c_0_32])).
% 0.47/0.70  cnf(c_0_107, plain, (m1_subset_1(k2_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_94])).
% 0.47/0.70  fof(c_0_108, plain, ![X79, X80]:(~l1_pre_topc(X79)|(~m1_subset_1(X80,k1_zfmisc_1(u1_struct_0(X79)))|k2_pre_topc(X79,X80)=k4_subset_1(u1_struct_0(X79),X80,k2_tops_1(X79,X80)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_tops_1])])])).
% 0.47/0.70  cnf(c_0_109, plain, (k4_subset_1(X1,k3_subset_1(X1,X2),k7_subset_1(X1,X1,X3))=k3_subset_1(X1,k7_subset_1(X1,X2,k7_subset_1(X1,X1,X3)))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_95, c_0_96])).
% 0.47/0.70  cnf(c_0_110, plain, (k3_subset_1(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[c_0_97, c_0_98])).
% 0.47/0.70  cnf(c_0_111, plain, (k7_subset_1(X1,k1_xboole_0,X2)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_99]), c_0_100])).
% 0.47/0.70  cnf(c_0_112, negated_conjecture, (m1_subset_1(k3_subset_1(esk2_0,k1_tops_1(esk1_0,esk2_0)),k1_zfmisc_1(esk2_0))), inference(spm,[status(thm)],[c_0_101, c_0_91])).
% 0.47/0.70  cnf(c_0_113, negated_conjecture, (k3_subset_1(esk2_0,k1_tops_1(esk1_0,esk2_0))=k2_tops_1(esk1_0,esk2_0)|k2_pre_topc(esk1_0,esk2_0)=esk2_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_102, c_0_103]), c_0_104])).
% 0.47/0.70  cnf(c_0_114, plain, (k4_subset_1(X2,X1,X3)=k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X3))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_105, c_0_106]), c_0_49]), c_0_50]), c_0_51]), c_0_52]), c_0_53])).
% 0.47/0.70  cnf(c_0_115, negated_conjecture, (m1_subset_1(k2_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107, c_0_70]), c_0_71])])).
% 0.47/0.70  cnf(c_0_116, plain, (k2_pre_topc(X1,X2)=k4_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_108])).
% 0.47/0.70  cnf(c_0_117, plain, (k4_subset_1(X1,X1,k7_subset_1(X1,X1,X2))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109, c_0_99]), c_0_110]), c_0_111]), c_0_110])).
% 0.47/0.70  cnf(c_0_118, negated_conjecture, (k2_pre_topc(esk1_0,esk2_0)=esk2_0|m1_subset_1(k2_tops_1(esk1_0,esk2_0),k1_zfmisc_1(esk2_0))), inference(spm,[status(thm)],[c_0_112, c_0_113])).
% 0.47/0.70  cnf(c_0_119, negated_conjecture, (k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k2_tops_1(esk1_0,esk2_0)))=k4_subset_1(u1_struct_0(esk1_0),X1,k2_tops_1(esk1_0,esk2_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_114, c_0_115])).
% 0.47/0.70  cnf(c_0_120, negated_conjecture, (k4_subset_1(u1_struct_0(esk1_0),esk2_0,k2_tops_1(esk1_0,esk2_0))=k2_pre_topc(esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116, c_0_70]), c_0_71])])).
% 0.47/0.70  fof(c_0_121, plain, ![X73, X74]:(~v2_pre_topc(X73)|~l1_pre_topc(X73)|~m1_subset_1(X74,k1_zfmisc_1(u1_struct_0(X73)))|v4_pre_topc(k2_pre_topc(X73,X74),X73)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_tops_1])])).
% 0.47/0.70  cnf(c_0_122, negated_conjecture, (k4_subset_1(esk2_0,esk2_0,k3_subset_1(esk2_0,k1_tops_1(esk1_0,esk2_0)))=esk2_0), inference(spm,[status(thm)],[c_0_117, c_0_104])).
% 0.47/0.70  cnf(c_0_123, negated_conjecture, (k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k2_tops_1(esk1_0,esk2_0)))=k4_subset_1(esk2_0,X1,k2_tops_1(esk1_0,esk2_0))|k2_pre_topc(esk1_0,esk2_0)=esk2_0|~m1_subset_1(X1,k1_zfmisc_1(esk2_0))), inference(spm,[status(thm)],[c_0_114, c_0_118])).
% 0.47/0.70  cnf(c_0_124, negated_conjecture, (k3_tarski(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,k2_tops_1(esk1_0,esk2_0)))=k2_pre_topc(esk1_0,esk2_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119, c_0_70]), c_0_120])).
% 0.47/0.70  cnf(c_0_125, plain, (v4_pre_topc(k2_pre_topc(X1,X2),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_121])).
% 0.47/0.70  cnf(c_0_126, negated_conjecture, (v2_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.47/0.70  cnf(c_0_127, negated_conjecture, (k4_subset_1(esk2_0,esk2_0,k2_tops_1(esk1_0,esk2_0))=esk2_0|k2_pre_topc(esk1_0,esk2_0)=esk2_0), inference(spm,[status(thm)],[c_0_122, c_0_113])).
% 0.47/0.70  cnf(c_0_128, negated_conjecture, (k4_subset_1(esk2_0,esk2_0,k2_tops_1(esk1_0,esk2_0))=k2_pre_topc(esk1_0,esk2_0)|k2_pre_topc(esk1_0,esk2_0)=esk2_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_123, c_0_64]), c_0_124])).
% 0.47/0.70  fof(c_0_129, plain, ![X75, X76]:(~l1_pre_topc(X75)|(~m1_subset_1(X76,k1_zfmisc_1(u1_struct_0(X75)))|k2_tops_1(X75,X76)=k7_subset_1(u1_struct_0(X75),k2_pre_topc(X75,X76),k1_tops_1(X75,X76)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l78_tops_1])])])).
% 0.47/0.70  cnf(c_0_130, negated_conjecture, (~v4_pre_topc(esk2_0,esk1_0)|k2_tops_1(esk1_0,esk2_0)!=k7_subset_1(u1_struct_0(esk1_0),esk2_0,k1_tops_1(esk1_0,esk2_0))), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.47/0.70  cnf(c_0_131, negated_conjecture, (v4_pre_topc(k2_pre_topc(esk1_0,esk2_0),esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_125, c_0_70]), c_0_126]), c_0_71])])).
% 0.47/0.70  cnf(c_0_132, negated_conjecture, (k2_pre_topc(esk1_0,esk2_0)=esk2_0), inference(spm,[status(thm)],[c_0_127, c_0_128])).
% 0.47/0.70  cnf(c_0_133, plain, (k2_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k1_tops_1(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_129])).
% 0.47/0.70  cnf(c_0_134, negated_conjecture, (k3_subset_1(esk2_0,k1_tops_1(esk1_0,esk2_0))!=k2_tops_1(esk1_0,esk2_0)|~v4_pre_topc(esk2_0,esk1_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_130, c_0_103]), c_0_104])).
% 0.47/0.70  cnf(c_0_135, negated_conjecture, (v4_pre_topc(esk2_0,esk1_0)), inference(rw,[status(thm)],[c_0_131, c_0_132])).
% 0.47/0.70  cnf(c_0_136, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),k1_tops_1(esk1_0,esk2_0))=k2_tops_1(esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_133, c_0_70]), c_0_71])])).
% 0.47/0.70  cnf(c_0_137, negated_conjecture, (k3_subset_1(esk2_0,k1_tops_1(esk1_0,esk2_0))!=k2_tops_1(esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_134, c_0_135])])).
% 0.47/0.70  cnf(c_0_138, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_136, c_0_132]), c_0_103]), c_0_104]), c_0_137]), ['proof']).
% 0.47/0.70  # SZS output end CNFRefutation
% 0.47/0.70  # Proof object total steps             : 139
% 0.47/0.70  # Proof object clause steps            : 82
% 0.47/0.70  # Proof object formula steps           : 57
% 0.47/0.70  # Proof object conjectures             : 32
% 0.47/0.70  # Proof object clause conjectures      : 29
% 0.47/0.70  # Proof object formula conjectures     : 3
% 0.47/0.70  # Proof object initial clauses used    : 32
% 0.47/0.70  # Proof object initial formulas used   : 28
% 0.47/0.70  # Proof object generating inferences   : 30
% 0.47/0.70  # Proof object simplifying inferences  : 71
% 0.47/0.70  # Training examples: 0 positive, 0 negative
% 0.47/0.70  # Parsed axioms                        : 29
% 0.47/0.70  # Removed by relevancy pruning/SinE    : 0
% 0.47/0.70  # Initial clauses                      : 38
% 0.47/0.70  # Removed in clause preprocessing      : 10
% 0.47/0.70  # Initial clauses in saturation        : 28
% 0.47/0.70  # Processed clauses                    : 2083
% 0.47/0.70  # ...of these trivial                  : 227
% 0.47/0.70  # ...subsumed                          : 581
% 0.47/0.70  # ...remaining for further processing  : 1274
% 0.47/0.70  # Other redundant clauses eliminated   : 8
% 0.47/0.70  # Clauses deleted for lack of memory   : 0
% 0.47/0.70  # Backward-subsumed                    : 2
% 0.47/0.70  # Backward-rewritten                   : 220
% 0.47/0.70  # Generated clauses                    : 20538
% 0.47/0.70  # ...of the previous two non-trivial   : 17944
% 0.47/0.70  # Contextual simplify-reflections      : 0
% 0.47/0.70  # Paramodulations                      : 20530
% 0.47/0.70  # Factorizations                       : 0
% 0.47/0.70  # Equation resolutions                 : 8
% 0.47/0.70  # Propositional unsat checks           : 0
% 0.47/0.70  #    Propositional check models        : 0
% 0.47/0.70  #    Propositional check unsatisfiable : 0
% 0.47/0.70  #    Propositional clauses             : 0
% 0.47/0.70  #    Propositional clauses after purity: 0
% 0.47/0.70  #    Propositional unsat core size     : 0
% 0.47/0.70  #    Propositional preprocessing time  : 0.000
% 0.47/0.70  #    Propositional encoding time       : 0.000
% 0.47/0.70  #    Propositional solver time         : 0.000
% 0.47/0.70  #    Success case prop preproc time    : 0.000
% 0.47/0.70  #    Success case prop encoding time   : 0.000
% 0.47/0.70  #    Success case prop solver time     : 0.000
% 0.47/0.70  # Current number of processed clauses  : 1023
% 0.47/0.70  #    Positive orientable unit clauses  : 710
% 0.47/0.70  #    Positive unorientable unit clauses: 0
% 0.47/0.70  #    Negative unit clauses             : 1
% 0.47/0.70  #    Non-unit-clauses                  : 312
% 0.47/0.70  # Current number of unprocessed clauses: 15732
% 0.47/0.70  # ...number of literals in the above   : 17438
% 0.47/0.70  # Current number of archived formulas  : 0
% 0.47/0.70  # Current number of archived clauses   : 259
% 0.47/0.70  # Clause-clause subsumption calls (NU) : 7711
% 0.47/0.70  # Rec. Clause-clause subsumption calls : 7155
% 0.47/0.70  # Non-unit clause-clause subsumptions  : 563
% 0.47/0.70  # Unit Clause-clause subsumption calls : 2930
% 0.47/0.70  # Rewrite failures with RHS unbound    : 21
% 0.47/0.70  # BW rewrite match attempts            : 11204
% 0.47/0.70  # BW rewrite match successes           : 71
% 0.47/0.70  # Condensation attempts                : 0
% 0.47/0.70  # Condensation successes               : 0
% 0.47/0.70  # Termbank termtop insertions          : 1112574
% 0.47/0.70  
% 0.47/0.70  # -------------------------------------------------
% 0.47/0.70  # User time                : 0.350 s
% 0.47/0.70  # System time              : 0.017 s
% 0.47/0.70  # Total time               : 0.368 s
% 0.47/0.70  # Maximum resident set size: 1600 pages
%------------------------------------------------------------------------------
