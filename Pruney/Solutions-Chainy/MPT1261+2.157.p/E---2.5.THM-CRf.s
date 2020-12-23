%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:11:50 EST 2020

% Result     : Theorem 0.91s
% Output     : CNFRefutation 0.91s
% Verified   : 
% Statistics : Number of formulae       :  132 (1524 expanded)
%              Number of clauses        :   89 ( 708 expanded)
%              Number of leaves         :   21 ( 386 expanded)
%              Depth                    :   20
%              Number of atoms          :  307 (3143 expanded)
%              Number of equality atoms :   81 (1106 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(redefinition_k7_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k7_subset_1(X1,X2,X3) = k4_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(t77_tops_1,conjecture,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v4_pre_topc(X2,X1)
          <=> k2_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),X2,k1_tops_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tops_1)).

fof(involutiveness_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,k3_subset_1(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(dt_k2_subset_1,axiom,(
    ! [X1] : m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(redefinition_k4_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => k4_subset_1(X1,X2,X3) = k2_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(t65_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k2_pre_topc(X1,X2) = k4_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

fof(t69_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v4_pre_topc(X2,X1)
           => r1_tarski(k2_tops_1(X1,X2),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_tops_1)).

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

fof(c_0_21,plain,(
    ! [X14,X15] : r1_tarski(k4_xboole_0(X14,X15),X14) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

fof(c_0_22,plain,(
    ! [X6,X7] : k4_xboole_0(X6,X7) = k5_xboole_0(X6,k3_xboole_0(X6,X7)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_23,plain,(
    ! [X30,X31,X32] :
      ( ~ m1_subset_1(X31,k1_zfmisc_1(X30))
      | k7_subset_1(X30,X31,X32) = k4_xboole_0(X31,X32) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).

cnf(c_0_24,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_25,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_26,plain,
    ( k7_subset_1(X2,X1,X3) = k4_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_27,plain,(
    ! [X22,X23] :
      ( ~ m1_subset_1(X23,k1_zfmisc_1(X22))
      | k3_subset_1(X22,X23) = k4_xboole_0(X22,X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

fof(c_0_28,plain,(
    ! [X34,X35] :
      ( ( ~ m1_subset_1(X34,k1_zfmisc_1(X35))
        | r1_tarski(X34,X35) )
      & ( ~ r1_tarski(X34,X35)
        | m1_subset_1(X34,k1_zfmisc_1(X35)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_29,plain,(
    ! [X9,X10,X11] :
      ( ~ r1_tarski(X9,X10)
      | ~ r1_tarski(X10,X11)
      | r1_tarski(X9,X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

fof(c_0_30,negated_conjecture,(
    ~ ! [X1] :
        ( ( v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( v4_pre_topc(X2,X1)
            <=> k2_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),X2,k1_tops_1(X1,X2)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t77_tops_1])).

cnf(c_0_31,plain,
    ( r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X1) ),
    inference(rw,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_32,plain,
    ( k7_subset_1(X2,X1,X3) = k5_xboole_0(X1,k3_xboole_0(X1,X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_26,c_0_25])).

cnf(c_0_33,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_34,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_35,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_36,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_37,negated_conjecture,
    ( v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & ( ~ v4_pre_topc(esk2_0,esk1_0)
      | k2_tops_1(esk1_0,esk2_0) != k7_subset_1(u1_struct_0(esk1_0),esk2_0,k1_tops_1(esk1_0,esk2_0)) )
    & ( v4_pre_topc(esk2_0,esk1_0)
      | k2_tops_1(esk1_0,esk2_0) = k7_subset_1(u1_struct_0(esk1_0),esk2_0,k1_tops_1(esk1_0,esk2_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_30])])])).

cnf(c_0_38,plain,
    ( r1_tarski(k7_subset_1(X1,X2,X3),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

fof(c_0_39,plain,(
    ! [X25,X26] :
      ( ~ m1_subset_1(X26,k1_zfmisc_1(X25))
      | k3_subset_1(X25,k3_subset_1(X25,X26)) = X26 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).

cnf(c_0_40,plain,
    ( k3_subset_1(X2,X1) = k5_xboole_0(X2,k3_xboole_0(X2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_33,c_0_25])).

cnf(c_0_41,plain,
    ( m1_subset_1(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_31])).

cnf(c_0_42,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_43,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_44,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ r1_tarski(X1,k7_subset_1(X3,X2,X4)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_38])).

cnf(c_0_45,plain,
    ( k3_subset_1(X2,k3_subset_1(X2,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_46,plain,
    ( k7_subset_1(X1,X2,X3) = k3_subset_1(X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_32])).

cnf(c_0_47,plain,
    ( m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_40])).

fof(c_0_48,plain,(
    ! [X24] : m1_subset_1(k2_subset_1(X24),k1_zfmisc_1(X24)) ),
    inference(variable_rename,[status(thm)],[dt_k2_subset_1])).

fof(c_0_49,plain,(
    ! [X21] : k2_subset_1(X21) = X21 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

fof(c_0_50,plain,(
    ! [X19,X20] : k2_xboole_0(X19,X20) = k5_xboole_0(X19,k4_xboole_0(X20,X19)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

cnf(c_0_51,negated_conjecture,
    ( r1_tarski(X1,u1_struct_0(esk1_0))
    | ~ r1_tarski(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

fof(c_0_52,plain,(
    ! [X4,X5] :
      ( ( r1_tarski(X4,X5)
        | X4 != X5 )
      & ( r1_tarski(X5,X4)
        | X4 != X5 )
      & ( ~ r1_tarski(X4,X5)
        | ~ r1_tarski(X5,X4)
        | X4 = X5 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_53,plain,
    ( r1_tarski(k7_subset_1(X1,k7_subset_1(X2,X3,X4),X5),X3)
    | ~ m1_subset_1(k7_subset_1(X2,X3,X4),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_38])).

cnf(c_0_54,plain,
    ( k7_subset_1(X1,X2,k3_subset_1(X2,X3)) = X3
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_47])).

cnf(c_0_55,plain,
    ( m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_56,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

fof(c_0_57,plain,(
    ! [X8] : k2_xboole_0(X8,k1_xboole_0) = X8 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

cnf(c_0_58,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

fof(c_0_59,plain,(
    ! [X16] : k4_xboole_0(X16,k1_xboole_0) = X16 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

fof(c_0_60,plain,(
    ! [X27,X28,X29] :
      ( ~ m1_subset_1(X28,k1_zfmisc_1(X27))
      | ~ m1_subset_1(X29,k1_zfmisc_1(X27))
      | k4_subset_1(X27,X28,X29) = k2_xboole_0(X28,X29) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).

cnf(c_0_61,negated_conjecture,
    ( r1_tarski(X1,u1_struct_0(esk1_0))
    | ~ r1_tarski(X2,esk2_0)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_35,c_0_51])).

cnf(c_0_62,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_63,negated_conjecture,
    ( v4_pre_topc(esk2_0,esk1_0)
    | k2_tops_1(esk1_0,esk2_0) = k7_subset_1(u1_struct_0(esk1_0),esk2_0,k1_tops_1(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_64,plain,
    ( k7_subset_1(X1,X2,X3) = k7_subset_1(X4,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X4)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_32])).

cnf(c_0_65,plain,
    ( r1_tarski(k7_subset_1(X1,X2,X3),X4)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X4)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_66,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_55,c_0_56])).

fof(c_0_67,plain,(
    ! [X12,X13] :
      ( ~ r1_tarski(X12,X13)
      | k3_xboole_0(X12,X13) = X12 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_68,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_69,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(rw,[status(thm)],[c_0_58,c_0_25])).

cnf(c_0_70,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

fof(c_0_71,plain,(
    ! [X33] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X33)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

cnf(c_0_72,plain,
    ( k4_subset_1(X2,X1,X3) = k2_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_73,negated_conjecture,
    ( r1_tarski(X1,u1_struct_0(esk1_0))
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,k7_subset_1(X2,esk2_0,X3)) ),
    inference(spm,[status(thm)],[c_0_61,c_0_38])).

cnf(c_0_74,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_62])).

cnf(c_0_75,negated_conjecture,
    ( k7_subset_1(X1,esk2_0,k1_tops_1(esk1_0,esk2_0)) = k2_tops_1(esk1_0,esk2_0)
    | v4_pre_topc(esk2_0,esk1_0)
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_43])])).

cnf(c_0_76,plain,
    ( r1_tarski(k7_subset_1(X1,X1,X2),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X4))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_77,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_78,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1))) = X1 ),
    inference(rw,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_79,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0)) = X1 ),
    inference(rw,[status(thm)],[c_0_70,c_0_25])).

cnf(c_0_80,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

fof(c_0_81,plain,(
    ! [X43,X44] :
      ( ~ l1_pre_topc(X43)
      | ~ m1_subset_1(X44,k1_zfmisc_1(u1_struct_0(X43)))
      | k2_pre_topc(X43,X44) = k4_subset_1(u1_struct_0(X43),X44,k2_tops_1(X43,X44)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_tops_1])])])).

cnf(c_0_82,plain,
    ( k4_subset_1(X2,X1,X3) = k5_xboole_0(X1,k5_xboole_0(X3,k3_xboole_0(X3,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_72,c_0_69])).

cnf(c_0_83,negated_conjecture,
    ( r1_tarski(k7_subset_1(X1,esk2_0,X2),u1_struct_0(esk1_0))
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_84,negated_conjecture,
    ( k7_subset_1(esk2_0,esk2_0,k1_tops_1(esk1_0,esk2_0)) = k2_tops_1(esk1_0,esk2_0)
    | v4_pre_topc(esk2_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_75,c_0_66])).

cnf(c_0_85,plain,
    ( r1_tarski(k7_subset_1(X1,X1,X2),X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_76,c_0_66])).

cnf(c_0_86,plain,
    ( k5_xboole_0(X1,X1) = k3_subset_1(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_40,c_0_77])).

cnf(c_0_87,plain,
    ( k5_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_78,c_0_79])).

cnf(c_0_88,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_80])).

cnf(c_0_89,plain,
    ( k2_pre_topc(X1,X2) = k4_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_81])).

cnf(c_0_90,plain,
    ( k4_subset_1(X1,X2,X3) = k4_subset_1(X4,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X4))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X4)) ),
    inference(spm,[status(thm)],[c_0_82,c_0_82])).

cnf(c_0_91,negated_conjecture,
    ( v4_pre_topc(esk2_0,esk1_0)
    | r1_tarski(k2_tops_1(esk1_0,esk2_0),u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_84]),c_0_66])])).

cnf(c_0_92,plain,
    ( m1_subset_1(k7_subset_1(X1,X1,X2),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_85])).

fof(c_0_93,plain,(
    ! [X45,X46] :
      ( ~ l1_pre_topc(X45)
      | ~ m1_subset_1(X46,k1_zfmisc_1(u1_struct_0(X45)))
      | ~ v4_pre_topc(X46,X45)
      | r1_tarski(k2_tops_1(X45,X46),X46) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t69_tops_1])])])).

cnf(c_0_94,plain,
    ( k5_xboole_0(X1,X1) = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_tarski(X1,k3_subset_1(X1,X2)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_86]),c_0_47])).

cnf(c_0_95,plain,
    ( k3_subset_1(X1,k1_xboole_0) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_40]),c_0_80])])).

cnf(c_0_96,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1
    | ~ r1_tarski(k1_xboole_0,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_77]),c_0_87])).

cnf(c_0_97,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_88,c_0_74])).

cnf(c_0_98,plain,
    ( k4_subset_1(X1,X2,k2_tops_1(X3,X2)) = k2_pre_topc(X3,X2)
    | ~ l1_pre_topc(X3)
    | ~ m1_subset_1(k2_tops_1(X3,X2),k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(k2_tops_1(X3,X2),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_89,c_0_90])).

cnf(c_0_99,negated_conjecture,
    ( v4_pre_topc(esk2_0,esk1_0)
    | m1_subset_1(k2_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_34,c_0_91])).

cnf(c_0_100,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_101,negated_conjecture,
    ( v4_pre_topc(esk2_0,esk1_0)
    | m1_subset_1(k2_tops_1(esk1_0,esk2_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_92,c_0_84])).

cnf(c_0_102,plain,
    ( r1_tarski(k2_tops_1(X1,X2),X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_93])).

cnf(c_0_103,plain,
    ( k4_subset_1(X1,X2,X3) = k5_xboole_0(X2,k5_xboole_0(X3,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_82,c_0_77])).

cnf(c_0_104,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_95]),c_0_80]),c_0_74])])).

cnf(c_0_105,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_96,c_0_97])])).

cnf(c_0_106,negated_conjecture,
    ( k4_subset_1(X1,esk2_0,k2_tops_1(esk1_0,esk2_0)) = k2_pre_topc(esk1_0,esk2_0)
    | v4_pre_topc(esk2_0,esk1_0)
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(X1)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_99]),c_0_100]),c_0_43])]),c_0_101])).

cnf(c_0_107,negated_conjecture,
    ( v4_pre_topc(esk2_0,esk1_0)
    | r1_tarski(k2_tops_1(esk1_0,esk2_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_63]),c_0_43])])).

cnf(c_0_108,negated_conjecture,
    ( r1_tarski(X1,u1_struct_0(esk1_0))
    | ~ v4_pre_topc(esk2_0,X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r1_tarski(X1,k2_tops_1(X2,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_61,c_0_102])).

fof(c_0_109,plain,(
    ! [X39,X40] :
      ( ~ v2_pre_topc(X39)
      | ~ l1_pre_topc(X39)
      | ~ m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X39)))
      | v4_pre_topc(k2_pre_topc(X39,X40),X39) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_tops_1])])).

cnf(c_0_110,plain,
    ( k4_subset_1(X1,X2,X3) = X2
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_tarski(X3,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_103,c_0_104]),c_0_105])).

cnf(c_0_111,negated_conjecture,
    ( k4_subset_1(esk2_0,esk2_0,k2_tops_1(esk1_0,esk2_0)) = k2_pre_topc(esk1_0,esk2_0)
    | v4_pre_topc(esk2_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_106,c_0_66])).

cnf(c_0_112,negated_conjecture,
    ( v4_pre_topc(esk2_0,esk1_0)
    | m1_subset_1(k2_tops_1(esk1_0,esk2_0),k1_zfmisc_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_107])).

cnf(c_0_113,plain,
    ( k4_subset_1(X1,X2,X3) = k5_xboole_0(X2,k7_subset_1(X4,X3,X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X4)) ),
    inference(spm,[status(thm)],[c_0_82,c_0_32])).

cnf(c_0_114,negated_conjecture,
    ( r1_tarski(k2_tops_1(X1,esk2_0),u1_struct_0(esk1_0))
    | ~ v4_pre_topc(esk2_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_108,c_0_74])).

cnf(c_0_115,plain,
    ( v4_pre_topc(k2_pre_topc(X1,X2),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_109])).

cnf(c_0_116,negated_conjecture,
    ( k2_pre_topc(esk1_0,esk2_0) = esk2_0
    | v4_pre_topc(esk2_0,esk1_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110,c_0_111]),c_0_66])]),c_0_36]),c_0_112])).

cnf(c_0_117,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_118,plain,
    ( k5_xboole_0(X1,k7_subset_1(X2,k2_tops_1(X3,X1),X1)) = k2_pre_topc(X3,X1)
    | ~ l1_pre_topc(X3)
    | ~ m1_subset_1(k2_tops_1(X3,X1),k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(k2_tops_1(X3,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X3))) ),
    inference(spm,[status(thm)],[c_0_89,c_0_113])).

cnf(c_0_119,negated_conjecture,
    ( m1_subset_1(k2_tops_1(X1,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ v4_pre_topc(esk2_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_34,c_0_114])).

cnf(c_0_120,negated_conjecture,
    ( v4_pre_topc(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115,c_0_116]),c_0_100]),c_0_117]),c_0_43])])).

cnf(c_0_121,plain,
    ( k7_subset_1(X1,X2,X3) = k5_xboole_0(X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_tarski(X2,X3) ),
    inference(spm,[status(thm)],[c_0_32,c_0_77])).

cnf(c_0_122,negated_conjecture,
    ( k5_xboole_0(esk2_0,k7_subset_1(X1,k2_tops_1(esk1_0,esk2_0),esk2_0)) = k2_pre_topc(esk1_0,esk2_0)
    | ~ m1_subset_1(k2_tops_1(esk1_0,esk2_0),k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_118,c_0_119]),c_0_100]),c_0_43])]),c_0_120])])).

cnf(c_0_123,plain,
    ( k7_subset_1(X1,X2,X3) = k1_xboole_0
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_tarski(X2,X3) ),
    inference(rw,[status(thm)],[c_0_121,c_0_104])).

cnf(c_0_124,negated_conjecture,
    ( k2_pre_topc(esk1_0,esk2_0) = esk2_0
    | ~ m1_subset_1(k2_tops_1(esk1_0,esk2_0),k1_zfmisc_1(X1))
    | ~ r1_tarski(k2_tops_1(esk1_0,esk2_0),esk2_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_122,c_0_123]),c_0_105])).

fof(c_0_125,plain,(
    ! [X41,X42] :
      ( ~ l1_pre_topc(X41)
      | ~ m1_subset_1(X42,k1_zfmisc_1(u1_struct_0(X41)))
      | k2_tops_1(X41,X42) = k7_subset_1(u1_struct_0(X41),k2_pre_topc(X41,X42),k1_tops_1(X41,X42)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l78_tops_1])])])).

cnf(c_0_126,negated_conjecture,
    ( k2_pre_topc(esk1_0,esk2_0) = esk2_0
    | ~ m1_subset_1(k2_tops_1(esk1_0,esk2_0),k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_124,c_0_102]),c_0_120]),c_0_100]),c_0_43])])).

cnf(c_0_127,negated_conjecture,
    ( ~ v4_pre_topc(esk2_0,esk1_0)
    | k2_tops_1(esk1_0,esk2_0) != k7_subset_1(u1_struct_0(esk1_0),esk2_0,k1_tops_1(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_128,plain,
    ( k2_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k1_tops_1(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_125])).

cnf(c_0_129,negated_conjecture,
    ( k2_pre_topc(esk1_0,esk2_0) = esk2_0 ),
    inference(spm,[status(thm)],[c_0_126,c_0_66])).

cnf(c_0_130,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),esk2_0,k1_tops_1(esk1_0,esk2_0)) != k2_tops_1(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_127,c_0_120])])).

cnf(c_0_131,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_128,c_0_129]),c_0_100]),c_0_43])]),c_0_130]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:20:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.91/1.14  # AutoSched0-Mode selected heuristic G_E___302_C18_F1_URBAN_RG_S04BN
% 0.91/1.14  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.91/1.14  #
% 0.91/1.14  # Preprocessing time       : 0.028 s
% 0.91/1.14  
% 0.91/1.14  # Proof found!
% 0.91/1.14  # SZS status Theorem
% 0.91/1.14  # SZS output start CNFRefutation
% 0.91/1.14  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.91/1.14  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.91/1.14  fof(redefinition_k7_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k7_subset_1(X1,X2,X3)=k4_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 0.91/1.14  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 0.91/1.14  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.91/1.14  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 0.91/1.14  fof(t77_tops_1, conjecture, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v4_pre_topc(X2,X1)<=>k2_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),X2,k1_tops_1(X1,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_tops_1)).
% 0.91/1.14  fof(involutiveness_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,k3_subset_1(X1,X2))=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 0.91/1.14  fof(dt_k2_subset_1, axiom, ![X1]:m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 0.91/1.14  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 0.91/1.14  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.91/1.14  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.91/1.14  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 0.91/1.14  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 0.91/1.14  fof(redefinition_k4_subset_1, axiom, ![X1, X2, X3]:((m1_subset_1(X2,k1_zfmisc_1(X1))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>k4_subset_1(X1,X2,X3)=k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 0.91/1.14  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.91/1.14  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 0.91/1.14  fof(t65_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k2_pre_topc(X1,X2)=k4_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tops_1)).
% 0.91/1.14  fof(t69_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v4_pre_topc(X2,X1)=>r1_tarski(k2_tops_1(X1,X2),X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_tops_1)).
% 0.91/1.14  fof(fc1_tops_1, axiom, ![X1, X2]:(((v2_pre_topc(X1)&l1_pre_topc(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>v4_pre_topc(k2_pre_topc(X1,X2),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_tops_1)).
% 0.91/1.14  fof(l78_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k2_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k1_tops_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l78_tops_1)).
% 0.91/1.14  fof(c_0_21, plain, ![X14, X15]:r1_tarski(k4_xboole_0(X14,X15),X14), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.91/1.14  fof(c_0_22, plain, ![X6, X7]:k4_xboole_0(X6,X7)=k5_xboole_0(X6,k3_xboole_0(X6,X7)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.91/1.14  fof(c_0_23, plain, ![X30, X31, X32]:(~m1_subset_1(X31,k1_zfmisc_1(X30))|k7_subset_1(X30,X31,X32)=k4_xboole_0(X31,X32)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).
% 0.91/1.14  cnf(c_0_24, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.91/1.14  cnf(c_0_25, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.91/1.14  cnf(c_0_26, plain, (k7_subset_1(X2,X1,X3)=k4_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.91/1.14  fof(c_0_27, plain, ![X22, X23]:(~m1_subset_1(X23,k1_zfmisc_1(X22))|k3_subset_1(X22,X23)=k4_xboole_0(X22,X23)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 0.91/1.14  fof(c_0_28, plain, ![X34, X35]:((~m1_subset_1(X34,k1_zfmisc_1(X35))|r1_tarski(X34,X35))&(~r1_tarski(X34,X35)|m1_subset_1(X34,k1_zfmisc_1(X35)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.91/1.14  fof(c_0_29, plain, ![X9, X10, X11]:(~r1_tarski(X9,X10)|~r1_tarski(X10,X11)|r1_tarski(X9,X11)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 0.91/1.14  fof(c_0_30, negated_conjecture, ~(![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v4_pre_topc(X2,X1)<=>k2_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),X2,k1_tops_1(X1,X2)))))), inference(assume_negation,[status(cth)],[t77_tops_1])).
% 0.91/1.14  cnf(c_0_31, plain, (r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X1)), inference(rw,[status(thm)],[c_0_24, c_0_25])).
% 0.91/1.14  cnf(c_0_32, plain, (k7_subset_1(X2,X1,X3)=k5_xboole_0(X1,k3_xboole_0(X1,X3))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_26, c_0_25])).
% 0.91/1.14  cnf(c_0_33, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.91/1.14  cnf(c_0_34, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.91/1.14  cnf(c_0_35, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.91/1.14  cnf(c_0_36, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.91/1.14  fof(c_0_37, negated_conjecture, ((v2_pre_topc(esk1_0)&l1_pre_topc(esk1_0))&(m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&((~v4_pre_topc(esk2_0,esk1_0)|k2_tops_1(esk1_0,esk2_0)!=k7_subset_1(u1_struct_0(esk1_0),esk2_0,k1_tops_1(esk1_0,esk2_0)))&(v4_pre_topc(esk2_0,esk1_0)|k2_tops_1(esk1_0,esk2_0)=k7_subset_1(u1_struct_0(esk1_0),esk2_0,k1_tops_1(esk1_0,esk2_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_30])])])).
% 0.91/1.14  cnf(c_0_38, plain, (r1_tarski(k7_subset_1(X1,X2,X3),X2)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.91/1.14  fof(c_0_39, plain, ![X25, X26]:(~m1_subset_1(X26,k1_zfmisc_1(X25))|k3_subset_1(X25,k3_subset_1(X25,X26))=X26), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).
% 0.91/1.14  cnf(c_0_40, plain, (k3_subset_1(X2,X1)=k5_xboole_0(X2,k3_xboole_0(X2,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_33, c_0_25])).
% 0.91/1.14  cnf(c_0_41, plain, (m1_subset_1(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_34, c_0_31])).
% 0.91/1.14  cnf(c_0_42, plain, (r1_tarski(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.91/1.14  cnf(c_0_43, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.91/1.14  cnf(c_0_44, plain, (r1_tarski(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~r1_tarski(X1,k7_subset_1(X3,X2,X4))), inference(spm,[status(thm)],[c_0_35, c_0_38])).
% 0.91/1.14  cnf(c_0_45, plain, (k3_subset_1(X2,k3_subset_1(X2,X1))=X1|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.91/1.14  cnf(c_0_46, plain, (k7_subset_1(X1,X2,X3)=k3_subset_1(X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(X2))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_40, c_0_32])).
% 0.91/1.14  cnf(c_0_47, plain, (m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_41, c_0_40])).
% 0.91/1.14  fof(c_0_48, plain, ![X24]:m1_subset_1(k2_subset_1(X24),k1_zfmisc_1(X24)), inference(variable_rename,[status(thm)],[dt_k2_subset_1])).
% 0.91/1.14  fof(c_0_49, plain, ![X21]:k2_subset_1(X21)=X21, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 0.91/1.14  fof(c_0_50, plain, ![X19, X20]:k2_xboole_0(X19,X20)=k5_xboole_0(X19,k4_xboole_0(X20,X19)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.91/1.14  cnf(c_0_51, negated_conjecture, (r1_tarski(X1,u1_struct_0(esk1_0))|~r1_tarski(X1,esk2_0)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.91/1.14  fof(c_0_52, plain, ![X4, X5]:(((r1_tarski(X4,X5)|X4!=X5)&(r1_tarski(X5,X4)|X4!=X5))&(~r1_tarski(X4,X5)|~r1_tarski(X5,X4)|X4=X5)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.91/1.14  cnf(c_0_53, plain, (r1_tarski(k7_subset_1(X1,k7_subset_1(X2,X3,X4),X5),X3)|~m1_subset_1(k7_subset_1(X2,X3,X4),k1_zfmisc_1(X1))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_44, c_0_38])).
% 0.91/1.14  cnf(c_0_54, plain, (k7_subset_1(X1,X2,k3_subset_1(X2,X3))=X3|~m1_subset_1(X3,k1_zfmisc_1(X2))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_47])).
% 0.91/1.14  cnf(c_0_55, plain, (m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.91/1.14  cnf(c_0_56, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.91/1.14  fof(c_0_57, plain, ![X8]:k2_xboole_0(X8,k1_xboole_0)=X8, inference(variable_rename,[status(thm)],[t1_boole])).
% 0.91/1.14  cnf(c_0_58, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.91/1.14  fof(c_0_59, plain, ![X16]:k4_xboole_0(X16,k1_xboole_0)=X16, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.91/1.14  fof(c_0_60, plain, ![X27, X28, X29]:(~m1_subset_1(X28,k1_zfmisc_1(X27))|~m1_subset_1(X29,k1_zfmisc_1(X27))|k4_subset_1(X27,X28,X29)=k2_xboole_0(X28,X29)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).
% 0.91/1.14  cnf(c_0_61, negated_conjecture, (r1_tarski(X1,u1_struct_0(esk1_0))|~r1_tarski(X2,esk2_0)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_35, c_0_51])).
% 0.91/1.14  cnf(c_0_62, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.91/1.14  cnf(c_0_63, negated_conjecture, (v4_pre_topc(esk2_0,esk1_0)|k2_tops_1(esk1_0,esk2_0)=k7_subset_1(u1_struct_0(esk1_0),esk2_0,k1_tops_1(esk1_0,esk2_0))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.91/1.14  cnf(c_0_64, plain, (k7_subset_1(X1,X2,X3)=k7_subset_1(X4,X2,X3)|~m1_subset_1(X2,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X4))), inference(spm,[status(thm)],[c_0_32, c_0_32])).
% 0.91/1.14  cnf(c_0_65, plain, (r1_tarski(k7_subset_1(X1,X2,X3),X4)|~m1_subset_1(X2,k1_zfmisc_1(X1))|~m1_subset_1(X4,k1_zfmisc_1(X5))|~m1_subset_1(X2,k1_zfmisc_1(X4))), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.91/1.14  cnf(c_0_66, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_55, c_0_56])).
% 0.91/1.14  fof(c_0_67, plain, ![X12, X13]:(~r1_tarski(X12,X13)|k3_xboole_0(X12,X13)=X12), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.91/1.14  cnf(c_0_68, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.91/1.14  cnf(c_0_69, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))), inference(rw,[status(thm)],[c_0_58, c_0_25])).
% 0.91/1.14  cnf(c_0_70, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.91/1.14  fof(c_0_71, plain, ![X33]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X33)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.91/1.14  cnf(c_0_72, plain, (k4_subset_1(X2,X1,X3)=k2_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.91/1.14  cnf(c_0_73, negated_conjecture, (r1_tarski(X1,u1_struct_0(esk1_0))|~m1_subset_1(esk2_0,k1_zfmisc_1(X2))|~r1_tarski(X1,k7_subset_1(X2,esk2_0,X3))), inference(spm,[status(thm)],[c_0_61, c_0_38])).
% 0.91/1.14  cnf(c_0_74, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_62])).
% 0.91/1.14  cnf(c_0_75, negated_conjecture, (k7_subset_1(X1,esk2_0,k1_tops_1(esk1_0,esk2_0))=k2_tops_1(esk1_0,esk2_0)|v4_pre_topc(esk2_0,esk1_0)|~m1_subset_1(esk2_0,k1_zfmisc_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_43])])).
% 0.91/1.14  cnf(c_0_76, plain, (r1_tarski(k7_subset_1(X1,X1,X2),X3)|~m1_subset_1(X3,k1_zfmisc_1(X4))|~m1_subset_1(X1,k1_zfmisc_1(X3))), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 0.91/1.14  cnf(c_0_77, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.91/1.14  cnf(c_0_78, plain, (k5_xboole_0(X1,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1)))=X1), inference(rw,[status(thm)],[c_0_68, c_0_69])).
% 0.91/1.14  cnf(c_0_79, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0))=X1), inference(rw,[status(thm)],[c_0_70, c_0_25])).
% 0.91/1.14  cnf(c_0_80, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_71])).
% 0.91/1.14  fof(c_0_81, plain, ![X43, X44]:(~l1_pre_topc(X43)|(~m1_subset_1(X44,k1_zfmisc_1(u1_struct_0(X43)))|k2_pre_topc(X43,X44)=k4_subset_1(u1_struct_0(X43),X44,k2_tops_1(X43,X44)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_tops_1])])])).
% 0.91/1.14  cnf(c_0_82, plain, (k4_subset_1(X2,X1,X3)=k5_xboole_0(X1,k5_xboole_0(X3,k3_xboole_0(X3,X1)))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_72, c_0_69])).
% 0.91/1.14  cnf(c_0_83, negated_conjecture, (r1_tarski(k7_subset_1(X1,esk2_0,X2),u1_struct_0(esk1_0))|~m1_subset_1(esk2_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_73, c_0_74])).
% 0.91/1.14  cnf(c_0_84, negated_conjecture, (k7_subset_1(esk2_0,esk2_0,k1_tops_1(esk1_0,esk2_0))=k2_tops_1(esk1_0,esk2_0)|v4_pre_topc(esk2_0,esk1_0)), inference(spm,[status(thm)],[c_0_75, c_0_66])).
% 0.91/1.14  cnf(c_0_85, plain, (r1_tarski(k7_subset_1(X1,X1,X2),X3)|~m1_subset_1(X1,k1_zfmisc_1(X3))), inference(spm,[status(thm)],[c_0_76, c_0_66])).
% 0.91/1.14  cnf(c_0_86, plain, (k5_xboole_0(X1,X1)=k3_subset_1(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_40, c_0_77])).
% 0.91/1.14  cnf(c_0_87, plain, (k5_xboole_0(k1_xboole_0,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_78, c_0_79])).
% 0.91/1.14  cnf(c_0_88, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_42, c_0_80])).
% 0.91/1.14  cnf(c_0_89, plain, (k2_pre_topc(X1,X2)=k4_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_81])).
% 0.91/1.14  cnf(c_0_90, plain, (k4_subset_1(X1,X2,X3)=k4_subset_1(X4,X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~m1_subset_1(X3,k1_zfmisc_1(X4))|~m1_subset_1(X2,k1_zfmisc_1(X4))), inference(spm,[status(thm)],[c_0_82, c_0_82])).
% 0.91/1.14  cnf(c_0_91, negated_conjecture, (v4_pre_topc(esk2_0,esk1_0)|r1_tarski(k2_tops_1(esk1_0,esk2_0),u1_struct_0(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_84]), c_0_66])])).
% 0.91/1.14  cnf(c_0_92, plain, (m1_subset_1(k7_subset_1(X1,X1,X2),k1_zfmisc_1(X3))|~m1_subset_1(X1,k1_zfmisc_1(X3))), inference(spm,[status(thm)],[c_0_34, c_0_85])).
% 0.91/1.14  fof(c_0_93, plain, ![X45, X46]:(~l1_pre_topc(X45)|(~m1_subset_1(X46,k1_zfmisc_1(u1_struct_0(X45)))|(~v4_pre_topc(X46,X45)|r1_tarski(k2_tops_1(X45,X46),X46)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t69_tops_1])])])).
% 0.91/1.14  cnf(c_0_94, plain, (k5_xboole_0(X1,X1)=X2|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_tarski(X1,k3_subset_1(X1,X2))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_86]), c_0_47])).
% 0.91/1.14  cnf(c_0_95, plain, (k3_subset_1(X1,k1_xboole_0)=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_40]), c_0_80])])).
% 0.91/1.14  cnf(c_0_96, plain, (k5_xboole_0(X1,k1_xboole_0)=X1|~r1_tarski(k1_xboole_0,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_77]), c_0_87])).
% 0.91/1.14  cnf(c_0_97, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_88, c_0_74])).
% 0.91/1.14  cnf(c_0_98, plain, (k4_subset_1(X1,X2,k2_tops_1(X3,X2))=k2_pre_topc(X3,X2)|~l1_pre_topc(X3)|~m1_subset_1(k2_tops_1(X3,X2),k1_zfmisc_1(u1_struct_0(X3)))|~m1_subset_1(k2_tops_1(X3,X2),k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_89, c_0_90])).
% 0.91/1.14  cnf(c_0_99, negated_conjecture, (v4_pre_topc(esk2_0,esk1_0)|m1_subset_1(k2_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_34, c_0_91])).
% 0.91/1.14  cnf(c_0_100, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.91/1.14  cnf(c_0_101, negated_conjecture, (v4_pre_topc(esk2_0,esk1_0)|m1_subset_1(k2_tops_1(esk1_0,esk2_0),k1_zfmisc_1(X1))|~m1_subset_1(esk2_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_92, c_0_84])).
% 0.91/1.14  cnf(c_0_102, plain, (r1_tarski(k2_tops_1(X1,X2),X2)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v4_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_93])).
% 0.91/1.14  cnf(c_0_103, plain, (k4_subset_1(X1,X2,X3)=k5_xboole_0(X2,k5_xboole_0(X3,X3))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_82, c_0_77])).
% 0.91/1.14  cnf(c_0_104, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_95]), c_0_80]), c_0_74])])).
% 0.91/1.14  cnf(c_0_105, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_96, c_0_97])])).
% 0.91/1.14  cnf(c_0_106, negated_conjecture, (k4_subset_1(X1,esk2_0,k2_tops_1(esk1_0,esk2_0))=k2_pre_topc(esk1_0,esk2_0)|v4_pre_topc(esk2_0,esk1_0)|~m1_subset_1(esk2_0,k1_zfmisc_1(X1))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_99]), c_0_100]), c_0_43])]), c_0_101])).
% 0.91/1.14  cnf(c_0_107, negated_conjecture, (v4_pre_topc(esk2_0,esk1_0)|r1_tarski(k2_tops_1(esk1_0,esk2_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_63]), c_0_43])])).
% 0.91/1.14  cnf(c_0_108, negated_conjecture, (r1_tarski(X1,u1_struct_0(esk1_0))|~v4_pre_topc(esk2_0,X2)|~l1_pre_topc(X2)|~m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(X2)))|~r1_tarski(X1,k2_tops_1(X2,esk2_0))), inference(spm,[status(thm)],[c_0_61, c_0_102])).
% 0.91/1.14  fof(c_0_109, plain, ![X39, X40]:(~v2_pre_topc(X39)|~l1_pre_topc(X39)|~m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X39)))|v4_pre_topc(k2_pre_topc(X39,X40),X39)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_tops_1])])).
% 0.91/1.14  cnf(c_0_110, plain, (k4_subset_1(X1,X2,X3)=X2|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_tarski(X3,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_103, c_0_104]), c_0_105])).
% 0.91/1.14  cnf(c_0_111, negated_conjecture, (k4_subset_1(esk2_0,esk2_0,k2_tops_1(esk1_0,esk2_0))=k2_pre_topc(esk1_0,esk2_0)|v4_pre_topc(esk2_0,esk1_0)), inference(spm,[status(thm)],[c_0_106, c_0_66])).
% 0.91/1.14  cnf(c_0_112, negated_conjecture, (v4_pre_topc(esk2_0,esk1_0)|m1_subset_1(k2_tops_1(esk1_0,esk2_0),k1_zfmisc_1(esk2_0))), inference(spm,[status(thm)],[c_0_34, c_0_107])).
% 0.91/1.14  cnf(c_0_113, plain, (k4_subset_1(X1,X2,X3)=k5_xboole_0(X2,k7_subset_1(X4,X3,X2))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~m1_subset_1(X3,k1_zfmisc_1(X4))), inference(spm,[status(thm)],[c_0_82, c_0_32])).
% 0.91/1.14  cnf(c_0_114, negated_conjecture, (r1_tarski(k2_tops_1(X1,esk2_0),u1_struct_0(esk1_0))|~v4_pre_topc(esk2_0,X1)|~l1_pre_topc(X1)|~m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_108, c_0_74])).
% 0.91/1.14  cnf(c_0_115, plain, (v4_pre_topc(k2_pre_topc(X1,X2),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_109])).
% 0.91/1.14  cnf(c_0_116, negated_conjecture, (k2_pre_topc(esk1_0,esk2_0)=esk2_0|v4_pre_topc(esk2_0,esk1_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110, c_0_111]), c_0_66])]), c_0_36]), c_0_112])).
% 0.91/1.14  cnf(c_0_117, negated_conjecture, (v2_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.91/1.14  cnf(c_0_118, plain, (k5_xboole_0(X1,k7_subset_1(X2,k2_tops_1(X3,X1),X1))=k2_pre_topc(X3,X1)|~l1_pre_topc(X3)|~m1_subset_1(k2_tops_1(X3,X1),k1_zfmisc_1(u1_struct_0(X3)))|~m1_subset_1(k2_tops_1(X3,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X3)))), inference(spm,[status(thm)],[c_0_89, c_0_113])).
% 0.91/1.14  cnf(c_0_119, negated_conjecture, (m1_subset_1(k2_tops_1(X1,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))|~v4_pre_topc(esk2_0,X1)|~l1_pre_topc(X1)|~m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_34, c_0_114])).
% 0.91/1.14  cnf(c_0_120, negated_conjecture, (v4_pre_topc(esk2_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115, c_0_116]), c_0_100]), c_0_117]), c_0_43])])).
% 0.91/1.14  cnf(c_0_121, plain, (k7_subset_1(X1,X2,X3)=k5_xboole_0(X2,X2)|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_tarski(X2,X3)), inference(spm,[status(thm)],[c_0_32, c_0_77])).
% 0.91/1.14  cnf(c_0_122, negated_conjecture, (k5_xboole_0(esk2_0,k7_subset_1(X1,k2_tops_1(esk1_0,esk2_0),esk2_0))=k2_pre_topc(esk1_0,esk2_0)|~m1_subset_1(k2_tops_1(esk1_0,esk2_0),k1_zfmisc_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_118, c_0_119]), c_0_100]), c_0_43])]), c_0_120])])).
% 0.91/1.14  cnf(c_0_123, plain, (k7_subset_1(X1,X2,X3)=k1_xboole_0|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_tarski(X2,X3)), inference(rw,[status(thm)],[c_0_121, c_0_104])).
% 0.91/1.14  cnf(c_0_124, negated_conjecture, (k2_pre_topc(esk1_0,esk2_0)=esk2_0|~m1_subset_1(k2_tops_1(esk1_0,esk2_0),k1_zfmisc_1(X1))|~r1_tarski(k2_tops_1(esk1_0,esk2_0),esk2_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_122, c_0_123]), c_0_105])).
% 0.91/1.14  fof(c_0_125, plain, ![X41, X42]:(~l1_pre_topc(X41)|(~m1_subset_1(X42,k1_zfmisc_1(u1_struct_0(X41)))|k2_tops_1(X41,X42)=k7_subset_1(u1_struct_0(X41),k2_pre_topc(X41,X42),k1_tops_1(X41,X42)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l78_tops_1])])])).
% 0.91/1.14  cnf(c_0_126, negated_conjecture, (k2_pre_topc(esk1_0,esk2_0)=esk2_0|~m1_subset_1(k2_tops_1(esk1_0,esk2_0),k1_zfmisc_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_124, c_0_102]), c_0_120]), c_0_100]), c_0_43])])).
% 0.91/1.14  cnf(c_0_127, negated_conjecture, (~v4_pre_topc(esk2_0,esk1_0)|k2_tops_1(esk1_0,esk2_0)!=k7_subset_1(u1_struct_0(esk1_0),esk2_0,k1_tops_1(esk1_0,esk2_0))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.91/1.14  cnf(c_0_128, plain, (k2_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k1_tops_1(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_125])).
% 0.91/1.14  cnf(c_0_129, negated_conjecture, (k2_pre_topc(esk1_0,esk2_0)=esk2_0), inference(spm,[status(thm)],[c_0_126, c_0_66])).
% 0.91/1.14  cnf(c_0_130, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),esk2_0,k1_tops_1(esk1_0,esk2_0))!=k2_tops_1(esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_127, c_0_120])])).
% 0.91/1.14  cnf(c_0_131, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_128, c_0_129]), c_0_100]), c_0_43])]), c_0_130]), ['proof']).
% 0.91/1.14  # SZS output end CNFRefutation
% 0.91/1.14  # Proof object total steps             : 132
% 0.91/1.14  # Proof object clause steps            : 89
% 0.91/1.14  # Proof object formula steps           : 43
% 0.91/1.14  # Proof object conjectures             : 32
% 0.91/1.14  # Proof object clause conjectures      : 29
% 0.91/1.14  # Proof object formula conjectures     : 3
% 0.91/1.14  # Proof object initial clauses used    : 26
% 0.91/1.14  # Proof object initial formulas used   : 21
% 0.91/1.14  # Proof object generating inferences   : 50
% 0.91/1.14  # Proof object simplifying inferences  : 56
% 0.91/1.14  # Training examples: 0 positive, 0 negative
% 0.91/1.14  # Parsed axioms                        : 23
% 0.91/1.14  # Removed by relevancy pruning/SinE    : 0
% 0.91/1.14  # Initial clauses                      : 30
% 0.91/1.14  # Removed in clause preprocessing      : 3
% 0.91/1.14  # Initial clauses in saturation        : 27
% 0.91/1.14  # Processed clauses                    : 5600
% 0.91/1.14  # ...of these trivial                  : 45
% 0.91/1.14  # ...subsumed                          : 4343
% 0.91/1.14  # ...remaining for further processing  : 1212
% 0.91/1.14  # Other redundant clauses eliminated   : 2
% 0.91/1.14  # Clauses deleted for lack of memory   : 0
% 0.91/1.14  # Backward-subsumed                    : 158
% 0.91/1.14  # Backward-rewritten                   : 279
% 0.91/1.14  # Generated clauses                    : 36684
% 0.91/1.14  # ...of the previous two non-trivial   : 33265
% 0.91/1.14  # Contextual simplify-reflections      : 111
% 0.91/1.14  # Paramodulations                      : 36682
% 0.91/1.14  # Factorizations                       : 0
% 0.91/1.14  # Equation resolutions                 : 2
% 0.91/1.14  # Propositional unsat checks           : 0
% 0.91/1.14  #    Propositional check models        : 0
% 0.91/1.14  #    Propositional check unsatisfiable : 0
% 0.91/1.14  #    Propositional clauses             : 0
% 0.91/1.14  #    Propositional clauses after purity: 0
% 0.91/1.14  #    Propositional unsat core size     : 0
% 0.91/1.14  #    Propositional preprocessing time  : 0.000
% 0.91/1.14  #    Propositional encoding time       : 0.000
% 0.91/1.14  #    Propositional solver time         : 0.000
% 0.91/1.14  #    Success case prop preproc time    : 0.000
% 0.91/1.14  #    Success case prop encoding time   : 0.000
% 0.91/1.14  #    Success case prop solver time     : 0.000
% 0.91/1.14  # Current number of processed clauses  : 773
% 0.91/1.14  #    Positive orientable unit clauses  : 41
% 0.91/1.14  #    Positive unorientable unit clauses: 0
% 0.91/1.14  #    Negative unit clauses             : 4
% 0.91/1.14  #    Non-unit-clauses                  : 728
% 0.91/1.14  # Current number of unprocessed clauses: 25722
% 0.91/1.14  # ...number of literals in the above   : 125751
% 0.91/1.14  # Current number of archived formulas  : 0
% 0.91/1.14  # Current number of archived clauses   : 440
% 0.91/1.14  # Clause-clause subsumption calls (NU) : 254551
% 0.91/1.14  # Rec. Clause-clause subsumption calls : 75208
% 0.91/1.14  # Non-unit clause-clause subsumptions  : 3833
% 0.91/1.14  # Unit Clause-clause subsumption calls : 1050
% 0.91/1.14  # Rewrite failures with RHS unbound    : 0
% 0.91/1.14  # BW rewrite match attempts            : 191
% 0.91/1.14  # BW rewrite match successes           : 70
% 0.91/1.14  # Condensation attempts                : 0
% 0.91/1.14  # Condensation successes               : 0
% 0.91/1.14  # Termbank termtop insertions          : 733393
% 0.91/1.14  
% 0.91/1.14  # -------------------------------------------------
% 0.91/1.14  # User time                : 0.766 s
% 0.91/1.14  # System time              : 0.025 s
% 0.91/1.14  # Total time               : 0.791 s
% 0.91/1.14  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
