%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:11:49 EST 2020

% Result     : Theorem 3.25s
% Output     : CNFRefutation 3.25s
% Verified   : 
% Statistics : Number of formulae       :  145 (2136 expanded)
%              Number of clauses        :   98 ( 993 expanded)
%              Number of leaves         :   23 ( 548 expanded)
%              Depth                    :   22
%              Number of atoms          :  335 (4044 expanded)
%              Number of equality atoms :   84 (1533 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t77_tops_1,conjecture,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v4_pre_topc(X2,X1)
          <=> k2_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),X2,k1_tops_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tops_1)).

fof(redefinition_k7_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k7_subset_1(X1,X2,X3) = k4_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(dt_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(t25_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k4_subset_1(X1,X2,k3_subset_1(X1,X2)) = k2_subset_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(redefinition_k4_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => k4_subset_1(X1,X2,X3) = k2_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(involutiveness_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,k3_subset_1(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(dt_k2_subset_1,axiom,(
    ! [X1] : m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

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

fof(c_0_23,plain,(
    ! [X18,X19] : k2_xboole_0(X18,X19) = k5_xboole_0(X18,k4_xboole_0(X19,X18)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_24,plain,(
    ! [X6,X7] : k4_xboole_0(X6,X7) = k5_xboole_0(X6,k3_xboole_0(X6,X7)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_25,plain,(
    ! [X10] : k2_xboole_0(X10,k1_xboole_0) = X10 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

cnf(c_0_26,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_27,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_28,plain,(
    ! [X8,X9] :
      ( ~ r1_tarski(X8,X9)
      | k2_xboole_0(X8,X9) = X9 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

fof(c_0_29,plain,(
    ! [X11,X12,X13] :
      ( ~ r1_tarski(X11,X12)
      | ~ r1_tarski(X12,X13)
      | r1_tarski(X11,X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

fof(c_0_30,plain,(
    ! [X37,X38] :
      ( ( ~ m1_subset_1(X37,k1_zfmisc_1(X38))
        | r1_tarski(X37,X38) )
      & ( ~ r1_tarski(X37,X38)
        | m1_subset_1(X37,k1_zfmisc_1(X38)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_31,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_32,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(rw,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_33,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_34,plain,(
    ! [X16,X17] : r1_tarski(k4_xboole_0(X16,X17),X16) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

fof(c_0_35,negated_conjecture,(
    ~ ! [X1] :
        ( ( v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( v4_pre_topc(X2,X1)
            <=> k2_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),X2,k1_tops_1(X1,X2)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t77_tops_1])).

fof(c_0_36,plain,(
    ! [X31,X32,X33] :
      ( ~ m1_subset_1(X32,k1_zfmisc_1(X31))
      | k7_subset_1(X31,X32,X33) = k4_xboole_0(X32,X33) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).

cnf(c_0_37,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_38,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_39,plain,(
    ! [X24,X25] :
      ( ~ m1_subset_1(X25,k1_zfmisc_1(X24))
      | m1_subset_1(k3_subset_1(X24,X25),k1_zfmisc_1(X24)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).

cnf(c_0_40,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1))) = X1 ),
    inference(rw,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_41,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_33,c_0_32])).

cnf(c_0_42,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

fof(c_0_43,negated_conjecture,
    ( v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & ( ~ v4_pre_topc(esk2_0,esk1_0)
      | k2_tops_1(esk1_0,esk2_0) != k7_subset_1(u1_struct_0(esk1_0),esk2_0,k1_tops_1(esk1_0,esk2_0)) )
    & ( v4_pre_topc(esk2_0,esk1_0)
      | k2_tops_1(esk1_0,esk2_0) = k7_subset_1(u1_struct_0(esk1_0),esk2_0,k1_tops_1(esk1_0,esk2_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_35])])])).

cnf(c_0_44,plain,
    ( k7_subset_1(X2,X1,X3) = k4_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_45,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_46,plain,
    ( m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

fof(c_0_47,plain,(
    ! [X34,X35] :
      ( ~ m1_subset_1(X35,k1_zfmisc_1(X34))
      | k4_subset_1(X34,X35,k3_subset_1(X34,X35)) = k2_subset_1(X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_subset_1])])).

fof(c_0_48,plain,(
    ! [X20] : k2_subset_1(X20) = X20 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

fof(c_0_49,plain,(
    ! [X28,X29,X30] :
      ( ~ m1_subset_1(X29,k1_zfmisc_1(X28))
      | ~ m1_subset_1(X30,k1_zfmisc_1(X28))
      | k4_subset_1(X28,X29,X30) = k2_xboole_0(X29,X30) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).

cnf(c_0_50,plain,
    ( k1_xboole_0 = X1
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_51,plain,
    ( r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X1) ),
    inference(rw,[status(thm)],[c_0_42,c_0_27])).

cnf(c_0_52,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_53,plain,
    ( k7_subset_1(X2,X1,X3) = k5_xboole_0(X1,k3_xboole_0(X1,X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_44,c_0_27])).

cnf(c_0_54,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,k3_subset_1(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

fof(c_0_55,plain,(
    ! [X26,X27] :
      ( ~ m1_subset_1(X27,k1_zfmisc_1(X26))
      | k3_subset_1(X26,k3_subset_1(X26,X27)) = X27 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).

cnf(c_0_56,plain,
    ( k4_subset_1(X2,X1,k3_subset_1(X2,X1)) = k2_subset_1(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_57,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_58,plain,
    ( k4_subset_1(X2,X1,X3) = k2_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

fof(c_0_59,plain,(
    ! [X36] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X36)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

cnf(c_0_60,plain,
    ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

fof(c_0_61,plain,(
    ! [X21,X22] :
      ( ~ m1_subset_1(X22,k1_zfmisc_1(X21))
      | k3_subset_1(X21,X22) = k4_xboole_0(X21,X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

cnf(c_0_62,negated_conjecture,
    ( r1_tarski(X1,u1_struct_0(esk1_0))
    | ~ r1_tarski(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_52])).

cnf(c_0_63,plain,
    ( r1_tarski(k7_subset_1(X1,X2,X3),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_53])).

cnf(c_0_64,negated_conjecture,
    ( v4_pre_topc(esk2_0,esk1_0)
    | k2_tops_1(esk1_0,esk2_0) = k7_subset_1(u1_struct_0(esk1_0),esk2_0,k1_tops_1(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

fof(c_0_65,plain,(
    ! [X4,X5] :
      ( ( r1_tarski(X4,X5)
        | X4 != X5 )
      & ( r1_tarski(X5,X4)
        | X4 != X5 )
      & ( ~ r1_tarski(X4,X5)
        | ~ r1_tarski(X5,X4)
        | X4 = X5 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_66,plain,
    ( r1_tarski(k5_xboole_0(k3_subset_1(X1,X2),k3_xboole_0(k3_subset_1(X1,X2),X3)),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_51])).

cnf(c_0_67,plain,
    ( k3_subset_1(X2,k3_subset_1(X2,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

fof(c_0_68,plain,(
    ! [X23] : m1_subset_1(k2_subset_1(X23),k1_zfmisc_1(X23)) ),
    inference(variable_rename,[status(thm)],[dt_k2_subset_1])).

cnf(c_0_69,plain,
    ( k4_subset_1(X2,X1,k3_subset_1(X2,X1)) = X2
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_70,plain,
    ( k4_subset_1(X2,X1,X3) = k5_xboole_0(X1,k5_xboole_0(X3,k3_xboole_0(X3,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_58,c_0_32])).

cnf(c_0_71,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_72,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[c_0_40,c_0_60])).

cnf(c_0_73,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

fof(c_0_74,plain,(
    ! [X14,X15] :
      ( ~ r1_tarski(X14,X15)
      | k3_xboole_0(X14,X15) = X14 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_75,negated_conjecture,
    ( r1_tarski(X1,u1_struct_0(esk1_0))
    | ~ r1_tarski(X2,esk2_0)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_37,c_0_62])).

cnf(c_0_76,negated_conjecture,
    ( v4_pre_topc(esk2_0,esk1_0)
    | r1_tarski(k2_tops_1(esk1_0,esk2_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_52])])).

cnf(c_0_77,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_78,plain,
    ( r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_46])).

cnf(c_0_79,plain,
    ( k7_subset_1(X1,X2,X3) = k7_subset_1(X4,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X4)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_53])).

cnf(c_0_80,plain,
    ( m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_81,plain,
    ( k4_subset_1(X1,k3_subset_1(X1,X2),X2) = X1
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_67]),c_0_46])).

cnf(c_0_82,plain,
    ( k4_subset_1(X1,X2,k1_xboole_0) = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_60]),c_0_71])]),c_0_72])).

cnf(c_0_83,plain,
    ( k3_subset_1(X2,X1) = k5_xboole_0(X2,k3_xboole_0(X2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_73,c_0_27])).

cnf(c_0_84,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

fof(c_0_85,plain,(
    ! [X46,X47] :
      ( ~ l1_pre_topc(X46)
      | ~ m1_subset_1(X47,k1_zfmisc_1(u1_struct_0(X46)))
      | k2_pre_topc(X46,X47) = k4_subset_1(u1_struct_0(X46),X47,k2_tops_1(X46,X47)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_tops_1])])])).

cnf(c_0_86,negated_conjecture,
    ( v4_pre_topc(esk2_0,esk1_0)
    | r1_tarski(X1,u1_struct_0(esk1_0))
    | ~ r1_tarski(X1,k2_tops_1(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_87,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_77])).

cnf(c_0_88,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_89,plain,
    ( r1_tarski(k7_subset_1(X1,X2,X3),X4)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X4))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_78,c_0_53])).

cnf(c_0_90,negated_conjecture,
    ( k7_subset_1(X1,esk2_0,k1_tops_1(esk1_0,esk2_0)) = k2_tops_1(esk1_0,esk2_0)
    | v4_pre_topc(esk2_0,esk1_0)
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_79]),c_0_52])])).

cnf(c_0_91,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_80,c_0_57])).

cnf(c_0_92,plain,
    ( k3_subset_1(X1,k1_xboole_0) = X1
    | ~ m1_subset_1(k3_subset_1(X1,k1_xboole_0),k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_82]),c_0_71])])).

cnf(c_0_93,plain,
    ( k5_xboole_0(X1,X1) = k3_subset_1(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_83,c_0_84])).

cnf(c_0_94,plain,
    ( k2_pre_topc(X1,X2) = k4_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_85])).

cnf(c_0_95,plain,
    ( k4_subset_1(X1,X2,X3) = k4_subset_1(X4,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X4))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X4)) ),
    inference(spm,[status(thm)],[c_0_70,c_0_70])).

cnf(c_0_96,negated_conjecture,
    ( v4_pre_topc(esk2_0,esk1_0)
    | r1_tarski(k2_tops_1(esk1_0,esk2_0),u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_86,c_0_87])).

cnf(c_0_97,plain,
    ( m1_subset_1(k7_subset_1(X1,X2,X3),k1_zfmisc_1(X4))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X4))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_88,c_0_89])).

cnf(c_0_98,negated_conjecture,
    ( k7_subset_1(esk2_0,esk2_0,k1_tops_1(esk1_0,esk2_0)) = k2_tops_1(esk1_0,esk2_0)
    | v4_pre_topc(esk2_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_90,c_0_91])).

cnf(c_0_99,plain,
    ( k5_xboole_0(X1,k3_subset_1(X2,X1)) = X2
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_83]),c_0_38])).

cnf(c_0_100,plain,
    ( k3_subset_1(X1,k1_xboole_0) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_46]),c_0_71])])).

cnf(c_0_101,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_71])).

cnf(c_0_102,plain,
    ( k5_xboole_0(X1,X1) = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_tarski(X1,k3_subset_1(X1,X2)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_93]),c_0_46])).

cnf(c_0_103,plain,
    ( k4_subset_1(X1,X2,k2_tops_1(X3,X2)) = k2_pre_topc(X3,X2)
    | ~ l1_pre_topc(X3)
    | ~ m1_subset_1(k2_tops_1(X3,X2),k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(k2_tops_1(X3,X2),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_94,c_0_95])).

cnf(c_0_104,negated_conjecture,
    ( v4_pre_topc(esk2_0,esk1_0)
    | m1_subset_1(k2_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_88,c_0_96])).

cnf(c_0_105,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_106,negated_conjecture,
    ( v4_pre_topc(esk2_0,esk1_0)
    | m1_subset_1(k2_tops_1(esk1_0,esk2_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_98]),c_0_91])])).

cnf(c_0_107,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X4))
    | ~ r1_tarski(X1,k7_subset_1(X4,X3,X5)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_89])).

cnf(c_0_108,plain,
    ( k5_xboole_0(X1,k7_subset_1(X2,X3,X1)) = X3
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_41,c_0_53])).

cnf(c_0_109,plain,
    ( k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_100]),c_0_71])])).

cnf(c_0_110,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_51]),c_0_60])).

fof(c_0_111,plain,(
    ! [X48,X49] :
      ( ~ l1_pre_topc(X48)
      | ~ m1_subset_1(X49,k1_zfmisc_1(u1_struct_0(X48)))
      | ~ v4_pre_topc(X49,X48)
      | r1_tarski(k2_tops_1(X48,X49),X49) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t69_tops_1])])])).

cnf(c_0_112,plain,
    ( k4_subset_1(X1,X2,X3) = k5_xboole_0(X2,k5_xboole_0(X3,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_70,c_0_84])).

cnf(c_0_113,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_100]),c_0_71]),c_0_87])])).

cnf(c_0_114,negated_conjecture,
    ( k4_subset_1(X1,esk2_0,k2_tops_1(esk1_0,esk2_0)) = k2_pre_topc(esk1_0,esk2_0)
    | v4_pre_topc(esk2_0,esk1_0)
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(X1)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_104]),c_0_105]),c_0_52])]),c_0_106])).

cnf(c_0_115,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k7_subset_1(X3,X4,X5)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_107,c_0_38])).

cnf(c_0_116,plain,
    ( k7_subset_1(X1,X2,k1_xboole_0) = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_109]),c_0_110])])).

cnf(c_0_117,plain,
    ( r1_tarski(k2_tops_1(X1,X2),X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_111])).

fof(c_0_118,plain,(
    ! [X42,X43] :
      ( ~ v2_pre_topc(X42)
      | ~ l1_pre_topc(X42)
      | ~ m1_subset_1(X43,k1_zfmisc_1(u1_struct_0(X42)))
      | v4_pre_topc(k2_pre_topc(X42,X43),X42) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_tops_1])])).

cnf(c_0_119,plain,
    ( k4_subset_1(X1,X2,X3) = X2
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_tarski(X3,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_112,c_0_113]),c_0_72])).

cnf(c_0_120,negated_conjecture,
    ( k4_subset_1(esk2_0,esk2_0,k2_tops_1(esk1_0,esk2_0)) = k2_pre_topc(esk1_0,esk2_0)
    | v4_pre_topc(esk2_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_114,c_0_91])).

cnf(c_0_121,negated_conjecture,
    ( v4_pre_topc(esk2_0,esk1_0)
    | m1_subset_1(k2_tops_1(esk1_0,esk2_0),k1_zfmisc_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_88,c_0_76])).

cnf(c_0_122,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X4)) ),
    inference(spm,[status(thm)],[c_0_115,c_0_116])).

cnf(c_0_123,plain,
    ( m1_subset_1(k2_tops_1(X1,X2),k1_zfmisc_1(X2))
    | ~ v4_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_88,c_0_117])).

cnf(c_0_124,plain,
    ( v4_pre_topc(k2_pre_topc(X1,X2),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_118])).

cnf(c_0_125,negated_conjecture,
    ( k2_pre_topc(esk1_0,esk2_0) = esk2_0
    | v4_pre_topc(esk2_0,esk1_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119,c_0_120]),c_0_91])]),c_0_38]),c_0_121])).

cnf(c_0_126,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_127,plain,
    ( r1_tarski(k2_tops_1(X1,X2),X3)
    | ~ v4_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X4)) ),
    inference(spm,[status(thm)],[c_0_122,c_0_123])).

cnf(c_0_128,negated_conjecture,
    ( v4_pre_topc(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_124,c_0_125]),c_0_105]),c_0_126]),c_0_52])])).

cnf(c_0_129,negated_conjecture,
    ( r1_tarski(k2_tops_1(esk1_0,esk2_0),X1)
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_127,c_0_52]),c_0_128]),c_0_105])])).

cnf(c_0_130,negated_conjecture,
    ( r1_tarski(k2_tops_1(esk1_0,esk2_0),esk2_0)
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_129,c_0_91])).

cnf(c_0_131,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_tarski(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_88,c_0_62])).

cnf(c_0_132,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k3_subset_1(X2,X3)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_38])).

cnf(c_0_133,negated_conjecture,
    ( r1_tarski(k2_tops_1(esk1_0,esk2_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_130,c_0_131]),c_0_87])])).

cnf(c_0_134,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_132,c_0_67]),c_0_46])).

cnf(c_0_135,negated_conjecture,
    ( m1_subset_1(k2_tops_1(esk1_0,esk2_0),k1_zfmisc_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_88,c_0_133])).

cnf(c_0_136,negated_conjecture,
    ( r1_tarski(k2_tops_1(esk1_0,esk2_0),X1)
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_134,c_0_135])).

fof(c_0_137,plain,(
    ! [X44,X45] :
      ( ~ l1_pre_topc(X44)
      | ~ m1_subset_1(X45,k1_zfmisc_1(u1_struct_0(X44)))
      | k2_tops_1(X44,X45) = k7_subset_1(u1_struct_0(X44),k2_pre_topc(X44,X45),k1_tops_1(X44,X45)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l78_tops_1])])])).

cnf(c_0_138,plain,
    ( k2_pre_topc(X1,X2) = X2
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(k2_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(k2_tops_1(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_94,c_0_119])).

cnf(c_0_139,negated_conjecture,
    ( m1_subset_1(k2_tops_1(esk1_0,esk2_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_88,c_0_136])).

cnf(c_0_140,negated_conjecture,
    ( ~ v4_pre_topc(esk2_0,esk1_0)
    | k2_tops_1(esk1_0,esk2_0) != k7_subset_1(u1_struct_0(esk1_0),esk2_0,k1_tops_1(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_141,plain,
    ( k2_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k1_tops_1(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_137])).

cnf(c_0_142,negated_conjecture,
    ( k2_pre_topc(esk1_0,esk2_0) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_138,c_0_139]),c_0_105]),c_0_52]),c_0_133])])).

cnf(c_0_143,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),esk2_0,k1_tops_1(esk1_0,esk2_0)) != k2_tops_1(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_140,c_0_128])])).

cnf(c_0_144,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_141,c_0_142]),c_0_105]),c_0_52])]),c_0_143]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:07:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 3.25/3.41  # AutoSched0-Mode selected heuristic G_E___302_C18_F1_URBAN_RG_S04BN
% 3.25/3.41  # and selection function PSelectComplexExceptUniqMaxHorn.
% 3.25/3.41  #
% 3.25/3.41  # Preprocessing time       : 0.029 s
% 3.25/3.41  
% 3.25/3.41  # Proof found!
% 3.25/3.41  # SZS status Theorem
% 3.25/3.41  # SZS output start CNFRefutation
% 3.25/3.41  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 3.25/3.41  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.25/3.41  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 3.25/3.41  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.25/3.41  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 3.25/3.41  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.25/3.41  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 3.25/3.41  fof(t77_tops_1, conjecture, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v4_pre_topc(X2,X1)<=>k2_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),X2,k1_tops_1(X1,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_tops_1)).
% 3.25/3.41  fof(redefinition_k7_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k7_subset_1(X1,X2,X3)=k4_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 3.25/3.41  fof(dt_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 3.25/3.41  fof(t25_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k4_subset_1(X1,X2,k3_subset_1(X1,X2))=k2_subset_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_subset_1)).
% 3.25/3.41  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 3.25/3.41  fof(redefinition_k4_subset_1, axiom, ![X1, X2, X3]:((m1_subset_1(X2,k1_zfmisc_1(X1))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>k4_subset_1(X1,X2,X3)=k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 3.25/3.41  fof(involutiveness_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,k3_subset_1(X1,X2))=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 3.25/3.41  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 3.25/3.41  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 3.25/3.41  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.25/3.41  fof(dt_k2_subset_1, axiom, ![X1]:m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 3.25/3.41  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.25/3.41  fof(t65_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k2_pre_topc(X1,X2)=k4_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tops_1)).
% 3.25/3.41  fof(t69_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v4_pre_topc(X2,X1)=>r1_tarski(k2_tops_1(X1,X2),X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_tops_1)).
% 3.25/3.41  fof(fc1_tops_1, axiom, ![X1, X2]:(((v2_pre_topc(X1)&l1_pre_topc(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>v4_pre_topc(k2_pre_topc(X1,X2),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_tops_1)).
% 3.25/3.41  fof(l78_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k2_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k1_tops_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l78_tops_1)).
% 3.25/3.41  fof(c_0_23, plain, ![X18, X19]:k2_xboole_0(X18,X19)=k5_xboole_0(X18,k4_xboole_0(X19,X18)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 3.25/3.41  fof(c_0_24, plain, ![X6, X7]:k4_xboole_0(X6,X7)=k5_xboole_0(X6,k3_xboole_0(X6,X7)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 3.25/3.41  fof(c_0_25, plain, ![X10]:k2_xboole_0(X10,k1_xboole_0)=X10, inference(variable_rename,[status(thm)],[t1_boole])).
% 3.25/3.41  cnf(c_0_26, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 3.25/3.41  cnf(c_0_27, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 3.25/3.41  fof(c_0_28, plain, ![X8, X9]:(~r1_tarski(X8,X9)|k2_xboole_0(X8,X9)=X9), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 3.25/3.41  fof(c_0_29, plain, ![X11, X12, X13]:(~r1_tarski(X11,X12)|~r1_tarski(X12,X13)|r1_tarski(X11,X13)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 3.25/3.41  fof(c_0_30, plain, ![X37, X38]:((~m1_subset_1(X37,k1_zfmisc_1(X38))|r1_tarski(X37,X38))&(~r1_tarski(X37,X38)|m1_subset_1(X37,k1_zfmisc_1(X38)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 3.25/3.41  cnf(c_0_31, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_25])).
% 3.25/3.41  cnf(c_0_32, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))), inference(rw,[status(thm)],[c_0_26, c_0_27])).
% 3.25/3.41  cnf(c_0_33, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 3.25/3.41  fof(c_0_34, plain, ![X16, X17]:r1_tarski(k4_xboole_0(X16,X17),X16), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 3.25/3.41  fof(c_0_35, negated_conjecture, ~(![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v4_pre_topc(X2,X1)<=>k2_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),X2,k1_tops_1(X1,X2)))))), inference(assume_negation,[status(cth)],[t77_tops_1])).
% 3.25/3.41  fof(c_0_36, plain, ![X31, X32, X33]:(~m1_subset_1(X32,k1_zfmisc_1(X31))|k7_subset_1(X31,X32,X33)=k4_xboole_0(X32,X33)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).
% 3.25/3.41  cnf(c_0_37, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 3.25/3.41  cnf(c_0_38, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 3.25/3.41  fof(c_0_39, plain, ![X24, X25]:(~m1_subset_1(X25,k1_zfmisc_1(X24))|m1_subset_1(k3_subset_1(X24,X25),k1_zfmisc_1(X24))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).
% 3.25/3.41  cnf(c_0_40, plain, (k5_xboole_0(X1,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1)))=X1), inference(rw,[status(thm)],[c_0_31, c_0_32])).
% 3.25/3.41  cnf(c_0_41, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))=X2|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_33, c_0_32])).
% 3.25/3.41  cnf(c_0_42, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 3.25/3.41  fof(c_0_43, negated_conjecture, ((v2_pre_topc(esk1_0)&l1_pre_topc(esk1_0))&(m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&((~v4_pre_topc(esk2_0,esk1_0)|k2_tops_1(esk1_0,esk2_0)!=k7_subset_1(u1_struct_0(esk1_0),esk2_0,k1_tops_1(esk1_0,esk2_0)))&(v4_pre_topc(esk2_0,esk1_0)|k2_tops_1(esk1_0,esk2_0)=k7_subset_1(u1_struct_0(esk1_0),esk2_0,k1_tops_1(esk1_0,esk2_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_35])])])).
% 3.25/3.41  cnf(c_0_44, plain, (k7_subset_1(X2,X1,X3)=k4_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 3.25/3.41  cnf(c_0_45, plain, (r1_tarski(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 3.25/3.41  cnf(c_0_46, plain, (m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 3.25/3.41  fof(c_0_47, plain, ![X34, X35]:(~m1_subset_1(X35,k1_zfmisc_1(X34))|k4_subset_1(X34,X35,k3_subset_1(X34,X35))=k2_subset_1(X34)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_subset_1])])).
% 3.25/3.41  fof(c_0_48, plain, ![X20]:k2_subset_1(X20)=X20, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 3.25/3.41  fof(c_0_49, plain, ![X28, X29, X30]:(~m1_subset_1(X29,k1_zfmisc_1(X28))|~m1_subset_1(X30,k1_zfmisc_1(X28))|k4_subset_1(X28,X29,X30)=k2_xboole_0(X29,X30)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).
% 3.25/3.41  cnf(c_0_50, plain, (k1_xboole_0=X1|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 3.25/3.41  cnf(c_0_51, plain, (r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X1)), inference(rw,[status(thm)],[c_0_42, c_0_27])).
% 3.25/3.41  cnf(c_0_52, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 3.25/3.41  cnf(c_0_53, plain, (k7_subset_1(X2,X1,X3)=k5_xboole_0(X1,k3_xboole_0(X1,X3))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_44, c_0_27])).
% 3.25/3.41  cnf(c_0_54, plain, (r1_tarski(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_tarski(X1,k3_subset_1(X2,X3))), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 3.25/3.41  fof(c_0_55, plain, ![X26, X27]:(~m1_subset_1(X27,k1_zfmisc_1(X26))|k3_subset_1(X26,k3_subset_1(X26,X27))=X27), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).
% 3.25/3.41  cnf(c_0_56, plain, (k4_subset_1(X2,X1,k3_subset_1(X2,X1))=k2_subset_1(X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_47])).
% 3.25/3.41  cnf(c_0_57, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_48])).
% 3.25/3.41  cnf(c_0_58, plain, (k4_subset_1(X2,X1,X3)=k2_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_49])).
% 3.25/3.41  fof(c_0_59, plain, ![X36]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X36)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 3.25/3.41  cnf(c_0_60, plain, (k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1))=k1_xboole_0), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 3.25/3.41  fof(c_0_61, plain, ![X21, X22]:(~m1_subset_1(X22,k1_zfmisc_1(X21))|k3_subset_1(X21,X22)=k4_xboole_0(X21,X22)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 3.25/3.41  cnf(c_0_62, negated_conjecture, (r1_tarski(X1,u1_struct_0(esk1_0))|~r1_tarski(X1,esk2_0)), inference(spm,[status(thm)],[c_0_45, c_0_52])).
% 3.25/3.41  cnf(c_0_63, plain, (r1_tarski(k7_subset_1(X1,X2,X3),X2)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_51, c_0_53])).
% 3.25/3.41  cnf(c_0_64, negated_conjecture, (v4_pre_topc(esk2_0,esk1_0)|k2_tops_1(esk1_0,esk2_0)=k7_subset_1(u1_struct_0(esk1_0),esk2_0,k1_tops_1(esk1_0,esk2_0))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 3.25/3.41  fof(c_0_65, plain, ![X4, X5]:(((r1_tarski(X4,X5)|X4!=X5)&(r1_tarski(X5,X4)|X4!=X5))&(~r1_tarski(X4,X5)|~r1_tarski(X5,X4)|X4=X5)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 3.25/3.41  cnf(c_0_66, plain, (r1_tarski(k5_xboole_0(k3_subset_1(X1,X2),k3_xboole_0(k3_subset_1(X1,X2),X3)),X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_54, c_0_51])).
% 3.25/3.41  cnf(c_0_67, plain, (k3_subset_1(X2,k3_subset_1(X2,X1))=X1|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_55])).
% 3.25/3.41  fof(c_0_68, plain, ![X23]:m1_subset_1(k2_subset_1(X23),k1_zfmisc_1(X23)), inference(variable_rename,[status(thm)],[dt_k2_subset_1])).
% 3.25/3.41  cnf(c_0_69, plain, (k4_subset_1(X2,X1,k3_subset_1(X2,X1))=X2|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_56, c_0_57])).
% 3.25/3.41  cnf(c_0_70, plain, (k4_subset_1(X2,X1,X3)=k5_xboole_0(X1,k5_xboole_0(X3,k3_xboole_0(X3,X1)))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_58, c_0_32])).
% 3.25/3.41  cnf(c_0_71, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_59])).
% 3.25/3.41  cnf(c_0_72, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[c_0_40, c_0_60])).
% 3.25/3.41  cnf(c_0_73, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_61])).
% 3.25/3.41  fof(c_0_74, plain, ![X14, X15]:(~r1_tarski(X14,X15)|k3_xboole_0(X14,X15)=X14), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 3.25/3.41  cnf(c_0_75, negated_conjecture, (r1_tarski(X1,u1_struct_0(esk1_0))|~r1_tarski(X2,esk2_0)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_37, c_0_62])).
% 3.25/3.41  cnf(c_0_76, negated_conjecture, (v4_pre_topc(esk2_0,esk1_0)|r1_tarski(k2_tops_1(esk1_0,esk2_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_52])])).
% 3.25/3.41  cnf(c_0_77, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_65])).
% 3.25/3.41  cnf(c_0_78, plain, (r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3)|~m1_subset_1(X1,k1_zfmisc_1(X3))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_46])).
% 3.25/3.41  cnf(c_0_79, plain, (k7_subset_1(X1,X2,X3)=k7_subset_1(X4,X2,X3)|~m1_subset_1(X2,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X4))), inference(spm,[status(thm)],[c_0_53, c_0_53])).
% 3.25/3.41  cnf(c_0_80, plain, (m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_68])).
% 3.25/3.41  cnf(c_0_81, plain, (k4_subset_1(X1,k3_subset_1(X1,X2),X2)=X1|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_67]), c_0_46])).
% 3.25/3.41  cnf(c_0_82, plain, (k4_subset_1(X1,X2,k1_xboole_0)=X2|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_60]), c_0_71])]), c_0_72])).
% 3.25/3.41  cnf(c_0_83, plain, (k3_subset_1(X2,X1)=k5_xboole_0(X2,k3_xboole_0(X2,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_73, c_0_27])).
% 3.25/3.41  cnf(c_0_84, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_74])).
% 3.25/3.41  fof(c_0_85, plain, ![X46, X47]:(~l1_pre_topc(X46)|(~m1_subset_1(X47,k1_zfmisc_1(u1_struct_0(X46)))|k2_pre_topc(X46,X47)=k4_subset_1(u1_struct_0(X46),X47,k2_tops_1(X46,X47)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_tops_1])])])).
% 3.25/3.41  cnf(c_0_86, negated_conjecture, (v4_pre_topc(esk2_0,esk1_0)|r1_tarski(X1,u1_struct_0(esk1_0))|~r1_tarski(X1,k2_tops_1(esk1_0,esk2_0))), inference(spm,[status(thm)],[c_0_75, c_0_76])).
% 3.25/3.41  cnf(c_0_87, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_77])).
% 3.25/3.41  cnf(c_0_88, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 3.25/3.41  cnf(c_0_89, plain, (r1_tarski(k7_subset_1(X1,X2,X3),X4)|~m1_subset_1(X2,k1_zfmisc_1(X4))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_78, c_0_53])).
% 3.25/3.41  cnf(c_0_90, negated_conjecture, (k7_subset_1(X1,esk2_0,k1_tops_1(esk1_0,esk2_0))=k2_tops_1(esk1_0,esk2_0)|v4_pre_topc(esk2_0,esk1_0)|~m1_subset_1(esk2_0,k1_zfmisc_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_79]), c_0_52])])).
% 3.25/3.41  cnf(c_0_91, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_80, c_0_57])).
% 3.25/3.41  cnf(c_0_92, plain, (k3_subset_1(X1,k1_xboole_0)=X1|~m1_subset_1(k3_subset_1(X1,k1_xboole_0),k1_zfmisc_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_82]), c_0_71])])).
% 3.25/3.41  cnf(c_0_93, plain, (k5_xboole_0(X1,X1)=k3_subset_1(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_83, c_0_84])).
% 3.25/3.41  cnf(c_0_94, plain, (k2_pre_topc(X1,X2)=k4_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_85])).
% 3.25/3.41  cnf(c_0_95, plain, (k4_subset_1(X1,X2,X3)=k4_subset_1(X4,X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~m1_subset_1(X3,k1_zfmisc_1(X4))|~m1_subset_1(X2,k1_zfmisc_1(X4))), inference(spm,[status(thm)],[c_0_70, c_0_70])).
% 3.25/3.41  cnf(c_0_96, negated_conjecture, (v4_pre_topc(esk2_0,esk1_0)|r1_tarski(k2_tops_1(esk1_0,esk2_0),u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_86, c_0_87])).
% 3.25/3.41  cnf(c_0_97, plain, (m1_subset_1(k7_subset_1(X1,X2,X3),k1_zfmisc_1(X4))|~m1_subset_1(X2,k1_zfmisc_1(X4))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_88, c_0_89])).
% 3.25/3.41  cnf(c_0_98, negated_conjecture, (k7_subset_1(esk2_0,esk2_0,k1_tops_1(esk1_0,esk2_0))=k2_tops_1(esk1_0,esk2_0)|v4_pre_topc(esk2_0,esk1_0)), inference(spm,[status(thm)],[c_0_90, c_0_91])).
% 3.25/3.41  cnf(c_0_99, plain, (k5_xboole_0(X1,k3_subset_1(X2,X1))=X2|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_83]), c_0_38])).
% 3.25/3.41  cnf(c_0_100, plain, (k3_subset_1(X1,k1_xboole_0)=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_46]), c_0_71])])).
% 3.25/3.41  cnf(c_0_101, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_45, c_0_71])).
% 3.25/3.41  cnf(c_0_102, plain, (k5_xboole_0(X1,X1)=X2|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_tarski(X1,k3_subset_1(X1,X2))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_93]), c_0_46])).
% 3.25/3.41  cnf(c_0_103, plain, (k4_subset_1(X1,X2,k2_tops_1(X3,X2))=k2_pre_topc(X3,X2)|~l1_pre_topc(X3)|~m1_subset_1(k2_tops_1(X3,X2),k1_zfmisc_1(u1_struct_0(X3)))|~m1_subset_1(k2_tops_1(X3,X2),k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_94, c_0_95])).
% 3.25/3.41  cnf(c_0_104, negated_conjecture, (v4_pre_topc(esk2_0,esk1_0)|m1_subset_1(k2_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_88, c_0_96])).
% 3.25/3.41  cnf(c_0_105, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 3.25/3.41  cnf(c_0_106, negated_conjecture, (v4_pre_topc(esk2_0,esk1_0)|m1_subset_1(k2_tops_1(esk1_0,esk2_0),k1_zfmisc_1(X1))|~m1_subset_1(esk2_0,k1_zfmisc_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97, c_0_98]), c_0_91])])).
% 3.25/3.41  cnf(c_0_107, plain, (r1_tarski(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X4))|~r1_tarski(X1,k7_subset_1(X4,X3,X5))), inference(spm,[status(thm)],[c_0_37, c_0_89])).
% 3.25/3.41  cnf(c_0_108, plain, (k5_xboole_0(X1,k7_subset_1(X2,X3,X1))=X3|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_41, c_0_53])).
% 3.25/3.41  cnf(c_0_109, plain, (k5_xboole_0(k1_xboole_0,X1)=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_100]), c_0_71])])).
% 3.25/3.41  cnf(c_0_110, plain, (r1_tarski(k1_xboole_0,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101, c_0_51]), c_0_60])).
% 3.25/3.41  fof(c_0_111, plain, ![X48, X49]:(~l1_pre_topc(X48)|(~m1_subset_1(X49,k1_zfmisc_1(u1_struct_0(X48)))|(~v4_pre_topc(X49,X48)|r1_tarski(k2_tops_1(X48,X49),X49)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t69_tops_1])])])).
% 3.25/3.41  cnf(c_0_112, plain, (k4_subset_1(X1,X2,X3)=k5_xboole_0(X2,k5_xboole_0(X3,X3))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_70, c_0_84])).
% 3.25/3.41  cnf(c_0_113, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102, c_0_100]), c_0_71]), c_0_87])])).
% 3.25/3.41  cnf(c_0_114, negated_conjecture, (k4_subset_1(X1,esk2_0,k2_tops_1(esk1_0,esk2_0))=k2_pre_topc(esk1_0,esk2_0)|v4_pre_topc(esk2_0,esk1_0)|~m1_subset_1(esk2_0,k1_zfmisc_1(X1))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103, c_0_104]), c_0_105]), c_0_52])]), c_0_106])).
% 3.25/3.41  cnf(c_0_115, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k7_subset_1(X3,X4,X5)))|~m1_subset_1(X4,k1_zfmisc_1(X2))|~m1_subset_1(X4,k1_zfmisc_1(X3))), inference(spm,[status(thm)],[c_0_107, c_0_38])).
% 3.25/3.41  cnf(c_0_116, plain, (k7_subset_1(X1,X2,k1_xboole_0)=X2|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108, c_0_109]), c_0_110])])).
% 3.25/3.41  cnf(c_0_117, plain, (r1_tarski(k2_tops_1(X1,X2),X2)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v4_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_111])).
% 3.25/3.41  fof(c_0_118, plain, ![X42, X43]:(~v2_pre_topc(X42)|~l1_pre_topc(X42)|~m1_subset_1(X43,k1_zfmisc_1(u1_struct_0(X42)))|v4_pre_topc(k2_pre_topc(X42,X43),X42)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_tops_1])])).
% 3.25/3.41  cnf(c_0_119, plain, (k4_subset_1(X1,X2,X3)=X2|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_tarski(X3,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_112, c_0_113]), c_0_72])).
% 3.25/3.41  cnf(c_0_120, negated_conjecture, (k4_subset_1(esk2_0,esk2_0,k2_tops_1(esk1_0,esk2_0))=k2_pre_topc(esk1_0,esk2_0)|v4_pre_topc(esk2_0,esk1_0)), inference(spm,[status(thm)],[c_0_114, c_0_91])).
% 3.25/3.41  cnf(c_0_121, negated_conjecture, (v4_pre_topc(esk2_0,esk1_0)|m1_subset_1(k2_tops_1(esk1_0,esk2_0),k1_zfmisc_1(esk2_0))), inference(spm,[status(thm)],[c_0_88, c_0_76])).
% 3.25/3.41  cnf(c_0_122, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X3))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X4))), inference(spm,[status(thm)],[c_0_115, c_0_116])).
% 3.25/3.41  cnf(c_0_123, plain, (m1_subset_1(k2_tops_1(X1,X2),k1_zfmisc_1(X2))|~v4_pre_topc(X2,X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_88, c_0_117])).
% 3.25/3.41  cnf(c_0_124, plain, (v4_pre_topc(k2_pre_topc(X1,X2),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_118])).
% 3.25/3.41  cnf(c_0_125, negated_conjecture, (k2_pre_topc(esk1_0,esk2_0)=esk2_0|v4_pre_topc(esk2_0,esk1_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119, c_0_120]), c_0_91])]), c_0_38]), c_0_121])).
% 3.25/3.41  cnf(c_0_126, negated_conjecture, (v2_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 3.25/3.41  cnf(c_0_127, plain, (r1_tarski(k2_tops_1(X1,X2),X3)|~v4_pre_topc(X2,X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(X3))|~m1_subset_1(X2,k1_zfmisc_1(X4))), inference(spm,[status(thm)],[c_0_122, c_0_123])).
% 3.25/3.41  cnf(c_0_128, negated_conjecture, (v4_pre_topc(esk2_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_124, c_0_125]), c_0_105]), c_0_126]), c_0_52])])).
% 3.25/3.41  cnf(c_0_129, negated_conjecture, (r1_tarski(k2_tops_1(esk1_0,esk2_0),X1)|~m1_subset_1(esk2_0,k1_zfmisc_1(X1))|~m1_subset_1(esk2_0,k1_zfmisc_1(X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_127, c_0_52]), c_0_128]), c_0_105])])).
% 3.25/3.41  cnf(c_0_130, negated_conjecture, (r1_tarski(k2_tops_1(esk1_0,esk2_0),esk2_0)|~m1_subset_1(esk2_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_129, c_0_91])).
% 3.25/3.41  cnf(c_0_131, negated_conjecture, (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))|~r1_tarski(X1,esk2_0)), inference(spm,[status(thm)],[c_0_88, c_0_62])).
% 3.25/3.41  cnf(c_0_132, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k3_subset_1(X2,X3)))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_54, c_0_38])).
% 3.25/3.41  cnf(c_0_133, negated_conjecture, (r1_tarski(k2_tops_1(esk1_0,esk2_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_130, c_0_131]), c_0_87])])).
% 3.25/3.41  cnf(c_0_134, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X3))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_132, c_0_67]), c_0_46])).
% 3.25/3.41  cnf(c_0_135, negated_conjecture, (m1_subset_1(k2_tops_1(esk1_0,esk2_0),k1_zfmisc_1(esk2_0))), inference(spm,[status(thm)],[c_0_88, c_0_133])).
% 3.25/3.41  cnf(c_0_136, negated_conjecture, (r1_tarski(k2_tops_1(esk1_0,esk2_0),X1)|~m1_subset_1(esk2_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_134, c_0_135])).
% 3.25/3.41  fof(c_0_137, plain, ![X44, X45]:(~l1_pre_topc(X44)|(~m1_subset_1(X45,k1_zfmisc_1(u1_struct_0(X44)))|k2_tops_1(X44,X45)=k7_subset_1(u1_struct_0(X44),k2_pre_topc(X44,X45),k1_tops_1(X44,X45)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l78_tops_1])])])).
% 3.25/3.41  cnf(c_0_138, plain, (k2_pre_topc(X1,X2)=X2|~l1_pre_topc(X1)|~m1_subset_1(k2_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(k2_tops_1(X1,X2),X2)), inference(spm,[status(thm)],[c_0_94, c_0_119])).
% 3.25/3.41  cnf(c_0_139, negated_conjecture, (m1_subset_1(k2_tops_1(esk1_0,esk2_0),k1_zfmisc_1(X1))|~m1_subset_1(esk2_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_88, c_0_136])).
% 3.25/3.41  cnf(c_0_140, negated_conjecture, (~v4_pre_topc(esk2_0,esk1_0)|k2_tops_1(esk1_0,esk2_0)!=k7_subset_1(u1_struct_0(esk1_0),esk2_0,k1_tops_1(esk1_0,esk2_0))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 3.25/3.41  cnf(c_0_141, plain, (k2_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k1_tops_1(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_137])).
% 3.25/3.41  cnf(c_0_142, negated_conjecture, (k2_pre_topc(esk1_0,esk2_0)=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_138, c_0_139]), c_0_105]), c_0_52]), c_0_133])])).
% 3.25/3.41  cnf(c_0_143, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),esk2_0,k1_tops_1(esk1_0,esk2_0))!=k2_tops_1(esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_140, c_0_128])])).
% 3.25/3.41  cnf(c_0_144, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_141, c_0_142]), c_0_105]), c_0_52])]), c_0_143]), ['proof']).
% 3.25/3.41  # SZS output end CNFRefutation
% 3.25/3.41  # Proof object total steps             : 145
% 3.25/3.41  # Proof object clause steps            : 98
% 3.25/3.41  # Proof object formula steps           : 47
% 3.25/3.41  # Proof object conjectures             : 32
% 3.25/3.41  # Proof object clause conjectures      : 29
% 3.25/3.41  # Proof object formula conjectures     : 3
% 3.25/3.41  # Proof object initial clauses used    : 28
% 3.25/3.41  # Proof object initial formulas used   : 23
% 3.25/3.41  # Proof object generating inferences   : 57
% 3.25/3.41  # Proof object simplifying inferences  : 66
% 3.25/3.41  # Training examples: 0 positive, 0 negative
% 3.25/3.41  # Parsed axioms                        : 24
% 3.25/3.41  # Removed by relevancy pruning/SinE    : 0
% 3.25/3.41  # Initial clauses                      : 31
% 3.25/3.41  # Removed in clause preprocessing      : 3
% 3.25/3.41  # Initial clauses in saturation        : 28
% 3.25/3.41  # Processed clauses                    : 17810
% 3.25/3.41  # ...of these trivial                  : 127
% 3.25/3.41  # ...subsumed                          : 14877
% 3.25/3.41  # ...remaining for further processing  : 2806
% 3.25/3.41  # Other redundant clauses eliminated   : 2
% 3.25/3.41  # Clauses deleted for lack of memory   : 0
% 3.25/3.41  # Backward-subsumed                    : 341
% 3.25/3.41  # Backward-rewritten                   : 308
% 3.25/3.41  # Generated clauses                    : 187752
% 3.25/3.41  # ...of the previous two non-trivial   : 175597
% 3.25/3.41  # Contextual simplify-reflections      : 569
% 3.25/3.41  # Paramodulations                      : 187750
% 3.25/3.41  # Factorizations                       : 0
% 3.25/3.41  # Equation resolutions                 : 2
% 3.25/3.41  # Propositional unsat checks           : 0
% 3.25/3.41  #    Propositional check models        : 0
% 3.25/3.41  #    Propositional check unsatisfiable : 0
% 3.25/3.41  #    Propositional clauses             : 0
% 3.25/3.41  #    Propositional clauses after purity: 0
% 3.25/3.41  #    Propositional unsat core size     : 0
% 3.25/3.41  #    Propositional preprocessing time  : 0.000
% 3.25/3.41  #    Propositional encoding time       : 0.000
% 3.25/3.41  #    Propositional solver time         : 0.000
% 3.25/3.41  #    Success case prop preproc time    : 0.000
% 3.25/3.41  #    Success case prop encoding time   : 0.000
% 3.25/3.41  #    Success case prop solver time     : 0.000
% 3.25/3.41  # Current number of processed clauses  : 2155
% 3.25/3.41  #    Positive orientable unit clauses  : 38
% 3.25/3.41  #    Positive unorientable unit clauses: 0
% 3.25/3.41  #    Negative unit clauses             : 5
% 3.25/3.41  #    Non-unit-clauses                  : 2112
% 3.25/3.41  # Current number of unprocessed clauses: 153863
% 3.25/3.41  # ...number of literals in the above   : 856061
% 3.25/3.41  # Current number of archived formulas  : 0
% 3.25/3.41  # Current number of archived clauses   : 652
% 3.25/3.41  # Clause-clause subsumption calls (NU) : 1070031
% 3.25/3.41  # Rec. Clause-clause subsumption calls : 332364
% 3.25/3.41  # Non-unit clause-clause subsumptions  : 11997
% 3.25/3.41  # Unit Clause-clause subsumption calls : 1850
% 3.25/3.41  # Rewrite failures with RHS unbound    : 0
% 3.25/3.41  # BW rewrite match attempts            : 228
% 3.25/3.41  # BW rewrite match successes           : 45
% 3.25/3.41  # Condensation attempts                : 0
% 3.25/3.41  # Condensation successes               : 0
% 3.25/3.41  # Termbank termtop insertions          : 4436448
% 3.26/3.42  
% 3.26/3.42  # -------------------------------------------------
% 3.26/3.42  # User time                : 2.979 s
% 3.26/3.42  # System time              : 0.095 s
% 3.26/3.42  # Total time               : 3.074 s
% 3.26/3.42  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
