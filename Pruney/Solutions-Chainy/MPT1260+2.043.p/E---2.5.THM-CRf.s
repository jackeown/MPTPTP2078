%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:11:20 EST 2020

% Result     : Theorem 2.69s
% Output     : CNFRefutation 2.69s
% Verified   : 
% Statistics : Number of formulae       :  206 (17474 expanded)
%              Number of clauses        :  145 (7747 expanded)
%              Number of leaves         :   30 (4489 expanded)
%              Depth                    :   19
%              Number of atoms          :  365 (33873 expanded)
%              Number of equality atoms :  146 (15219 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t76_tops_1,conjecture,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_pre_topc(X2,X1)
          <=> k2_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_tops_1)).

fof(t46_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(t62_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k2_tops_1(X1,X2) = k2_tops_1(X1,k3_subset_1(u1_struct_0(X1),X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_tops_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(dt_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(redefinition_k7_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k7_subset_1(X1,X2,X3) = k4_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(t40_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(dt_k2_tops_1,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k2_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t74_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k1_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).

fof(t65_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k2_pre_topc(X1,X2) = k4_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

fof(redefinition_k4_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => k4_subset_1(X1,X2,X3) = k2_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(dt_k4_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => m1_subset_1(k4_subset_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_subset_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t44_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k4_xboole_0(X1,X2),X3)
     => r1_tarski(X1,k2_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(t56_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( ( v3_pre_topc(X2,X1)
                  & r1_tarski(X2,X3) )
               => r1_tarski(X2,k1_tops_1(X1,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_tops_1)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(fc9_tops_1,axiom,(
    ! [X1,X2] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => v3_pre_topc(k1_tops_1(X1,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

fof(c_0_30,plain,(
    ! [X12,X13] : k4_xboole_0(X12,X13) = k5_xboole_0(X12,k3_xboole_0(X12,X13)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_31,plain,(
    ! [X49,X50] : k1_setfam_1(k2_tarski(X49,X50)) = k3_xboole_0(X49,X50) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_32,negated_conjecture,(
    ~ ! [X1] :
        ( ( v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( v3_pre_topc(X2,X1)
            <=> k2_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t76_tops_1])).

fof(c_0_33,plain,(
    ! [X32,X33] : k4_xboole_0(X32,k2_xboole_0(X32,X33)) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t46_xboole_1])).

cnf(c_0_34,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_35,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_36,plain,(
    ! [X62,X63] :
      ( ~ l1_pre_topc(X62)
      | ~ m1_subset_1(X63,k1_zfmisc_1(u1_struct_0(X62)))
      | k2_tops_1(X62,X63) = k2_tops_1(X62,k3_subset_1(u1_struct_0(X62),X63)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t62_tops_1])])])).

fof(c_0_37,negated_conjecture,
    ( v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & ( ~ v3_pre_topc(esk2_0,esk1_0)
      | k2_tops_1(esk1_0,esk2_0) != k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),esk2_0) )
    & ( v3_pre_topc(esk2_0,esk1_0)
      | k2_tops_1(esk1_0,esk2_0) = k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),esk2_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_32])])])).

fof(c_0_38,plain,(
    ! [X51,X52] :
      ( ( ~ m1_subset_1(X51,k1_zfmisc_1(X52))
        | r1_tarski(X51,X52) )
      & ( ~ r1_tarski(X51,X52)
        | m1_subset_1(X51,k1_zfmisc_1(X52)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_39,plain,(
    ! [X38,X39] :
      ( ~ m1_subset_1(X39,k1_zfmisc_1(X38))
      | m1_subset_1(k3_subset_1(X38,X39),k1_zfmisc_1(X38)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).

fof(c_0_40,plain,(
    ! [X22,X23] : r1_tarski(k4_xboole_0(X22,X23),X22) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

fof(c_0_41,plain,(
    ! [X34,X35] : k4_xboole_0(X34,k4_xboole_0(X34,X35)) = k3_xboole_0(X34,X35) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_42,plain,(
    ! [X10,X11] :
      ( ( k4_xboole_0(X10,X11) != k1_xboole_0
        | r1_tarski(X10,X11) )
      & ( ~ r1_tarski(X10,X11)
        | k4_xboole_0(X10,X11) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

fof(c_0_43,plain,(
    ! [X6,X7] : k3_xboole_0(X6,X7) = k3_xboole_0(X7,X6) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_44,plain,(
    ! [X36,X37] :
      ( ~ m1_subset_1(X37,k1_zfmisc_1(X36))
      | k3_subset_1(X36,X37) = k4_xboole_0(X36,X37) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

fof(c_0_45,plain,(
    ! [X46,X47,X48] :
      ( ~ m1_subset_1(X47,k1_zfmisc_1(X46))
      | k7_subset_1(X46,X47,X48) = k4_xboole_0(X47,X48) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).

fof(c_0_46,plain,(
    ! [X27,X28] : k4_xboole_0(k2_xboole_0(X27,X28),X28) = k4_xboole_0(X27,X28) ),
    inference(variable_rename,[status(thm)],[t40_xboole_1])).

cnf(c_0_47,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_48,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_34,c_0_35])).

fof(c_0_49,plain,(
    ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_50,plain,(
    ! [X26] : k4_xboole_0(X26,k1_xboole_0) = X26 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

fof(c_0_51,plain,(
    ! [X53,X54] :
      ( ~ l1_pre_topc(X53)
      | ~ m1_subset_1(X54,k1_zfmisc_1(u1_struct_0(X53)))
      | m1_subset_1(k2_tops_1(X53,X54),k1_zfmisc_1(u1_struct_0(X53))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_tops_1])])).

cnf(c_0_52,plain,
    ( k2_tops_1(X1,X2) = k2_tops_1(X1,k3_subset_1(u1_struct_0(X1),X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_53,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_54,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_55,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_56,plain,
    ( m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

fof(c_0_57,plain,(
    ! [X16] : k2_xboole_0(X16,k1_xboole_0) = X16 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

fof(c_0_58,plain,(
    ! [X14,X15] :
      ( ~ r1_tarski(X14,X15)
      | k2_xboole_0(X14,X15) = X15 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_59,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_60,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_61,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_62,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_63,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

fof(c_0_64,plain,(
    ! [X8,X9] :
      ( ( r1_tarski(X8,X9)
        | X8 != X9 )
      & ( r1_tarski(X9,X8)
        | X8 != X9 )
      & ( ~ r1_tarski(X8,X9)
        | ~ r1_tarski(X9,X8)
        | X8 = X9 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_65,plain,(
    ! [X66,X67] :
      ( ~ l1_pre_topc(X66)
      | ~ m1_subset_1(X67,k1_zfmisc_1(u1_struct_0(X66)))
      | k1_tops_1(X66,X67) = k7_subset_1(u1_struct_0(X66),X67,k2_tops_1(X66,X67)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t74_tops_1])])])).

cnf(c_0_66,plain,
    ( k7_subset_1(X2,X1,X3) = k4_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_67,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_68,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k2_xboole_0(X1,X2)))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_69,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_70,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_71,plain,
    ( m1_subset_1(k2_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_72,negated_conjecture,
    ( k2_tops_1(esk1_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0)) = k2_tops_1(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_54])])).

cnf(c_0_73,plain,
    ( r1_tarski(k3_subset_1(X1,X2),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_74,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_75,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_76,plain,
    ( r1_tarski(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),X1) ),
    inference(rw,[status(thm)],[c_0_59,c_0_48])).

cnf(c_0_77,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))))) = k1_setfam_1(k2_tarski(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_60,c_0_35]),c_0_48]),c_0_48])).

cnf(c_0_78,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_61,c_0_48])).

cnf(c_0_79,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k1_setfam_1(k2_tarski(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_62,c_0_35]),c_0_35])).

cnf(c_0_80,plain,
    ( k3_subset_1(X2,X1) = k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_63,c_0_48])).

cnf(c_0_81,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_82,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

fof(c_0_83,plain,(
    ! [X64,X65] :
      ( ~ l1_pre_topc(X64)
      | ~ m1_subset_1(X65,k1_zfmisc_1(u1_struct_0(X64)))
      | k2_pre_topc(X64,X65) = k4_subset_1(u1_struct_0(X64),X65,k2_tops_1(X64,X65)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_tops_1])])])).

cnf(c_0_84,plain,
    ( k1_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_85,plain,
    ( k7_subset_1(X2,X1,X3) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_66,c_0_48])).

cnf(c_0_86,plain,
    ( k5_xboole_0(k2_xboole_0(X1,X2),k1_setfam_1(k2_tarski(k2_xboole_0(X1,X2),X2))) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_67,c_0_48]),c_0_48])).

cnf(c_0_87,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k2_xboole_0(X2,X1)))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_88,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k1_xboole_0))) = X1 ),
    inference(rw,[status(thm)],[c_0_70,c_0_48])).

fof(c_0_89,plain,(
    ! [X43,X44,X45] :
      ( ~ m1_subset_1(X44,k1_zfmisc_1(X43))
      | ~ m1_subset_1(X45,k1_zfmisc_1(X43))
      | k4_subset_1(X43,X44,X45) = k2_xboole_0(X44,X45) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).

cnf(c_0_90,negated_conjecture,
    ( m1_subset_1(k2_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_54])])).

cnf(c_0_91,negated_conjecture,
    ( r1_tarski(k3_subset_1(u1_struct_0(esk1_0),esk2_0),u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_73,c_0_53])).

cnf(c_0_92,plain,
    ( k1_xboole_0 = X1
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_93,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(X1,X2)),X1) ),
    inference(spm,[status(thm)],[c_0_76,c_0_77])).

cnf(c_0_94,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1))) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_78,c_0_79])).

cnf(c_0_95,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k3_subset_1(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_80,c_0_81])).

cnf(c_0_96,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_82])).

fof(c_0_97,plain,(
    ! [X40,X41,X42] :
      ( ~ m1_subset_1(X41,k1_zfmisc_1(X40))
      | ~ m1_subset_1(X42,k1_zfmisc_1(X40))
      | m1_subset_1(k4_subset_1(X40,X41,X42),k1_zfmisc_1(X40)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_subset_1])])).

cnf(c_0_98,plain,
    ( k2_pre_topc(X1,X2) = k4_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_83])).

fof(c_0_99,plain,(
    ! [X20,X21] :
      ( ~ r1_tarski(X20,X21)
      | k3_xboole_0(X20,X21) = X20 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_100,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),esk2_0,k2_tops_1(esk1_0,esk2_0)) = k1_tops_1(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_53]),c_0_54])])).

cnf(c_0_101,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1) = k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(esk2_0,X1))) ),
    inference(spm,[status(thm)],[c_0_85,c_0_53])).

cnf(c_0_102,plain,
    ( k5_xboole_0(k2_xboole_0(X1,X2),k1_setfam_1(k2_tarski(X2,k2_xboole_0(X1,X2)))) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_86,c_0_79])).

cnf(c_0_103,plain,
    ( k1_setfam_1(k2_tarski(X1,k2_xboole_0(X2,X1))) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_87]),c_0_88])).

fof(c_0_104,plain,(
    ! [X29,X30,X31] :
      ( ~ r1_tarski(k4_xboole_0(X29,X30),X31)
      | r1_tarski(X29,k2_xboole_0(X30,X31)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_xboole_1])])).

fof(c_0_105,plain,(
    ! [X24,X25] : k2_xboole_0(X24,k4_xboole_0(X25,X24)) = k2_xboole_0(X24,X25) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

cnf(c_0_106,plain,
    ( k4_subset_1(X2,X1,X3) = k2_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_89])).

cnf(c_0_107,negated_conjecture,
    ( m1_subset_1(k2_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_81]),c_0_91])])).

cnf(c_0_108,plain,
    ( r1_tarski(X1,X2)
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_109,plain,
    ( k1_setfam_1(k2_tarski(k1_xboole_0,X1)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_92,c_0_93])).

cnf(c_0_110,plain,
    ( k3_subset_1(X1,X1) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_95]),c_0_96])])).

cnf(c_0_111,plain,
    ( m1_subset_1(k4_subset_1(X2,X1,X3),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_97])).

cnf(c_0_112,negated_conjecture,
    ( k4_subset_1(u1_struct_0(esk1_0),esk2_0,k2_tops_1(esk1_0,esk2_0)) = k2_pre_topc(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_53]),c_0_54])])).

cnf(c_0_113,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_99])).

cnf(c_0_114,negated_conjecture,
    ( k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(esk2_0,k2_tops_1(esk1_0,esk2_0)))) = k1_tops_1(esk1_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_100,c_0_101])).

cnf(c_0_115,plain,
    ( k5_xboole_0(k2_xboole_0(X1,X2),X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_102,c_0_103])).

cnf(c_0_116,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r1_tarski(k4_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_104])).

cnf(c_0_117,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_105])).

cnf(c_0_118,negated_conjecture,
    ( k4_subset_1(u1_struct_0(esk1_0),X1,k2_tops_1(esk1_0,esk2_0)) = k2_xboole_0(X1,k2_tops_1(esk1_0,esk2_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_106,c_0_107])).

cnf(c_0_119,plain,
    ( r1_tarski(X1,X2)
    | k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_108,c_0_48])).

cnf(c_0_120,plain,
    ( k1_setfam_1(k2_tarski(X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_79,c_0_109])).

cnf(c_0_121,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_109]),c_0_74]),c_0_88])).

cnf(c_0_122,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_76,c_0_68])).

cnf(c_0_123,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_110])).

cnf(c_0_124,negated_conjecture,
    ( m1_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(k2_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111,c_0_112]),c_0_53])])).

cnf(c_0_125,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_113,c_0_35])).

cnf(c_0_126,negated_conjecture,
    ( k1_setfam_1(k2_tarski(esk2_0,k2_tops_1(esk1_0,esk2_0))) = k5_xboole_0(k2_xboole_0(esk2_0,k1_tops_1(esk1_0,esk2_0)),k1_tops_1(esk1_0,esk2_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_114]),c_0_115])).

cnf(c_0_127,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r1_tarski(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),X3) ),
    inference(rw,[status(thm)],[c_0_116,c_0_48])).

cnf(c_0_128,plain,
    ( k2_xboole_0(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_117,c_0_48])).

cnf(c_0_129,plain,
    ( k1_setfam_1(k2_tarski(X1,k2_xboole_0(X1,X2))) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_68]),c_0_88])).

cnf(c_0_130,negated_conjecture,
    ( k2_xboole_0(esk2_0,k2_tops_1(esk1_0,esk2_0)) = k2_pre_topc(esk1_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_118,c_0_53]),c_0_112])).

cnf(c_0_131,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_119,c_0_68])).

cnf(c_0_132,plain,
    ( k3_subset_1(X1,k1_xboole_0) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_120]),c_0_121]),c_0_122])])).

cnf(c_0_133,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_123,c_0_81]),c_0_96])])).

cnf(c_0_134,negated_conjecture,
    ( m1_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_124,c_0_107])])).

cnf(c_0_135,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = X2
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_125,c_0_79])).

cnf(c_0_136,negated_conjecture,
    ( k5_xboole_0(esk2_0,k5_xboole_0(k2_xboole_0(esk2_0,k1_tops_1(esk1_0,esk2_0)),k1_tops_1(esk1_0,esk2_0))) = k1_tops_1(esk1_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_114,c_0_126])).

cnf(c_0_137,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_127,c_0_96]),c_0_128])).

cnf(c_0_138,plain,
    ( k2_xboole_0(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X1,X2)))) = k2_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_128,c_0_79])).

cnf(c_0_139,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_128,c_0_68]),c_0_74]),c_0_69])).

cnf(c_0_140,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1))) = k3_subset_1(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_95,c_0_79])).

cnf(c_0_141,negated_conjecture,
    ( k1_setfam_1(k2_tarski(esk2_0,k2_pre_topc(esk1_0,esk2_0))) = esk2_0 ),
    inference(spm,[status(thm)],[c_0_129,c_0_130])).

cnf(c_0_142,negated_conjecture,
    ( r1_tarski(esk2_0,k2_pre_topc(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_131,c_0_130])).

cnf(c_0_143,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_132]),c_0_133])])).

cnf(c_0_144,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1)))))) = k1_setfam_1(k2_tarski(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_77,c_0_79])).

cnf(c_0_145,negated_conjecture,
    ( k5_xboole_0(k2_pre_topc(esk1_0,esk2_0),k1_setfam_1(k2_tarski(k2_pre_topc(esk1_0,esk2_0),X1))) = k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),X1) ),
    inference(spm,[status(thm)],[c_0_85,c_0_134])).

cnf(c_0_146,plain,
    ( k5_xboole_0(X1,X2) = k3_subset_1(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_95,c_0_135])).

cnf(c_0_147,negated_conjecture,
    ( k5_xboole_0(k2_pre_topc(esk1_0,esk2_0),k2_tops_1(esk1_0,esk2_0)) = k1_tops_1(esk1_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115,c_0_130]),c_0_126]),c_0_136])).

cnf(c_0_148,negated_conjecture,
    ( r1_tarski(k2_tops_1(esk1_0,esk2_0),k2_pre_topc(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_137,c_0_130])).

cnf(c_0_149,plain,
    ( k1_setfam_1(k2_tarski(k2_xboole_0(X1,X2),k5_xboole_0(X2,k1_setfam_1(k2_tarski(X1,X2))))) = k5_xboole_0(X2,k1_setfam_1(k2_tarski(X1,X2))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_138]),c_0_79])).

cnf(c_0_150,negated_conjecture,
    ( k2_xboole_0(esk2_0,k2_pre_topc(esk1_0,esk2_0)) = k2_pre_topc(esk1_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_139,c_0_130])).

cnf(c_0_151,negated_conjecture,
    ( k5_xboole_0(k2_pre_topc(esk1_0,esk2_0),esk2_0) = k3_subset_1(k2_pre_topc(esk1_0,esk2_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_140,c_0_141]),c_0_142])])).

cnf(c_0_152,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k7_subset_1(X1,X1,X2) ),
    inference(spm,[status(thm)],[c_0_85,c_0_143])).

cnf(c_0_153,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),k5_xboole_0(k2_pre_topc(esk1_0,esk2_0),esk2_0)) = esk2_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_144,c_0_141]),c_0_145])).

cnf(c_0_154,plain,
    ( r1_tarski(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1))),X1) ),
    inference(spm,[status(thm)],[c_0_76,c_0_79])).

cnf(c_0_155,negated_conjecture,
    ( k3_subset_1(k2_pre_topc(esk1_0,esk2_0),k2_tops_1(esk1_0,esk2_0)) = k1_tops_1(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_146,c_0_147]),c_0_148])])).

cnf(c_0_156,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k5_xboole_0(X1,X2)))) = X2
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_77,c_0_135])).

cnf(c_0_157,negated_conjecture,
    ( k1_setfam_1(k2_tarski(k2_pre_topc(esk1_0,esk2_0),k3_subset_1(k2_pre_topc(esk1_0,esk2_0),esk2_0))) = k3_subset_1(k2_pre_topc(esk1_0,esk2_0),esk2_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_149,c_0_150]),c_0_141]),c_0_151]),c_0_141]),c_0_151])).

cnf(c_0_158,negated_conjecture,
    ( k7_subset_1(k2_pre_topc(esk1_0,esk2_0),k2_pre_topc(esk1_0,esk2_0),X1) = k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),X1) ),
    inference(rw,[status(thm)],[c_0_145,c_0_152])).

cnf(c_0_159,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),k3_subset_1(k2_pre_topc(esk1_0,esk2_0),esk2_0)) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_153,c_0_146]),c_0_142])])).

cnf(c_0_160,plain,
    ( r1_tarski(k5_xboole_0(k2_xboole_0(X1,X2),X1),k2_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_154,c_0_129])).

cnf(c_0_161,negated_conjecture,
    ( m1_subset_1(k1_tops_1(esk1_0,esk2_0),k1_zfmisc_1(k2_pre_topc(esk1_0,esk2_0)))
    | ~ m1_subset_1(k2_tops_1(esk1_0,esk2_0),k1_zfmisc_1(k2_pre_topc(esk1_0,esk2_0))) ),
    inference(spm,[status(thm)],[c_0_56,c_0_155])).

fof(c_0_162,plain,(
    ! [X59,X60,X61] :
      ( ~ l1_pre_topc(X59)
      | ~ m1_subset_1(X60,k1_zfmisc_1(u1_struct_0(X59)))
      | ~ m1_subset_1(X61,k1_zfmisc_1(u1_struct_0(X59)))
      | ~ v3_pre_topc(X60,X59)
      | ~ r1_tarski(X60,X61)
      | r1_tarski(X60,k1_tops_1(X59,X61)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t56_tops_1])])])).

fof(c_0_163,plain,(
    ! [X17,X18,X19] :
      ( ~ r1_tarski(X17,X18)
      | ~ r1_tarski(X18,X19)
      | r1_tarski(X17,X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

cnf(c_0_164,plain,
    ( k7_subset_1(X1,X1,k5_xboole_0(X1,X2)) = X2
    | ~ r1_tarski(X2,X1) ),
    inference(rw,[status(thm)],[c_0_156,c_0_152])).

cnf(c_0_165,negated_conjecture,
    ( k5_xboole_0(k2_pre_topc(esk1_0,esk2_0),k3_subset_1(k2_pre_topc(esk1_0,esk2_0),esk2_0)) = esk2_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_152,c_0_157]),c_0_158]),c_0_159])).

cnf(c_0_166,negated_conjecture,
    ( r1_tarski(k3_subset_1(k2_pre_topc(esk1_0,esk2_0),esk2_0),k2_pre_topc(esk1_0,esk2_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_160,c_0_130]),c_0_151])).

cnf(c_0_167,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k3_subset_1(X1,X2)))) = k3_subset_1(X1,k3_subset_1(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_80,c_0_56])).

cnf(c_0_168,negated_conjecture,
    ( m1_subset_1(k1_tops_1(esk1_0,esk2_0),k1_zfmisc_1(k2_pre_topc(esk1_0,esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_161,c_0_81]),c_0_148])])).

cnf(c_0_169,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),k1_tops_1(esk1_0,esk2_0)) = k2_tops_1(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_156,c_0_147]),c_0_145]),c_0_148])])).

cnf(c_0_170,plain,
    ( r1_tarski(k5_xboole_0(X1,X2),X1)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_154,c_0_125])).

cnf(c_0_171,plain,
    ( r1_tarski(X2,k1_tops_1(X1,X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(X2,X1)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_162])).

cnf(c_0_172,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_163])).

cnf(c_0_173,negated_conjecture,
    ( r1_tarski(esk2_0,u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_55,c_0_53])).

cnf(c_0_174,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k3_subset_1(X1,X2)))) = k1_setfam_1(k2_tarski(X1,X2))
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_77,c_0_95])).

cnf(c_0_175,negated_conjecture,
    ( v3_pre_topc(esk2_0,esk1_0)
    | k2_tops_1(esk1_0,esk2_0) = k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_176,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),esk2_0) = k3_subset_1(k2_pre_topc(esk1_0,esk2_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_164,c_0_165]),c_0_158]),c_0_166])])).

cnf(c_0_177,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k3_subset_1(X1,X2)))) = k3_subset_1(X1,k3_subset_1(X1,X2))
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_167,c_0_81])).

cnf(c_0_178,negated_conjecture,
    ( k3_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_tops_1(esk1_0,esk2_0)) = k2_tops_1(esk1_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_168]),c_0_145]),c_0_169])).

cnf(c_0_179,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,esk2_0),k2_pre_topc(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_170,c_0_147]),c_0_148])])).

cnf(c_0_180,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

fof(c_0_181,plain,(
    ! [X55,X56] :
      ( ~ v2_pre_topc(X55)
      | ~ l1_pre_topc(X55)
      | ~ m1_subset_1(X56,k1_zfmisc_1(u1_struct_0(X55)))
      | v3_pre_topc(k1_tops_1(X55,X56),X55) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc9_tops_1])])).

cnf(c_0_182,negated_conjecture,
    ( r1_tarski(X1,k1_tops_1(esk1_0,esk2_0))
    | ~ v3_pre_topc(X1,esk1_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_tarski(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_171,c_0_53]),c_0_54])])).

cnf(c_0_183,negated_conjecture,
    ( r1_tarski(X1,u1_struct_0(esk1_0))
    | ~ r1_tarski(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_172,c_0_173])).

cnf(c_0_184,plain,
    ( k7_subset_1(X1,X1,k3_subset_1(X1,X2)) = k1_setfam_1(k2_tarski(X1,X2))
    | ~ r1_tarski(X2,X1) ),
    inference(rw,[status(thm)],[c_0_174,c_0_152])).

cnf(c_0_185,negated_conjecture,
    ( k3_subset_1(k2_pre_topc(esk1_0,esk2_0),esk2_0) = k2_tops_1(esk1_0,esk2_0)
    | v3_pre_topc(esk2_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_175,c_0_176])).

cnf(c_0_186,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),k2_tops_1(esk1_0,esk2_0)) = k1_tops_1(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_177,c_0_178]),c_0_145]),c_0_155]),c_0_179])])).

cnf(c_0_187,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = X1
    | ~ r1_tarski(X1,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))) ),
    inference(spm,[status(thm)],[c_0_180,c_0_76])).

cnf(c_0_188,plain,
    ( r1_tarski(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1))),k2_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_137,c_0_138])).

cnf(c_0_189,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X2,X1)) = k2_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_139,c_0_69])).

cnf(c_0_190,plain,
    ( v3_pre_topc(k1_tops_1(X1,X2),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_181])).

cnf(c_0_191,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_192,negated_conjecture,
    ( r1_tarski(X1,k1_tops_1(esk1_0,esk2_0))
    | ~ v3_pre_topc(X1,esk1_0)
    | ~ r1_tarski(X1,esk2_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_182,c_0_81]),c_0_183])).

cnf(c_0_193,negated_conjecture,
    ( k1_tops_1(esk1_0,esk2_0) = esk2_0
    | v3_pre_topc(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_184,c_0_185]),c_0_158]),c_0_186]),c_0_79]),c_0_141]),c_0_142])])).

cnf(c_0_194,negated_conjecture,
    ( k1_tops_1(esk1_0,esk2_0) = esk2_0
    | ~ r1_tarski(esk2_0,k1_tops_1(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_187,c_0_114])).

cnf(c_0_195,plain,
    ( k5_xboole_0(k2_xboole_0(X1,X2),k5_xboole_0(X2,k1_setfam_1(k2_tarski(X1,X2)))) = k3_subset_1(k2_xboole_0(X1,X2),k5_xboole_0(X2,k1_setfam_1(k2_tarski(X1,X2)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_149]),c_0_188])])).

cnf(c_0_196,negated_conjecture,
    ( k1_setfam_1(k2_tarski(k2_tops_1(esk1_0,esk2_0),k2_pre_topc(esk1_0,esk2_0))) = k2_tops_1(esk1_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_103,c_0_130])).

cnf(c_0_197,negated_conjecture,
    ( k2_xboole_0(k2_tops_1(esk1_0,esk2_0),k2_pre_topc(esk1_0,esk2_0)) = k2_pre_topc(esk1_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_189,c_0_130])).

cnf(c_0_198,negated_conjecture,
    ( ~ v3_pre_topc(esk2_0,esk1_0)
    | k2_tops_1(esk1_0,esk2_0) != k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_199,negated_conjecture,
    ( v3_pre_topc(k1_tops_1(esk1_0,esk2_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_190,c_0_53]),c_0_191]),c_0_54])])).

cnf(c_0_200,negated_conjecture,
    ( k1_tops_1(esk1_0,esk2_0) = esk2_0 ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_192,c_0_193]),c_0_96])]),c_0_194])).

cnf(c_0_201,negated_conjecture,
    ( k5_xboole_0(k2_pre_topc(esk1_0,esk2_0),k1_tops_1(esk1_0,esk2_0)) = k2_tops_1(esk1_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_195,c_0_196]),c_0_197]),c_0_147]),c_0_197]),c_0_147]),c_0_178])).

cnf(c_0_202,negated_conjecture,
    ( k3_subset_1(k2_pre_topc(esk1_0,esk2_0),esk2_0) != k2_tops_1(esk1_0,esk2_0)
    | ~ v3_pre_topc(esk2_0,esk1_0) ),
    inference(rw,[status(thm)],[c_0_198,c_0_176])).

cnf(c_0_203,negated_conjecture,
    ( v3_pre_topc(esk2_0,esk1_0) ),
    inference(rw,[status(thm)],[c_0_199,c_0_200])).

cnf(c_0_204,negated_conjecture,
    ( k3_subset_1(k2_pre_topc(esk1_0,esk2_0),esk2_0) = k2_tops_1(esk1_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_201,c_0_200]),c_0_151])).

cnf(c_0_205,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_202,c_0_203])]),c_0_204])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 16:16:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 2.69/2.86  # AutoSched0-Mode selected heuristic G_E___107_C36_F1_PI_AE_Q4_CS_SP_PS_S0Y
% 2.69/2.86  # and selection function SelectMaxLComplexAvoidPosPred.
% 2.69/2.86  #
% 2.69/2.86  # Preprocessing time       : 0.030 s
% 2.69/2.86  # Presaturation interreduction done
% 2.69/2.86  
% 2.69/2.86  # Proof found!
% 2.69/2.86  # SZS status Theorem
% 2.69/2.86  # SZS output start CNFRefutation
% 2.69/2.86  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.69/2.86  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.69/2.86  fof(t76_tops_1, conjecture, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>k2_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_tops_1)).
% 2.69/2.86  fof(t46_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 2.69/2.86  fof(t62_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k2_tops_1(X1,X2)=k2_tops_1(X1,k3_subset_1(u1_struct_0(X1),X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_tops_1)).
% 2.69/2.86  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.69/2.86  fof(dt_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 2.69/2.86  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.69/2.86  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.69/2.86  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.69/2.86  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.69/2.86  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 2.69/2.86  fof(redefinition_k7_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k7_subset_1(X1,X2,X3)=k4_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 2.69/2.86  fof(t40_xboole_1, axiom, ![X1, X2]:k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 2.69/2.86  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.69/2.86  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 2.69/2.86  fof(dt_k2_tops_1, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>m1_subset_1(k2_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 2.69/2.86  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 2.69/2.86  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.69/2.86  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.69/2.86  fof(t74_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k1_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_tops_1)).
% 2.69/2.86  fof(t65_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k2_pre_topc(X1,X2)=k4_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tops_1)).
% 2.69/2.86  fof(redefinition_k4_subset_1, axiom, ![X1, X2, X3]:((m1_subset_1(X2,k1_zfmisc_1(X1))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>k4_subset_1(X1,X2,X3)=k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 2.69/2.86  fof(dt_k4_subset_1, axiom, ![X1, X2, X3]:((m1_subset_1(X2,k1_zfmisc_1(X1))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>m1_subset_1(k4_subset_1(X1,X2,X3),k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_subset_1)).
% 2.69/2.86  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.69/2.86  fof(t44_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(k4_xboole_0(X1,X2),X3)=>r1_tarski(X1,k2_xboole_0(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_xboole_1)).
% 2.69/2.86  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 2.69/2.86  fof(t56_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((v3_pre_topc(X2,X1)&r1_tarski(X2,X3))=>r1_tarski(X2,k1_tops_1(X1,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_tops_1)).
% 2.69/2.86  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 2.69/2.86  fof(fc9_tops_1, axiom, ![X1, X2]:(((v2_pre_topc(X1)&l1_pre_topc(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>v3_pre_topc(k1_tops_1(X1,X2),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_tops_1)).
% 2.69/2.86  fof(c_0_30, plain, ![X12, X13]:k4_xboole_0(X12,X13)=k5_xboole_0(X12,k3_xboole_0(X12,X13)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 2.69/2.86  fof(c_0_31, plain, ![X49, X50]:k1_setfam_1(k2_tarski(X49,X50))=k3_xboole_0(X49,X50), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 2.69/2.86  fof(c_0_32, negated_conjecture, ~(![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>k2_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),X2))))), inference(assume_negation,[status(cth)],[t76_tops_1])).
% 2.69/2.86  fof(c_0_33, plain, ![X32, X33]:k4_xboole_0(X32,k2_xboole_0(X32,X33))=k1_xboole_0, inference(variable_rename,[status(thm)],[t46_xboole_1])).
% 2.69/2.86  cnf(c_0_34, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 2.69/2.86  cnf(c_0_35, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 2.69/2.86  fof(c_0_36, plain, ![X62, X63]:(~l1_pre_topc(X62)|(~m1_subset_1(X63,k1_zfmisc_1(u1_struct_0(X62)))|k2_tops_1(X62,X63)=k2_tops_1(X62,k3_subset_1(u1_struct_0(X62),X63)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t62_tops_1])])])).
% 2.69/2.86  fof(c_0_37, negated_conjecture, ((v2_pre_topc(esk1_0)&l1_pre_topc(esk1_0))&(m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&((~v3_pre_topc(esk2_0,esk1_0)|k2_tops_1(esk1_0,esk2_0)!=k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),esk2_0))&(v3_pre_topc(esk2_0,esk1_0)|k2_tops_1(esk1_0,esk2_0)=k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),esk2_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_32])])])).
% 2.69/2.86  fof(c_0_38, plain, ![X51, X52]:((~m1_subset_1(X51,k1_zfmisc_1(X52))|r1_tarski(X51,X52))&(~r1_tarski(X51,X52)|m1_subset_1(X51,k1_zfmisc_1(X52)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 2.69/2.86  fof(c_0_39, plain, ![X38, X39]:(~m1_subset_1(X39,k1_zfmisc_1(X38))|m1_subset_1(k3_subset_1(X38,X39),k1_zfmisc_1(X38))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).
% 2.69/2.86  fof(c_0_40, plain, ![X22, X23]:r1_tarski(k4_xboole_0(X22,X23),X22), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 2.69/2.86  fof(c_0_41, plain, ![X34, X35]:k4_xboole_0(X34,k4_xboole_0(X34,X35))=k3_xboole_0(X34,X35), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 2.69/2.86  fof(c_0_42, plain, ![X10, X11]:((k4_xboole_0(X10,X11)!=k1_xboole_0|r1_tarski(X10,X11))&(~r1_tarski(X10,X11)|k4_xboole_0(X10,X11)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 2.69/2.86  fof(c_0_43, plain, ![X6, X7]:k3_xboole_0(X6,X7)=k3_xboole_0(X7,X6), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 2.69/2.86  fof(c_0_44, plain, ![X36, X37]:(~m1_subset_1(X37,k1_zfmisc_1(X36))|k3_subset_1(X36,X37)=k4_xboole_0(X36,X37)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 2.69/2.86  fof(c_0_45, plain, ![X46, X47, X48]:(~m1_subset_1(X47,k1_zfmisc_1(X46))|k7_subset_1(X46,X47,X48)=k4_xboole_0(X47,X48)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).
% 2.69/2.86  fof(c_0_46, plain, ![X27, X28]:k4_xboole_0(k2_xboole_0(X27,X28),X28)=k4_xboole_0(X27,X28), inference(variable_rename,[status(thm)],[t40_xboole_1])).
% 2.69/2.86  cnf(c_0_47, plain, (k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_33])).
% 2.69/2.86  cnf(c_0_48, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))), inference(rw,[status(thm)],[c_0_34, c_0_35])).
% 2.69/2.86  fof(c_0_49, plain, ![X4, X5]:k2_xboole_0(X4,X5)=k2_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 2.69/2.86  fof(c_0_50, plain, ![X26]:k4_xboole_0(X26,k1_xboole_0)=X26, inference(variable_rename,[status(thm)],[t3_boole])).
% 2.69/2.86  fof(c_0_51, plain, ![X53, X54]:(~l1_pre_topc(X53)|~m1_subset_1(X54,k1_zfmisc_1(u1_struct_0(X53)))|m1_subset_1(k2_tops_1(X53,X54),k1_zfmisc_1(u1_struct_0(X53)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_tops_1])])).
% 2.69/2.86  cnf(c_0_52, plain, (k2_tops_1(X1,X2)=k2_tops_1(X1,k3_subset_1(u1_struct_0(X1),X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 2.69/2.86  cnf(c_0_53, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 2.69/2.86  cnf(c_0_54, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 2.69/2.86  cnf(c_0_55, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 2.69/2.86  cnf(c_0_56, plain, (m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 2.69/2.86  fof(c_0_57, plain, ![X16]:k2_xboole_0(X16,k1_xboole_0)=X16, inference(variable_rename,[status(thm)],[t1_boole])).
% 2.69/2.86  fof(c_0_58, plain, ![X14, X15]:(~r1_tarski(X14,X15)|k2_xboole_0(X14,X15)=X15), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 2.69/2.86  cnf(c_0_59, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 2.69/2.86  cnf(c_0_60, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 2.69/2.86  cnf(c_0_61, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 2.69/2.86  cnf(c_0_62, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 2.69/2.86  cnf(c_0_63, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 2.69/2.86  fof(c_0_64, plain, ![X8, X9]:(((r1_tarski(X8,X9)|X8!=X9)&(r1_tarski(X9,X8)|X8!=X9))&(~r1_tarski(X8,X9)|~r1_tarski(X9,X8)|X8=X9)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 2.69/2.86  fof(c_0_65, plain, ![X66, X67]:(~l1_pre_topc(X66)|(~m1_subset_1(X67,k1_zfmisc_1(u1_struct_0(X66)))|k1_tops_1(X66,X67)=k7_subset_1(u1_struct_0(X66),X67,k2_tops_1(X66,X67)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t74_tops_1])])])).
% 2.69/2.86  cnf(c_0_66, plain, (k7_subset_1(X2,X1,X3)=k4_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_45])).
% 2.69/2.86  cnf(c_0_67, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 2.69/2.86  cnf(c_0_68, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k2_xboole_0(X1,X2))))=k1_xboole_0), inference(rw,[status(thm)],[c_0_47, c_0_48])).
% 2.69/2.86  cnf(c_0_69, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 2.69/2.86  cnf(c_0_70, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_50])).
% 2.69/2.86  cnf(c_0_71, plain, (m1_subset_1(k2_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_51])).
% 2.69/2.86  cnf(c_0_72, negated_conjecture, (k2_tops_1(esk1_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0))=k2_tops_1(esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_54])])).
% 2.69/2.86  cnf(c_0_73, plain, (r1_tarski(k3_subset_1(X1,X2),X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 2.69/2.86  cnf(c_0_74, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_57])).
% 2.69/2.86  cnf(c_0_75, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 2.69/2.86  cnf(c_0_76, plain, (r1_tarski(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),X1)), inference(rw,[status(thm)],[c_0_59, c_0_48])).
% 2.69/2.86  cnf(c_0_77, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))))))=k1_setfam_1(k2_tarski(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_60, c_0_35]), c_0_48]), c_0_48])).
% 2.69/2.86  cnf(c_0_78, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))=k1_xboole_0|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_61, c_0_48])).
% 2.69/2.86  cnf(c_0_79, plain, (k1_setfam_1(k2_tarski(X1,X2))=k1_setfam_1(k2_tarski(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_62, c_0_35]), c_0_35])).
% 2.69/2.86  cnf(c_0_80, plain, (k3_subset_1(X2,X1)=k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_63, c_0_48])).
% 2.69/2.86  cnf(c_0_81, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 2.69/2.86  cnf(c_0_82, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_64])).
% 2.69/2.86  fof(c_0_83, plain, ![X64, X65]:(~l1_pre_topc(X64)|(~m1_subset_1(X65,k1_zfmisc_1(u1_struct_0(X64)))|k2_pre_topc(X64,X65)=k4_subset_1(u1_struct_0(X64),X65,k2_tops_1(X64,X65)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_tops_1])])])).
% 2.69/2.86  cnf(c_0_84, plain, (k1_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_65])).
% 2.69/2.86  cnf(c_0_85, plain, (k7_subset_1(X2,X1,X3)=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X3)))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_66, c_0_48])).
% 2.69/2.86  cnf(c_0_86, plain, (k5_xboole_0(k2_xboole_0(X1,X2),k1_setfam_1(k2_tarski(k2_xboole_0(X1,X2),X2)))=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_67, c_0_48]), c_0_48])).
% 2.69/2.86  cnf(c_0_87, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k2_xboole_0(X2,X1))))=k1_xboole_0), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 2.69/2.86  cnf(c_0_88, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k1_xboole_0)))=X1), inference(rw,[status(thm)],[c_0_70, c_0_48])).
% 2.69/2.86  fof(c_0_89, plain, ![X43, X44, X45]:(~m1_subset_1(X44,k1_zfmisc_1(X43))|~m1_subset_1(X45,k1_zfmisc_1(X43))|k4_subset_1(X43,X44,X45)=k2_xboole_0(X44,X45)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).
% 2.69/2.86  cnf(c_0_90, negated_conjecture, (m1_subset_1(k2_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_54])])).
% 2.69/2.86  cnf(c_0_91, negated_conjecture, (r1_tarski(k3_subset_1(u1_struct_0(esk1_0),esk2_0),u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_73, c_0_53])).
% 2.69/2.86  cnf(c_0_92, plain, (k1_xboole_0=X1|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_74, c_0_75])).
% 2.69/2.86  cnf(c_0_93, plain, (r1_tarski(k1_setfam_1(k2_tarski(X1,X2)),X1)), inference(spm,[status(thm)],[c_0_76, c_0_77])).
% 2.69/2.86  cnf(c_0_94, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1)))=k1_xboole_0|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_78, c_0_79])).
% 2.69/2.86  cnf(c_0_95, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))=k3_subset_1(X1,X2)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_80, c_0_81])).
% 2.69/2.86  cnf(c_0_96, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_82])).
% 2.69/2.86  fof(c_0_97, plain, ![X40, X41, X42]:(~m1_subset_1(X41,k1_zfmisc_1(X40))|~m1_subset_1(X42,k1_zfmisc_1(X40))|m1_subset_1(k4_subset_1(X40,X41,X42),k1_zfmisc_1(X40))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_subset_1])])).
% 2.69/2.86  cnf(c_0_98, plain, (k2_pre_topc(X1,X2)=k4_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_83])).
% 2.69/2.86  fof(c_0_99, plain, ![X20, X21]:(~r1_tarski(X20,X21)|k3_xboole_0(X20,X21)=X20), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 2.69/2.86  cnf(c_0_100, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),esk2_0,k2_tops_1(esk1_0,esk2_0))=k1_tops_1(esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_53]), c_0_54])])).
% 2.69/2.86  cnf(c_0_101, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1)=k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(esk2_0,X1)))), inference(spm,[status(thm)],[c_0_85, c_0_53])).
% 2.69/2.86  cnf(c_0_102, plain, (k5_xboole_0(k2_xboole_0(X1,X2),k1_setfam_1(k2_tarski(X2,k2_xboole_0(X1,X2))))=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))), inference(rw,[status(thm)],[c_0_86, c_0_79])).
% 2.69/2.86  cnf(c_0_103, plain, (k1_setfam_1(k2_tarski(X1,k2_xboole_0(X2,X1)))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_87]), c_0_88])).
% 2.69/2.86  fof(c_0_104, plain, ![X29, X30, X31]:(~r1_tarski(k4_xboole_0(X29,X30),X31)|r1_tarski(X29,k2_xboole_0(X30,X31))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_xboole_1])])).
% 2.69/2.86  fof(c_0_105, plain, ![X24, X25]:k2_xboole_0(X24,k4_xboole_0(X25,X24))=k2_xboole_0(X24,X25), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 2.69/2.86  cnf(c_0_106, plain, (k4_subset_1(X2,X1,X3)=k2_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_89])).
% 2.69/2.86  cnf(c_0_107, negated_conjecture, (m1_subset_1(k2_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_81]), c_0_91])])).
% 2.69/2.86  cnf(c_0_108, plain, (r1_tarski(X1,X2)|k4_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_42])).
% 2.69/2.86  cnf(c_0_109, plain, (k1_setfam_1(k2_tarski(k1_xboole_0,X1))=k1_xboole_0), inference(spm,[status(thm)],[c_0_92, c_0_93])).
% 2.69/2.86  cnf(c_0_110, plain, (k3_subset_1(X1,X1)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_95]), c_0_96])])).
% 2.69/2.86  cnf(c_0_111, plain, (m1_subset_1(k4_subset_1(X2,X1,X3),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_97])).
% 2.69/2.86  cnf(c_0_112, negated_conjecture, (k4_subset_1(u1_struct_0(esk1_0),esk2_0,k2_tops_1(esk1_0,esk2_0))=k2_pre_topc(esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_53]), c_0_54])])).
% 2.69/2.86  cnf(c_0_113, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_99])).
% 2.69/2.86  cnf(c_0_114, negated_conjecture, (k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(esk2_0,k2_tops_1(esk1_0,esk2_0))))=k1_tops_1(esk1_0,esk2_0)), inference(rw,[status(thm)],[c_0_100, c_0_101])).
% 2.69/2.86  cnf(c_0_115, plain, (k5_xboole_0(k2_xboole_0(X1,X2),X2)=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))), inference(rw,[status(thm)],[c_0_102, c_0_103])).
% 2.69/2.86  cnf(c_0_116, plain, (r1_tarski(X1,k2_xboole_0(X2,X3))|~r1_tarski(k4_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_104])).
% 2.69/2.86  cnf(c_0_117, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_105])).
% 2.69/2.86  cnf(c_0_118, negated_conjecture, (k4_subset_1(u1_struct_0(esk1_0),X1,k2_tops_1(esk1_0,esk2_0))=k2_xboole_0(X1,k2_tops_1(esk1_0,esk2_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_106, c_0_107])).
% 2.69/2.86  cnf(c_0_119, plain, (r1_tarski(X1,X2)|k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))!=k1_xboole_0), inference(rw,[status(thm)],[c_0_108, c_0_48])).
% 2.69/2.86  cnf(c_0_120, plain, (k1_setfam_1(k2_tarski(X1,k1_xboole_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_79, c_0_109])).
% 2.69/2.86  cnf(c_0_121, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102, c_0_109]), c_0_74]), c_0_88])).
% 2.69/2.86  cnf(c_0_122, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_76, c_0_68])).
% 2.69/2.86  cnf(c_0_123, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~m1_subset_1(X1,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_56, c_0_110])).
% 2.69/2.86  cnf(c_0_124, negated_conjecture, (m1_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(k2_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111, c_0_112]), c_0_53])])).
% 2.69/2.86  cnf(c_0_125, plain, (k1_setfam_1(k2_tarski(X1,X2))=X1|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_113, c_0_35])).
% 2.69/2.86  cnf(c_0_126, negated_conjecture, (k1_setfam_1(k2_tarski(esk2_0,k2_tops_1(esk1_0,esk2_0)))=k5_xboole_0(k2_xboole_0(esk2_0,k1_tops_1(esk1_0,esk2_0)),k1_tops_1(esk1_0,esk2_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_114]), c_0_115])).
% 2.69/2.86  cnf(c_0_127, plain, (r1_tarski(X1,k2_xboole_0(X2,X3))|~r1_tarski(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),X3)), inference(rw,[status(thm)],[c_0_116, c_0_48])).
% 2.69/2.86  cnf(c_0_128, plain, (k2_xboole_0(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1))))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_117, c_0_48])).
% 2.69/2.86  cnf(c_0_129, plain, (k1_setfam_1(k2_tarski(X1,k2_xboole_0(X1,X2)))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_68]), c_0_88])).
% 2.69/2.86  cnf(c_0_130, negated_conjecture, (k2_xboole_0(esk2_0,k2_tops_1(esk1_0,esk2_0))=k2_pre_topc(esk1_0,esk2_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_118, c_0_53]), c_0_112])).
% 2.69/2.86  cnf(c_0_131, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_119, c_0_68])).
% 2.69/2.86  cnf(c_0_132, plain, (k3_subset_1(X1,k1_xboole_0)=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_120]), c_0_121]), c_0_122])])).
% 2.69/2.86  cnf(c_0_133, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_123, c_0_81]), c_0_96])])).
% 2.69/2.86  cnf(c_0_134, negated_conjecture, (m1_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_124, c_0_107])])).
% 2.69/2.86  cnf(c_0_135, plain, (k1_setfam_1(k2_tarski(X1,X2))=X2|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_125, c_0_79])).
% 2.69/2.86  cnf(c_0_136, negated_conjecture, (k5_xboole_0(esk2_0,k5_xboole_0(k2_xboole_0(esk2_0,k1_tops_1(esk1_0,esk2_0)),k1_tops_1(esk1_0,esk2_0)))=k1_tops_1(esk1_0,esk2_0)), inference(rw,[status(thm)],[c_0_114, c_0_126])).
% 2.69/2.86  cnf(c_0_137, plain, (r1_tarski(X1,k2_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_127, c_0_96]), c_0_128])).
% 2.69/2.86  cnf(c_0_138, plain, (k2_xboole_0(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X1,X2))))=k2_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_128, c_0_79])).
% 2.69/2.86  cnf(c_0_139, plain, (k2_xboole_0(X1,k2_xboole_0(X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_128, c_0_68]), c_0_74]), c_0_69])).
% 2.69/2.86  cnf(c_0_140, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1)))=k3_subset_1(X1,X2)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_95, c_0_79])).
% 2.69/2.86  cnf(c_0_141, negated_conjecture, (k1_setfam_1(k2_tarski(esk2_0,k2_pre_topc(esk1_0,esk2_0)))=esk2_0), inference(spm,[status(thm)],[c_0_129, c_0_130])).
% 2.69/2.86  cnf(c_0_142, negated_conjecture, (r1_tarski(esk2_0,k2_pre_topc(esk1_0,esk2_0))), inference(spm,[status(thm)],[c_0_131, c_0_130])).
% 2.69/2.86  cnf(c_0_143, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_132]), c_0_133])])).
% 2.69/2.86  cnf(c_0_144, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1))))))=k1_setfam_1(k2_tarski(X2,X1))), inference(spm,[status(thm)],[c_0_77, c_0_79])).
% 2.69/2.86  cnf(c_0_145, negated_conjecture, (k5_xboole_0(k2_pre_topc(esk1_0,esk2_0),k1_setfam_1(k2_tarski(k2_pre_topc(esk1_0,esk2_0),X1)))=k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),X1)), inference(spm,[status(thm)],[c_0_85, c_0_134])).
% 2.69/2.86  cnf(c_0_146, plain, (k5_xboole_0(X1,X2)=k3_subset_1(X1,X2)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_95, c_0_135])).
% 2.69/2.86  cnf(c_0_147, negated_conjecture, (k5_xboole_0(k2_pre_topc(esk1_0,esk2_0),k2_tops_1(esk1_0,esk2_0))=k1_tops_1(esk1_0,esk2_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115, c_0_130]), c_0_126]), c_0_136])).
% 2.69/2.86  cnf(c_0_148, negated_conjecture, (r1_tarski(k2_tops_1(esk1_0,esk2_0),k2_pre_topc(esk1_0,esk2_0))), inference(spm,[status(thm)],[c_0_137, c_0_130])).
% 2.69/2.86  cnf(c_0_149, plain, (k1_setfam_1(k2_tarski(k2_xboole_0(X1,X2),k5_xboole_0(X2,k1_setfam_1(k2_tarski(X1,X2)))))=k5_xboole_0(X2,k1_setfam_1(k2_tarski(X1,X2)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103, c_0_138]), c_0_79])).
% 2.69/2.86  cnf(c_0_150, negated_conjecture, (k2_xboole_0(esk2_0,k2_pre_topc(esk1_0,esk2_0))=k2_pre_topc(esk1_0,esk2_0)), inference(spm,[status(thm)],[c_0_139, c_0_130])).
% 2.69/2.86  cnf(c_0_151, negated_conjecture, (k5_xboole_0(k2_pre_topc(esk1_0,esk2_0),esk2_0)=k3_subset_1(k2_pre_topc(esk1_0,esk2_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_140, c_0_141]), c_0_142])])).
% 2.69/2.86  cnf(c_0_152, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))=k7_subset_1(X1,X1,X2)), inference(spm,[status(thm)],[c_0_85, c_0_143])).
% 2.69/2.86  cnf(c_0_153, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),k5_xboole_0(k2_pre_topc(esk1_0,esk2_0),esk2_0))=esk2_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_144, c_0_141]), c_0_145])).
% 2.69/2.86  cnf(c_0_154, plain, (r1_tarski(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1))),X1)), inference(spm,[status(thm)],[c_0_76, c_0_79])).
% 2.69/2.86  cnf(c_0_155, negated_conjecture, (k3_subset_1(k2_pre_topc(esk1_0,esk2_0),k2_tops_1(esk1_0,esk2_0))=k1_tops_1(esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_146, c_0_147]), c_0_148])])).
% 2.69/2.86  cnf(c_0_156, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k5_xboole_0(X1,X2))))=X2|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_77, c_0_135])).
% 2.69/2.86  cnf(c_0_157, negated_conjecture, (k1_setfam_1(k2_tarski(k2_pre_topc(esk1_0,esk2_0),k3_subset_1(k2_pre_topc(esk1_0,esk2_0),esk2_0)))=k3_subset_1(k2_pre_topc(esk1_0,esk2_0),esk2_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_149, c_0_150]), c_0_141]), c_0_151]), c_0_141]), c_0_151])).
% 2.69/2.86  cnf(c_0_158, negated_conjecture, (k7_subset_1(k2_pre_topc(esk1_0,esk2_0),k2_pre_topc(esk1_0,esk2_0),X1)=k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),X1)), inference(rw,[status(thm)],[c_0_145, c_0_152])).
% 2.69/2.86  cnf(c_0_159, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),k3_subset_1(k2_pre_topc(esk1_0,esk2_0),esk2_0))=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_153, c_0_146]), c_0_142])])).
% 2.69/2.86  cnf(c_0_160, plain, (r1_tarski(k5_xboole_0(k2_xboole_0(X1,X2),X1),k2_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_154, c_0_129])).
% 2.69/2.86  cnf(c_0_161, negated_conjecture, (m1_subset_1(k1_tops_1(esk1_0,esk2_0),k1_zfmisc_1(k2_pre_topc(esk1_0,esk2_0)))|~m1_subset_1(k2_tops_1(esk1_0,esk2_0),k1_zfmisc_1(k2_pre_topc(esk1_0,esk2_0)))), inference(spm,[status(thm)],[c_0_56, c_0_155])).
% 2.69/2.86  fof(c_0_162, plain, ![X59, X60, X61]:(~l1_pre_topc(X59)|(~m1_subset_1(X60,k1_zfmisc_1(u1_struct_0(X59)))|(~m1_subset_1(X61,k1_zfmisc_1(u1_struct_0(X59)))|(~v3_pre_topc(X60,X59)|~r1_tarski(X60,X61)|r1_tarski(X60,k1_tops_1(X59,X61)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t56_tops_1])])])).
% 2.69/2.86  fof(c_0_163, plain, ![X17, X18, X19]:(~r1_tarski(X17,X18)|~r1_tarski(X18,X19)|r1_tarski(X17,X19)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 2.69/2.86  cnf(c_0_164, plain, (k7_subset_1(X1,X1,k5_xboole_0(X1,X2))=X2|~r1_tarski(X2,X1)), inference(rw,[status(thm)],[c_0_156, c_0_152])).
% 2.69/2.86  cnf(c_0_165, negated_conjecture, (k5_xboole_0(k2_pre_topc(esk1_0,esk2_0),k3_subset_1(k2_pre_topc(esk1_0,esk2_0),esk2_0))=esk2_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_152, c_0_157]), c_0_158]), c_0_159])).
% 2.69/2.86  cnf(c_0_166, negated_conjecture, (r1_tarski(k3_subset_1(k2_pre_topc(esk1_0,esk2_0),esk2_0),k2_pre_topc(esk1_0,esk2_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_160, c_0_130]), c_0_151])).
% 2.69/2.86  cnf(c_0_167, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k3_subset_1(X1,X2))))=k3_subset_1(X1,k3_subset_1(X1,X2))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_80, c_0_56])).
% 2.69/2.86  cnf(c_0_168, negated_conjecture, (m1_subset_1(k1_tops_1(esk1_0,esk2_0),k1_zfmisc_1(k2_pre_topc(esk1_0,esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_161, c_0_81]), c_0_148])])).
% 2.69/2.86  cnf(c_0_169, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),k1_tops_1(esk1_0,esk2_0))=k2_tops_1(esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_156, c_0_147]), c_0_145]), c_0_148])])).
% 2.69/2.86  cnf(c_0_170, plain, (r1_tarski(k5_xboole_0(X1,X2),X1)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_154, c_0_125])).
% 2.69/2.86  cnf(c_0_171, plain, (r1_tarski(X2,k1_tops_1(X1,X3))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v3_pre_topc(X2,X1)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_162])).
% 2.69/2.86  cnf(c_0_172, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_163])).
% 2.69/2.86  cnf(c_0_173, negated_conjecture, (r1_tarski(esk2_0,u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_55, c_0_53])).
% 2.69/2.86  cnf(c_0_174, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k3_subset_1(X1,X2))))=k1_setfam_1(k2_tarski(X1,X2))|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_77, c_0_95])).
% 2.69/2.86  cnf(c_0_175, negated_conjecture, (v3_pre_topc(esk2_0,esk1_0)|k2_tops_1(esk1_0,esk2_0)=k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),esk2_0)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 2.69/2.86  cnf(c_0_176, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),esk2_0)=k3_subset_1(k2_pre_topc(esk1_0,esk2_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_164, c_0_165]), c_0_158]), c_0_166])])).
% 2.69/2.86  cnf(c_0_177, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k3_subset_1(X1,X2))))=k3_subset_1(X1,k3_subset_1(X1,X2))|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_167, c_0_81])).
% 2.69/2.86  cnf(c_0_178, negated_conjecture, (k3_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_tops_1(esk1_0,esk2_0))=k2_tops_1(esk1_0,esk2_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_168]), c_0_145]), c_0_169])).
% 2.69/2.86  cnf(c_0_179, negated_conjecture, (r1_tarski(k1_tops_1(esk1_0,esk2_0),k2_pre_topc(esk1_0,esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_170, c_0_147]), c_0_148])])).
% 2.69/2.86  cnf(c_0_180, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_64])).
% 2.69/2.86  fof(c_0_181, plain, ![X55, X56]:(~v2_pre_topc(X55)|~l1_pre_topc(X55)|~m1_subset_1(X56,k1_zfmisc_1(u1_struct_0(X55)))|v3_pre_topc(k1_tops_1(X55,X56),X55)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc9_tops_1])])).
% 2.69/2.86  cnf(c_0_182, negated_conjecture, (r1_tarski(X1,k1_tops_1(esk1_0,esk2_0))|~v3_pre_topc(X1,esk1_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))|~r1_tarski(X1,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_171, c_0_53]), c_0_54])])).
% 2.69/2.86  cnf(c_0_183, negated_conjecture, (r1_tarski(X1,u1_struct_0(esk1_0))|~r1_tarski(X1,esk2_0)), inference(spm,[status(thm)],[c_0_172, c_0_173])).
% 2.69/2.86  cnf(c_0_184, plain, (k7_subset_1(X1,X1,k3_subset_1(X1,X2))=k1_setfam_1(k2_tarski(X1,X2))|~r1_tarski(X2,X1)), inference(rw,[status(thm)],[c_0_174, c_0_152])).
% 2.69/2.86  cnf(c_0_185, negated_conjecture, (k3_subset_1(k2_pre_topc(esk1_0,esk2_0),esk2_0)=k2_tops_1(esk1_0,esk2_0)|v3_pre_topc(esk2_0,esk1_0)), inference(spm,[status(thm)],[c_0_175, c_0_176])).
% 2.69/2.86  cnf(c_0_186, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),k2_tops_1(esk1_0,esk2_0))=k1_tops_1(esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_177, c_0_178]), c_0_145]), c_0_155]), c_0_179])])).
% 2.69/2.86  cnf(c_0_187, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))=X1|~r1_tarski(X1,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))))), inference(spm,[status(thm)],[c_0_180, c_0_76])).
% 2.69/2.86  cnf(c_0_188, plain, (r1_tarski(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1))),k2_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_137, c_0_138])).
% 2.69/2.86  cnf(c_0_189, plain, (k2_xboole_0(X1,k2_xboole_0(X2,X1))=k2_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_139, c_0_69])).
% 2.69/2.86  cnf(c_0_190, plain, (v3_pre_topc(k1_tops_1(X1,X2),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_181])).
% 2.69/2.86  cnf(c_0_191, negated_conjecture, (v2_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 2.69/2.86  cnf(c_0_192, negated_conjecture, (r1_tarski(X1,k1_tops_1(esk1_0,esk2_0))|~v3_pre_topc(X1,esk1_0)|~r1_tarski(X1,esk2_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_182, c_0_81]), c_0_183])).
% 2.69/2.86  cnf(c_0_193, negated_conjecture, (k1_tops_1(esk1_0,esk2_0)=esk2_0|v3_pre_topc(esk2_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_184, c_0_185]), c_0_158]), c_0_186]), c_0_79]), c_0_141]), c_0_142])])).
% 2.69/2.86  cnf(c_0_194, negated_conjecture, (k1_tops_1(esk1_0,esk2_0)=esk2_0|~r1_tarski(esk2_0,k1_tops_1(esk1_0,esk2_0))), inference(spm,[status(thm)],[c_0_187, c_0_114])).
% 2.69/2.86  cnf(c_0_195, plain, (k5_xboole_0(k2_xboole_0(X1,X2),k5_xboole_0(X2,k1_setfam_1(k2_tarski(X1,X2))))=k3_subset_1(k2_xboole_0(X1,X2),k5_xboole_0(X2,k1_setfam_1(k2_tarski(X1,X2))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_149]), c_0_188])])).
% 2.69/2.86  cnf(c_0_196, negated_conjecture, (k1_setfam_1(k2_tarski(k2_tops_1(esk1_0,esk2_0),k2_pre_topc(esk1_0,esk2_0)))=k2_tops_1(esk1_0,esk2_0)), inference(spm,[status(thm)],[c_0_103, c_0_130])).
% 2.69/2.86  cnf(c_0_197, negated_conjecture, (k2_xboole_0(k2_tops_1(esk1_0,esk2_0),k2_pre_topc(esk1_0,esk2_0))=k2_pre_topc(esk1_0,esk2_0)), inference(spm,[status(thm)],[c_0_189, c_0_130])).
% 2.69/2.86  cnf(c_0_198, negated_conjecture, (~v3_pre_topc(esk2_0,esk1_0)|k2_tops_1(esk1_0,esk2_0)!=k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),esk2_0)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 2.69/2.86  cnf(c_0_199, negated_conjecture, (v3_pre_topc(k1_tops_1(esk1_0,esk2_0),esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_190, c_0_53]), c_0_191]), c_0_54])])).
% 2.69/2.86  cnf(c_0_200, negated_conjecture, (k1_tops_1(esk1_0,esk2_0)=esk2_0), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_192, c_0_193]), c_0_96])]), c_0_194])).
% 2.69/2.86  cnf(c_0_201, negated_conjecture, (k5_xboole_0(k2_pre_topc(esk1_0,esk2_0),k1_tops_1(esk1_0,esk2_0))=k2_tops_1(esk1_0,esk2_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_195, c_0_196]), c_0_197]), c_0_147]), c_0_197]), c_0_147]), c_0_178])).
% 2.69/2.86  cnf(c_0_202, negated_conjecture, (k3_subset_1(k2_pre_topc(esk1_0,esk2_0),esk2_0)!=k2_tops_1(esk1_0,esk2_0)|~v3_pre_topc(esk2_0,esk1_0)), inference(rw,[status(thm)],[c_0_198, c_0_176])).
% 2.69/2.86  cnf(c_0_203, negated_conjecture, (v3_pre_topc(esk2_0,esk1_0)), inference(rw,[status(thm)],[c_0_199, c_0_200])).
% 2.69/2.86  cnf(c_0_204, negated_conjecture, (k3_subset_1(k2_pre_topc(esk1_0,esk2_0),esk2_0)=k2_tops_1(esk1_0,esk2_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_201, c_0_200]), c_0_151])).
% 2.69/2.86  cnf(c_0_205, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_202, c_0_203])]), c_0_204])]), ['proof']).
% 2.69/2.86  # SZS output end CNFRefutation
% 2.69/2.86  # Proof object total steps             : 206
% 2.69/2.86  # Proof object clause steps            : 145
% 2.69/2.86  # Proof object formula steps           : 61
% 2.69/2.86  # Proof object conjectures             : 59
% 2.69/2.86  # Proof object clause conjectures      : 56
% 2.69/2.86  # Proof object formula conjectures     : 3
% 2.69/2.86  # Proof object initial clauses used    : 37
% 2.69/2.86  # Proof object initial formulas used   : 30
% 2.69/2.86  # Proof object generating inferences   : 81
% 2.69/2.86  # Proof object simplifying inferences  : 121
% 2.69/2.86  # Training examples: 0 positive, 0 negative
% 2.69/2.86  # Parsed axioms                        : 31
% 2.69/2.86  # Removed by relevancy pruning/SinE    : 0
% 2.69/2.86  # Initial clauses                      : 39
% 2.69/2.86  # Removed in clause preprocessing      : 2
% 2.69/2.86  # Initial clauses in saturation        : 37
% 2.69/2.86  # Processed clauses                    : 39899
% 2.69/2.86  # ...of these trivial                  : 1314
% 2.69/2.86  # ...subsumed                          : 34719
% 2.69/2.86  # ...remaining for further processing  : 3865
% 2.69/2.86  # Other redundant clauses eliminated   : 2
% 2.69/2.86  # Clauses deleted for lack of memory   : 0
% 2.69/2.86  # Backward-subsumed                    : 243
% 2.69/2.86  # Backward-rewritten                   : 508
% 2.69/2.86  # Generated clauses                    : 383710
% 2.69/2.86  # ...of the previous two non-trivial   : 320793
% 2.69/2.86  # Contextual simplify-reflections      : 169
% 2.69/2.86  # Paramodulations                      : 383680
% 2.69/2.86  # Factorizations                       : 0
% 2.69/2.86  # Equation resolutions                 : 30
% 2.69/2.86  # Propositional unsat checks           : 0
% 2.69/2.86  #    Propositional check models        : 0
% 2.69/2.86  #    Propositional check unsatisfiable : 0
% 2.69/2.86  #    Propositional clauses             : 0
% 2.69/2.86  #    Propositional clauses after purity: 0
% 2.69/2.86  #    Propositional unsat core size     : 0
% 2.69/2.86  #    Propositional preprocessing time  : 0.000
% 2.69/2.86  #    Propositional encoding time       : 0.000
% 2.69/2.86  #    Propositional solver time         : 0.000
% 2.69/2.86  #    Success case prop preproc time    : 0.000
% 2.69/2.86  #    Success case prop encoding time   : 0.000
% 2.69/2.86  #    Success case prop solver time     : 0.000
% 2.69/2.86  # Current number of processed clauses  : 3076
% 2.69/2.86  #    Positive orientable unit clauses  : 614
% 2.69/2.86  #    Positive unorientable unit clauses: 12
% 2.69/2.86  #    Negative unit clauses             : 126
% 2.69/2.86  #    Non-unit-clauses                  : 2324
% 2.69/2.86  # Current number of unprocessed clauses: 276519
% 2.69/2.86  # ...number of literals in the above   : 761958
% 2.69/2.86  # Current number of archived formulas  : 0
% 2.69/2.86  # Current number of archived clauses   : 789
% 2.69/2.86  # Clause-clause subsumption calls (NU) : 1150976
% 2.69/2.86  # Rec. Clause-clause subsumption calls : 745934
% 2.69/2.86  # Non-unit clause-clause subsumptions  : 17430
% 2.69/2.86  # Unit Clause-clause subsumption calls : 30481
% 2.69/2.86  # Rewrite failures with RHS unbound    : 0
% 2.69/2.86  # BW rewrite match attempts            : 4818
% 2.69/2.86  # BW rewrite match successes           : 332
% 2.69/2.86  # Condensation attempts                : 0
% 2.69/2.86  # Condensation successes               : 0
% 2.69/2.86  # Termbank termtop insertions          : 5501314
% 2.69/2.87  
% 2.69/2.87  # -------------------------------------------------
% 2.69/2.87  # User time                : 2.418 s
% 2.69/2.87  # System time              : 0.111 s
% 2.69/2.87  # Total time               : 2.529 s
% 2.69/2.87  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------
