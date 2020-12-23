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
% DateTime   : Thu Dec  3 11:11:39 EST 2020

% Result     : Theorem 0.40s
% Output     : CNFRefutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 614 expanded)
%              Number of clauses        :   61 ( 266 expanded)
%              Number of leaves         :   19 ( 150 expanded)
%              Depth                    :   12
%              Number of atoms          :  226 (1594 expanded)
%              Number of equality atoms :   74 ( 516 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    9 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(redefinition_k7_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k7_subset_1(X1,X2,X3) = k4_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(t77_tops_1,conjecture,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v4_pre_topc(X2,X1)
          <=> k2_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),X2,k1_tops_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tops_1)).

fof(t74_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k1_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t69_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v4_pre_topc(X2,X1)
           => r1_tarski(k2_tops_1(X1,X2),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_tops_1)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t44_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => r1_tarski(k1_tops_1(X1,X2),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

fof(involutiveness_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,k3_subset_1(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

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

fof(redefinition_k4_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => k4_subset_1(X1,X2,X3) = k2_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t65_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k2_pre_topc(X1,X2) = k4_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

fof(c_0_19,plain,(
    ! [X10,X11] : k4_xboole_0(X10,X11) = k5_xboole_0(X10,k3_xboole_0(X10,X11)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_20,plain,(
    ! [X48,X49] : k1_setfam_1(k2_tarski(X48,X49)) = k3_xboole_0(X48,X49) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_21,plain,(
    ! [X44,X45,X46] :
      ( ~ m1_subset_1(X45,k1_zfmisc_1(X44))
      | k7_subset_1(X44,X45,X46) = k4_xboole_0(X45,X46) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).

cnf(c_0_22,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_23,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_24,negated_conjecture,(
    ~ ! [X1] :
        ( ( v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( v4_pre_topc(X2,X1)
            <=> k2_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),X2,k1_tops_1(X1,X2)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t77_tops_1])).

cnf(c_0_25,plain,
    ( k7_subset_1(X2,X1,X3) = k4_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_26,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_22,c_0_23])).

fof(c_0_27,negated_conjecture,
    ( v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & ( ~ v4_pre_topc(esk2_0,esk1_0)
      | k2_tops_1(esk1_0,esk2_0) != k7_subset_1(u1_struct_0(esk1_0),esk2_0,k1_tops_1(esk1_0,esk2_0)) )
    & ( v4_pre_topc(esk2_0,esk1_0)
      | k2_tops_1(esk1_0,esk2_0) = k7_subset_1(u1_struct_0(esk1_0),esk2_0,k1_tops_1(esk1_0,esk2_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_24])])])).

fof(c_0_28,plain,(
    ! [X65,X66] :
      ( ~ l1_pre_topc(X65)
      | ~ m1_subset_1(X66,k1_zfmisc_1(u1_struct_0(X65)))
      | k1_tops_1(X65,X66) = k7_subset_1(u1_struct_0(X65),X66,k2_tops_1(X65,X66)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t74_tops_1])])])).

fof(c_0_29,plain,(
    ! [X35,X36] :
      ( ~ m1_subset_1(X36,k1_zfmisc_1(X35))
      | k3_subset_1(X35,X36) = k4_xboole_0(X35,X36) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

fof(c_0_30,plain,(
    ! [X22,X23] : r1_tarski(k4_xboole_0(X22,X23),X22) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

cnf(c_0_31,plain,
    ( k7_subset_1(X2,X1,X3) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_32,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_33,plain,(
    ! [X63,X64] :
      ( ~ l1_pre_topc(X63)
      | ~ m1_subset_1(X64,k1_zfmisc_1(u1_struct_0(X63)))
      | ~ v4_pre_topc(X64,X63)
      | r1_tarski(k2_tops_1(X63,X64),X64) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t69_tops_1])])])).

fof(c_0_34,plain,(
    ! [X24,X25] : k2_xboole_0(X24,k4_xboole_0(X25,X24)) = k2_xboole_0(X24,X25) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

cnf(c_0_35,plain,
    ( k1_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_36,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_37,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_38,plain,(
    ! [X50,X51] :
      ( ( ~ m1_subset_1(X50,k1_zfmisc_1(X51))
        | r1_tarski(X50,X51) )
      & ( ~ r1_tarski(X50,X51)
        | m1_subset_1(X50,k1_zfmisc_1(X51)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_39,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_40,negated_conjecture,
    ( v4_pre_topc(esk2_0,esk1_0)
    | k2_tops_1(esk1_0,esk2_0) = k7_subset_1(u1_struct_0(esk1_0),esk2_0,k1_tops_1(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_41,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1) = k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(esk2_0,X1))) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_42,plain,
    ( r1_tarski(k2_tops_1(X1,X2),X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_43,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_44,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),esk2_0,k2_tops_1(esk1_0,esk2_0)) = k1_tops_1(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_32]),c_0_36])])).

fof(c_0_45,plain,(
    ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_46,plain,(
    ! [X57,X58] :
      ( ~ l1_pre_topc(X57)
      | ~ m1_subset_1(X58,k1_zfmisc_1(u1_struct_0(X57)))
      | r1_tarski(k1_tops_1(X57,X58),X58) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_tops_1])])])).

fof(c_0_47,plain,(
    ! [X39,X40] :
      ( ~ m1_subset_1(X40,k1_zfmisc_1(X39))
      | k3_subset_1(X39,k3_subset_1(X39,X40)) = X40 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).

cnf(c_0_48,plain,
    ( k3_subset_1(X2,X1) = k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_37,c_0_26])).

cnf(c_0_49,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_50,plain,
    ( r1_tarski(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),X1) ),
    inference(rw,[status(thm)],[c_0_39,c_0_26])).

cnf(c_0_51,negated_conjecture,
    ( k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(esk2_0,k1_tops_1(esk1_0,esk2_0)))) = k2_tops_1(esk1_0,esk2_0)
    | v4_pre_topc(esk2_0,esk1_0) ),
    inference(rw,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_52,negated_conjecture,
    ( r1_tarski(k2_tops_1(esk1_0,esk2_0),esk2_0)
    | ~ v4_pre_topc(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_32]),c_0_36])])).

fof(c_0_53,plain,(
    ! [X18,X19,X20] :
      ( ~ r1_tarski(X18,X19)
      | ~ r1_tarski(X19,X20)
      | r1_tarski(X18,X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

cnf(c_0_54,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

fof(c_0_55,plain,(
    ! [X15,X16] :
      ( ~ r1_tarski(X15,X16)
      | k2_xboole_0(X15,X16) = X16 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_56,plain,
    ( k2_xboole_0(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_43,c_0_26])).

cnf(c_0_57,negated_conjecture,
    ( k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(esk2_0,k2_tops_1(esk1_0,esk2_0)))) = k1_tops_1(esk1_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_44,c_0_41])).

cnf(c_0_58,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_59,negated_conjecture,
    ( ~ v4_pre_topc(esk2_0,esk1_0)
    | k2_tops_1(esk1_0,esk2_0) != k7_subset_1(u1_struct_0(esk1_0),esk2_0,k1_tops_1(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_60,plain,
    ( r1_tarski(k1_tops_1(X1,X2),X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_61,plain,
    ( k3_subset_1(X2,k3_subset_1(X2,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_62,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k3_subset_1(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_63,negated_conjecture,
    ( r1_tarski(k2_tops_1(esk1_0,esk2_0),esk2_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_52])).

cnf(c_0_64,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_65,negated_conjecture,
    ( r1_tarski(esk2_0,u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_32])).

fof(c_0_66,plain,(
    ! [X55,X56] :
      ( ( ~ v4_pre_topc(X56,X55)
        | k2_pre_topc(X55,X56) = X56
        | ~ m1_subset_1(X56,k1_zfmisc_1(u1_struct_0(X55)))
        | ~ l1_pre_topc(X55) )
      & ( ~ v2_pre_topc(X55)
        | k2_pre_topc(X55,X56) != X56
        | v4_pre_topc(X56,X55)
        | ~ m1_subset_1(X56,k1_zfmisc_1(u1_struct_0(X55)))
        | ~ l1_pre_topc(X55) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t52_pre_topc])])])])).

fof(c_0_67,plain,(
    ! [X41,X42,X43] :
      ( ~ m1_subset_1(X42,k1_zfmisc_1(X41))
      | ~ m1_subset_1(X43,k1_zfmisc_1(X41))
      | k4_subset_1(X41,X42,X43) = k2_xboole_0(X42,X43) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).

cnf(c_0_68,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_69,negated_conjecture,
    ( k2_xboole_0(k2_tops_1(esk1_0,esk2_0),k1_tops_1(esk1_0,esk2_0)) = k2_xboole_0(esk2_0,k2_tops_1(esk1_0,esk2_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_58])).

cnf(c_0_70,negated_conjecture,
    ( k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(esk2_0,k1_tops_1(esk1_0,esk2_0)))) != k2_tops_1(esk1_0,esk2_0)
    | ~ v4_pre_topc(esk2_0,esk1_0) ),
    inference(rw,[status(thm)],[c_0_59,c_0_41])).

cnf(c_0_71,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,esk2_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_32]),c_0_36])])).

cnf(c_0_72,plain,
    ( k3_subset_1(X1,k3_subset_1(X1,X2)) = X2
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_61,c_0_49])).

cnf(c_0_73,negated_conjecture,
    ( k3_subset_1(esk2_0,k2_tops_1(esk1_0,esk2_0)) = k1_tops_1(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_62]),c_0_63])])).

cnf(c_0_74,negated_conjecture,
    ( r1_tarski(X1,u1_struct_0(esk1_0))
    | ~ r1_tarski(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

fof(c_0_75,plain,(
    ! [X8,X9] :
      ( ( r1_tarski(X8,X9)
        | X8 != X9 )
      & ( r1_tarski(X9,X8)
        | X8 != X9 )
      & ( ~ r1_tarski(X8,X9)
        | ~ r1_tarski(X9,X8)
        | X8 = X9 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_76,plain,
    ( v4_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | k2_pre_topc(X1,X2) != X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

fof(c_0_77,plain,(
    ! [X61,X62] :
      ( ~ l1_pre_topc(X61)
      | ~ m1_subset_1(X62,k1_zfmisc_1(u1_struct_0(X61)))
      | k2_pre_topc(X61,X62) = k4_subset_1(u1_struct_0(X61),X62,k2_tops_1(X61,X62)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_tops_1])])])).

cnf(c_0_78,plain,
    ( k4_subset_1(X2,X1,X3) = k2_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_79,plain,
    ( k2_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_68,c_0_58])).

cnf(c_0_80,negated_conjecture,
    ( k2_xboole_0(esk2_0,k1_tops_1(esk1_0,esk2_0)) = k2_xboole_0(esk2_0,k2_tops_1(esk1_0,esk2_0))
    | v4_pre_topc(esk2_0,esk1_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_51]),c_0_58]),c_0_69]),c_0_58])).

cnf(c_0_81,negated_conjecture,
    ( k3_subset_1(esk2_0,k1_tops_1(esk1_0,esk2_0)) != k2_tops_1(esk1_0,esk2_0)
    | ~ v4_pre_topc(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_62]),c_0_71])])).

cnf(c_0_82,negated_conjecture,
    ( k3_subset_1(esk2_0,k1_tops_1(esk1_0,esk2_0)) = k2_tops_1(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_63])])).

cnf(c_0_83,negated_conjecture,
    ( r1_tarski(X1,u1_struct_0(esk1_0))
    | ~ r1_tarski(X2,esk2_0)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_64,c_0_74])).

cnf(c_0_84,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_85,plain,
    ( v4_pre_topc(X1,X2)
    | k2_pre_topc(X2,X1) != X1
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ r1_tarski(X1,u1_struct_0(X2)) ),
    inference(spm,[status(thm)],[c_0_76,c_0_49])).

cnf(c_0_86,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_87,plain,
    ( k2_pre_topc(X1,X2) = k4_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_77])).

cnf(c_0_88,plain,
    ( k4_subset_1(X1,X2,X3) = k2_xboole_0(X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_tarski(X3,X1) ),
    inference(spm,[status(thm)],[c_0_78,c_0_49])).

cnf(c_0_89,negated_conjecture,
    ( k2_xboole_0(esk2_0,k2_tops_1(esk1_0,esk2_0)) = esk2_0
    | v4_pre_topc(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_71])])).

cnf(c_0_90,negated_conjecture,
    ( ~ v4_pre_topc(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_81,c_0_82])])).

cnf(c_0_91,negated_conjecture,
    ( r1_tarski(X1,u1_struct_0(esk1_0))
    | ~ r1_tarski(X1,k2_tops_1(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_83,c_0_63])).

cnf(c_0_92,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_84])).

cnf(c_0_93,negated_conjecture,
    ( v4_pre_topc(X1,esk1_0)
    | k2_pre_topc(esk1_0,X1) != X1
    | ~ r1_tarski(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_86]),c_0_36])])).

cnf(c_0_94,plain,
    ( k4_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2)) = k2_pre_topc(X1,X2)
    | ~ l1_pre_topc(X1)
    | ~ r1_tarski(X2,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_87,c_0_49])).

cnf(c_0_95,negated_conjecture,
    ( k4_subset_1(u1_struct_0(esk1_0),esk2_0,X1) = k2_xboole_0(esk2_0,X1)
    | ~ r1_tarski(X1,u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_88,c_0_32])).

cnf(c_0_96,negated_conjecture,
    ( k2_xboole_0(esk2_0,k2_tops_1(esk1_0,esk2_0)) = esk2_0 ),
    inference(sr,[status(thm)],[c_0_89,c_0_90])).

cnf(c_0_97,negated_conjecture,
    ( r1_tarski(k2_tops_1(esk1_0,esk2_0),u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_91,c_0_92])).

cnf(c_0_98,negated_conjecture,
    ( k2_pre_topc(esk1_0,esk2_0) != esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_93]),c_0_65])])).

cnf(c_0_99,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_95]),c_0_96]),c_0_36]),c_0_65]),c_0_97])]),c_0_98]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n009.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 17:43:26 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.40/0.59  # AutoSched0-Mode selected heuristic G_E___107_C36_F1_PI_AE_Q4_CS_SP_PS_S0Y
% 0.40/0.59  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.40/0.59  #
% 0.40/0.59  # Preprocessing time       : 0.028 s
% 0.40/0.59  # Presaturation interreduction done
% 0.40/0.59  
% 0.40/0.59  # Proof found!
% 0.40/0.59  # SZS status Theorem
% 0.40/0.59  # SZS output start CNFRefutation
% 0.40/0.59  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.40/0.59  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.40/0.59  fof(redefinition_k7_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k7_subset_1(X1,X2,X3)=k4_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 0.40/0.59  fof(t77_tops_1, conjecture, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v4_pre_topc(X2,X1)<=>k2_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),X2,k1_tops_1(X1,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_tops_1)).
% 0.40/0.59  fof(t74_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k1_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_tops_1)).
% 0.40/0.59  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 0.40/0.59  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.40/0.59  fof(t69_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v4_pre_topc(X2,X1)=>r1_tarski(k2_tops_1(X1,X2),X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_tops_1)).
% 0.40/0.59  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 0.40/0.59  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.40/0.59  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.40/0.59  fof(t44_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>r1_tarski(k1_tops_1(X1,X2),X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_1)).
% 0.40/0.59  fof(involutiveness_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,k3_subset_1(X1,X2))=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 0.40/0.59  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 0.40/0.59  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.40/0.59  fof(t52_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>((v4_pre_topc(X2,X1)=>k2_pre_topc(X1,X2)=X2)&((v2_pre_topc(X1)&k2_pre_topc(X1,X2)=X2)=>v4_pre_topc(X2,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 0.40/0.59  fof(redefinition_k4_subset_1, axiom, ![X1, X2, X3]:((m1_subset_1(X2,k1_zfmisc_1(X1))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>k4_subset_1(X1,X2,X3)=k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 0.40/0.59  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.40/0.59  fof(t65_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k2_pre_topc(X1,X2)=k4_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tops_1)).
% 0.40/0.59  fof(c_0_19, plain, ![X10, X11]:k4_xboole_0(X10,X11)=k5_xboole_0(X10,k3_xboole_0(X10,X11)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.40/0.59  fof(c_0_20, plain, ![X48, X49]:k1_setfam_1(k2_tarski(X48,X49))=k3_xboole_0(X48,X49), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.40/0.59  fof(c_0_21, plain, ![X44, X45, X46]:(~m1_subset_1(X45,k1_zfmisc_1(X44))|k7_subset_1(X44,X45,X46)=k4_xboole_0(X45,X46)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).
% 0.40/0.59  cnf(c_0_22, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.40/0.59  cnf(c_0_23, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.40/0.59  fof(c_0_24, negated_conjecture, ~(![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v4_pre_topc(X2,X1)<=>k2_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),X2,k1_tops_1(X1,X2)))))), inference(assume_negation,[status(cth)],[t77_tops_1])).
% 0.40/0.59  cnf(c_0_25, plain, (k7_subset_1(X2,X1,X3)=k4_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.40/0.59  cnf(c_0_26, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))), inference(rw,[status(thm)],[c_0_22, c_0_23])).
% 0.40/0.59  fof(c_0_27, negated_conjecture, ((v2_pre_topc(esk1_0)&l1_pre_topc(esk1_0))&(m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&((~v4_pre_topc(esk2_0,esk1_0)|k2_tops_1(esk1_0,esk2_0)!=k7_subset_1(u1_struct_0(esk1_0),esk2_0,k1_tops_1(esk1_0,esk2_0)))&(v4_pre_topc(esk2_0,esk1_0)|k2_tops_1(esk1_0,esk2_0)=k7_subset_1(u1_struct_0(esk1_0),esk2_0,k1_tops_1(esk1_0,esk2_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_24])])])).
% 0.40/0.59  fof(c_0_28, plain, ![X65, X66]:(~l1_pre_topc(X65)|(~m1_subset_1(X66,k1_zfmisc_1(u1_struct_0(X65)))|k1_tops_1(X65,X66)=k7_subset_1(u1_struct_0(X65),X66,k2_tops_1(X65,X66)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t74_tops_1])])])).
% 0.40/0.59  fof(c_0_29, plain, ![X35, X36]:(~m1_subset_1(X36,k1_zfmisc_1(X35))|k3_subset_1(X35,X36)=k4_xboole_0(X35,X36)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 0.40/0.59  fof(c_0_30, plain, ![X22, X23]:r1_tarski(k4_xboole_0(X22,X23),X22), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.40/0.59  cnf(c_0_31, plain, (k7_subset_1(X2,X1,X3)=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X3)))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_25, c_0_26])).
% 0.40/0.59  cnf(c_0_32, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.40/0.59  fof(c_0_33, plain, ![X63, X64]:(~l1_pre_topc(X63)|(~m1_subset_1(X64,k1_zfmisc_1(u1_struct_0(X63)))|(~v4_pre_topc(X64,X63)|r1_tarski(k2_tops_1(X63,X64),X64)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t69_tops_1])])])).
% 0.40/0.59  fof(c_0_34, plain, ![X24, X25]:k2_xboole_0(X24,k4_xboole_0(X25,X24))=k2_xboole_0(X24,X25), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 0.40/0.59  cnf(c_0_35, plain, (k1_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.40/0.59  cnf(c_0_36, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.40/0.59  cnf(c_0_37, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.40/0.59  fof(c_0_38, plain, ![X50, X51]:((~m1_subset_1(X50,k1_zfmisc_1(X51))|r1_tarski(X50,X51))&(~r1_tarski(X50,X51)|m1_subset_1(X50,k1_zfmisc_1(X51)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.40/0.59  cnf(c_0_39, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.40/0.59  cnf(c_0_40, negated_conjecture, (v4_pre_topc(esk2_0,esk1_0)|k2_tops_1(esk1_0,esk2_0)=k7_subset_1(u1_struct_0(esk1_0),esk2_0,k1_tops_1(esk1_0,esk2_0))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.40/0.59  cnf(c_0_41, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1)=k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(esk2_0,X1)))), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.40/0.59  cnf(c_0_42, plain, (r1_tarski(k2_tops_1(X1,X2),X2)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v4_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.40/0.59  cnf(c_0_43, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.40/0.59  cnf(c_0_44, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),esk2_0,k2_tops_1(esk1_0,esk2_0))=k1_tops_1(esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_32]), c_0_36])])).
% 0.40/0.59  fof(c_0_45, plain, ![X4, X5]:k2_xboole_0(X4,X5)=k2_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.40/0.59  fof(c_0_46, plain, ![X57, X58]:(~l1_pre_topc(X57)|(~m1_subset_1(X58,k1_zfmisc_1(u1_struct_0(X57)))|r1_tarski(k1_tops_1(X57,X58),X58))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_tops_1])])])).
% 0.40/0.59  fof(c_0_47, plain, ![X39, X40]:(~m1_subset_1(X40,k1_zfmisc_1(X39))|k3_subset_1(X39,k3_subset_1(X39,X40))=X40), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).
% 0.40/0.59  cnf(c_0_48, plain, (k3_subset_1(X2,X1)=k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_37, c_0_26])).
% 0.40/0.59  cnf(c_0_49, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.40/0.59  cnf(c_0_50, plain, (r1_tarski(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),X1)), inference(rw,[status(thm)],[c_0_39, c_0_26])).
% 0.40/0.59  cnf(c_0_51, negated_conjecture, (k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(esk2_0,k1_tops_1(esk1_0,esk2_0))))=k2_tops_1(esk1_0,esk2_0)|v4_pre_topc(esk2_0,esk1_0)), inference(rw,[status(thm)],[c_0_40, c_0_41])).
% 0.40/0.59  cnf(c_0_52, negated_conjecture, (r1_tarski(k2_tops_1(esk1_0,esk2_0),esk2_0)|~v4_pre_topc(esk2_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_32]), c_0_36])])).
% 0.40/0.59  fof(c_0_53, plain, ![X18, X19, X20]:(~r1_tarski(X18,X19)|~r1_tarski(X19,X20)|r1_tarski(X18,X20)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 0.40/0.59  cnf(c_0_54, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.40/0.59  fof(c_0_55, plain, ![X15, X16]:(~r1_tarski(X15,X16)|k2_xboole_0(X15,X16)=X16), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.40/0.59  cnf(c_0_56, plain, (k2_xboole_0(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1))))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_43, c_0_26])).
% 0.40/0.59  cnf(c_0_57, negated_conjecture, (k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(esk2_0,k2_tops_1(esk1_0,esk2_0))))=k1_tops_1(esk1_0,esk2_0)), inference(rw,[status(thm)],[c_0_44, c_0_41])).
% 0.40/0.59  cnf(c_0_58, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.40/0.59  cnf(c_0_59, negated_conjecture, (~v4_pre_topc(esk2_0,esk1_0)|k2_tops_1(esk1_0,esk2_0)!=k7_subset_1(u1_struct_0(esk1_0),esk2_0,k1_tops_1(esk1_0,esk2_0))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.40/0.59  cnf(c_0_60, plain, (r1_tarski(k1_tops_1(X1,X2),X2)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.40/0.59  cnf(c_0_61, plain, (k3_subset_1(X2,k3_subset_1(X2,X1))=X1|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.40/0.59  cnf(c_0_62, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))=k3_subset_1(X1,X2)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.40/0.59  cnf(c_0_63, negated_conjecture, (r1_tarski(k2_tops_1(esk1_0,esk2_0),esk2_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_52])).
% 0.40/0.59  cnf(c_0_64, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.40/0.59  cnf(c_0_65, negated_conjecture, (r1_tarski(esk2_0,u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_54, c_0_32])).
% 0.40/0.59  fof(c_0_66, plain, ![X55, X56]:((~v4_pre_topc(X56,X55)|k2_pre_topc(X55,X56)=X56|~m1_subset_1(X56,k1_zfmisc_1(u1_struct_0(X55)))|~l1_pre_topc(X55))&(~v2_pre_topc(X55)|k2_pre_topc(X55,X56)!=X56|v4_pre_topc(X56,X55)|~m1_subset_1(X56,k1_zfmisc_1(u1_struct_0(X55)))|~l1_pre_topc(X55))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t52_pre_topc])])])])).
% 0.40/0.59  fof(c_0_67, plain, ![X41, X42, X43]:(~m1_subset_1(X42,k1_zfmisc_1(X41))|~m1_subset_1(X43,k1_zfmisc_1(X41))|k4_subset_1(X41,X42,X43)=k2_xboole_0(X42,X43)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).
% 0.40/0.59  cnf(c_0_68, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.40/0.59  cnf(c_0_69, negated_conjecture, (k2_xboole_0(k2_tops_1(esk1_0,esk2_0),k1_tops_1(esk1_0,esk2_0))=k2_xboole_0(esk2_0,k2_tops_1(esk1_0,esk2_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_58])).
% 0.40/0.59  cnf(c_0_70, negated_conjecture, (k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(esk2_0,k1_tops_1(esk1_0,esk2_0))))!=k2_tops_1(esk1_0,esk2_0)|~v4_pre_topc(esk2_0,esk1_0)), inference(rw,[status(thm)],[c_0_59, c_0_41])).
% 0.40/0.59  cnf(c_0_71, negated_conjecture, (r1_tarski(k1_tops_1(esk1_0,esk2_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_32]), c_0_36])])).
% 0.40/0.59  cnf(c_0_72, plain, (k3_subset_1(X1,k3_subset_1(X1,X2))=X2|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_61, c_0_49])).
% 0.40/0.59  cnf(c_0_73, negated_conjecture, (k3_subset_1(esk2_0,k2_tops_1(esk1_0,esk2_0))=k1_tops_1(esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_62]), c_0_63])])).
% 0.40/0.59  cnf(c_0_74, negated_conjecture, (r1_tarski(X1,u1_struct_0(esk1_0))|~r1_tarski(X1,esk2_0)), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 0.40/0.59  fof(c_0_75, plain, ![X8, X9]:(((r1_tarski(X8,X9)|X8!=X9)&(r1_tarski(X9,X8)|X8!=X9))&(~r1_tarski(X8,X9)|~r1_tarski(X9,X8)|X8=X9)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.40/0.59  cnf(c_0_76, plain, (v4_pre_topc(X2,X1)|~v2_pre_topc(X1)|k2_pre_topc(X1,X2)!=X2|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_66])).
% 0.40/0.59  fof(c_0_77, plain, ![X61, X62]:(~l1_pre_topc(X61)|(~m1_subset_1(X62,k1_zfmisc_1(u1_struct_0(X61)))|k2_pre_topc(X61,X62)=k4_subset_1(u1_struct_0(X61),X62,k2_tops_1(X61,X62)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_tops_1])])])).
% 0.40/0.59  cnf(c_0_78, plain, (k4_subset_1(X2,X1,X3)=k2_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.40/0.59  cnf(c_0_79, plain, (k2_xboole_0(X1,X2)=X1|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_68, c_0_58])).
% 0.40/0.59  cnf(c_0_80, negated_conjecture, (k2_xboole_0(esk2_0,k1_tops_1(esk1_0,esk2_0))=k2_xboole_0(esk2_0,k2_tops_1(esk1_0,esk2_0))|v4_pre_topc(esk2_0,esk1_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_51]), c_0_58]), c_0_69]), c_0_58])).
% 0.40/0.59  cnf(c_0_81, negated_conjecture, (k3_subset_1(esk2_0,k1_tops_1(esk1_0,esk2_0))!=k2_tops_1(esk1_0,esk2_0)|~v4_pre_topc(esk2_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_62]), c_0_71])])).
% 0.40/0.59  cnf(c_0_82, negated_conjecture, (k3_subset_1(esk2_0,k1_tops_1(esk1_0,esk2_0))=k2_tops_1(esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_73]), c_0_63])])).
% 0.40/0.59  cnf(c_0_83, negated_conjecture, (r1_tarski(X1,u1_struct_0(esk1_0))|~r1_tarski(X2,esk2_0)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_64, c_0_74])).
% 0.40/0.59  cnf(c_0_84, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_75])).
% 0.40/0.59  cnf(c_0_85, plain, (v4_pre_topc(X1,X2)|k2_pre_topc(X2,X1)!=X1|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~r1_tarski(X1,u1_struct_0(X2))), inference(spm,[status(thm)],[c_0_76, c_0_49])).
% 0.40/0.59  cnf(c_0_86, negated_conjecture, (v2_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.40/0.59  cnf(c_0_87, plain, (k2_pre_topc(X1,X2)=k4_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_77])).
% 0.40/0.59  cnf(c_0_88, plain, (k4_subset_1(X1,X2,X3)=k2_xboole_0(X2,X3)|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_tarski(X3,X1)), inference(spm,[status(thm)],[c_0_78, c_0_49])).
% 0.40/0.59  cnf(c_0_89, negated_conjecture, (k2_xboole_0(esk2_0,k2_tops_1(esk1_0,esk2_0))=esk2_0|v4_pre_topc(esk2_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_80]), c_0_71])])).
% 0.40/0.59  cnf(c_0_90, negated_conjecture, (~v4_pre_topc(esk2_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_81, c_0_82])])).
% 0.40/0.59  cnf(c_0_91, negated_conjecture, (r1_tarski(X1,u1_struct_0(esk1_0))|~r1_tarski(X1,k2_tops_1(esk1_0,esk2_0))), inference(spm,[status(thm)],[c_0_83, c_0_63])).
% 0.40/0.59  cnf(c_0_92, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_84])).
% 0.40/0.59  cnf(c_0_93, negated_conjecture, (v4_pre_topc(X1,esk1_0)|k2_pre_topc(esk1_0,X1)!=X1|~r1_tarski(X1,u1_struct_0(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_86]), c_0_36])])).
% 0.40/0.59  cnf(c_0_94, plain, (k4_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2))=k2_pre_topc(X1,X2)|~l1_pre_topc(X1)|~r1_tarski(X2,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_87, c_0_49])).
% 0.40/0.59  cnf(c_0_95, negated_conjecture, (k4_subset_1(u1_struct_0(esk1_0),esk2_0,X1)=k2_xboole_0(esk2_0,X1)|~r1_tarski(X1,u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_88, c_0_32])).
% 0.40/0.59  cnf(c_0_96, negated_conjecture, (k2_xboole_0(esk2_0,k2_tops_1(esk1_0,esk2_0))=esk2_0), inference(sr,[status(thm)],[c_0_89, c_0_90])).
% 0.40/0.59  cnf(c_0_97, negated_conjecture, (r1_tarski(k2_tops_1(esk1_0,esk2_0),u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_91, c_0_92])).
% 0.40/0.59  cnf(c_0_98, negated_conjecture, (k2_pre_topc(esk1_0,esk2_0)!=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_93]), c_0_65])])).
% 0.40/0.59  cnf(c_0_99, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_95]), c_0_96]), c_0_36]), c_0_65]), c_0_97])]), c_0_98]), ['proof']).
% 0.40/0.59  # SZS output end CNFRefutation
% 0.40/0.59  # Proof object total steps             : 100
% 0.40/0.59  # Proof object clause steps            : 61
% 0.40/0.59  # Proof object formula steps           : 39
% 0.40/0.59  # Proof object conjectures             : 33
% 0.40/0.59  # Proof object clause conjectures      : 30
% 0.40/0.59  # Proof object formula conjectures     : 3
% 0.40/0.59  # Proof object initial clauses used    : 24
% 0.40/0.59  # Proof object initial formulas used   : 19
% 0.40/0.59  # Proof object generating inferences   : 26
% 0.40/0.59  # Proof object simplifying inferences  : 41
% 0.40/0.59  # Training examples: 0 positive, 0 negative
% 0.40/0.59  # Parsed axioms                        : 31
% 0.40/0.59  # Removed by relevancy pruning/SinE    : 0
% 0.40/0.59  # Initial clauses                      : 39
% 0.40/0.59  # Removed in clause preprocessing      : 2
% 0.40/0.59  # Initial clauses in saturation        : 37
% 0.40/0.59  # Processed clauses                    : 2961
% 0.40/0.59  # ...of these trivial                  : 129
% 0.40/0.59  # ...subsumed                          : 1981
% 0.40/0.59  # ...remaining for further processing  : 851
% 0.40/0.59  # Other redundant clauses eliminated   : 2
% 0.40/0.59  # Clauses deleted for lack of memory   : 0
% 0.40/0.59  # Backward-subsumed                    : 27
% 0.40/0.59  # Backward-rewritten                   : 54
% 0.40/0.59  # Generated clauses                    : 19651
% 0.40/0.59  # ...of the previous two non-trivial   : 14893
% 0.40/0.59  # Contextual simplify-reflections      : 9
% 0.40/0.59  # Paramodulations                      : 19643
% 0.40/0.59  # Factorizations                       : 0
% 0.40/0.59  # Equation resolutions                 : 2
% 0.40/0.59  # Propositional unsat checks           : 0
% 0.40/0.59  #    Propositional check models        : 0
% 0.40/0.59  #    Propositional check unsatisfiable : 0
% 0.40/0.59  #    Propositional clauses             : 0
% 0.40/0.59  #    Propositional clauses after purity: 0
% 0.40/0.59  #    Propositional unsat core size     : 0
% 0.40/0.59  #    Propositional preprocessing time  : 0.000
% 0.40/0.59  #    Propositional encoding time       : 0.000
% 0.40/0.59  #    Propositional solver time         : 0.000
% 0.40/0.59  #    Success case prop preproc time    : 0.000
% 0.40/0.59  #    Success case prop encoding time   : 0.000
% 0.40/0.59  #    Success case prop solver time     : 0.000
% 0.40/0.59  # Current number of processed clauses  : 726
% 0.40/0.59  #    Positive orientable unit clauses  : 179
% 0.40/0.59  #    Positive unorientable unit clauses: 2
% 0.40/0.59  #    Negative unit clauses             : 5
% 0.40/0.59  #    Non-unit-clauses                  : 540
% 0.40/0.59  # Current number of unprocessed clauses: 11789
% 0.40/0.59  # ...number of literals in the above   : 31681
% 0.40/0.59  # Current number of archived formulas  : 0
% 0.40/0.59  # Current number of archived clauses   : 125
% 0.40/0.59  # Clause-clause subsumption calls (NU) : 54990
% 0.40/0.59  # Rec. Clause-clause subsumption calls : 51961
% 0.40/0.59  # Non-unit clause-clause subsumptions  : 1682
% 0.40/0.59  # Unit Clause-clause subsumption calls : 921
% 0.40/0.59  # Rewrite failures with RHS unbound    : 0
% 0.40/0.59  # BW rewrite match attempts            : 534
% 0.40/0.59  # BW rewrite match successes           : 48
% 0.40/0.59  # Condensation attempts                : 0
% 0.40/0.59  # Condensation successes               : 0
% 0.40/0.59  # Termbank termtop insertions          : 263431
% 0.40/0.59  
% 0.40/0.59  # -------------------------------------------------
% 0.40/0.59  # User time                : 0.243 s
% 0.40/0.59  # System time              : 0.011 s
% 0.40/0.59  # Total time               : 0.254 s
% 0.40/0.59  # Maximum resident set size: 1600 pages
%------------------------------------------------------------------------------
