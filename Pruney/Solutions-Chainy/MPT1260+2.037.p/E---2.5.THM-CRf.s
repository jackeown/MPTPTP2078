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
% DateTime   : Thu Dec  3 11:11:19 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 480 expanded)
%              Number of clauses        :   57 ( 210 expanded)
%              Number of leaves         :   18 ( 124 expanded)
%              Depth                    :   15
%              Number of atoms          :  193 ( 966 expanded)
%              Number of equality atoms :   80 ( 456 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    7 (   2 average)

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

fof(t76_tops_1,conjecture,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_pre_topc(X2,X1)
          <=> k2_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_tops_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(t55_tops_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( l1_pre_topc(X2)
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ! [X4] :
                  ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
                 => ( ( v3_pre_topc(X4,X2)
                     => k1_tops_1(X2,X4) = X4 )
                    & ( k1_tops_1(X1,X3) = X3
                     => v3_pre_topc(X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_tops_1)).

fof(dt_k2_pre_topc,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(l78_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k2_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k1_tops_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

fof(t47_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(t49_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(t112_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2)) = k3_xboole_0(k5_xboole_0(X1,X3),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_xboole_1)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(t74_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k1_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).

fof(c_0_18,plain,(
    ! [X6,X7] : k4_xboole_0(X6,X7) = k5_xboole_0(X6,k3_xboole_0(X6,X7)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_19,plain,(
    ! [X30,X31] : k1_setfam_1(k2_tarski(X30,X31)) = k3_xboole_0(X30,X31) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_20,plain,(
    ! [X27,X28,X29] :
      ( ~ m1_subset_1(X28,k1_zfmisc_1(X27))
      | k7_subset_1(X27,X28,X29) = k4_xboole_0(X28,X29) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).

cnf(c_0_21,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_22,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_23,negated_conjecture,(
    ~ ! [X1] :
        ( ( v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( v3_pre_topc(X2,X1)
            <=> k2_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t76_tops_1])).

cnf(c_0_24,plain,
    ( k7_subset_1(X2,X1,X3) = k4_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_25,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_21,c_0_22])).

fof(c_0_26,plain,(
    ! [X12,X13] : r1_tarski(k4_xboole_0(X12,X13),X12) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

fof(c_0_27,plain,(
    ! [X14] : k4_xboole_0(X14,k1_xboole_0) = X14 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

fof(c_0_28,plain,(
    ! [X11] : k3_xboole_0(X11,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

fof(c_0_29,negated_conjecture,
    ( v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & ( ~ v3_pre_topc(esk2_0,esk1_0)
      | k2_tops_1(esk1_0,esk2_0) != k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),esk2_0) )
    & ( v3_pre_topc(esk2_0,esk1_0)
      | k2_tops_1(esk1_0,esk2_0) = k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),esk2_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_23])])])).

cnf(c_0_30,plain,
    ( k7_subset_1(X2,X1,X3) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_24,c_0_25])).

fof(c_0_31,plain,(
    ! [X32,X33] :
      ( ( ~ m1_subset_1(X32,k1_zfmisc_1(X33))
        | r1_tarski(X32,X33) )
      & ( ~ r1_tarski(X32,X33)
        | m1_subset_1(X32,k1_zfmisc_1(X33)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_32,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_33,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_34,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_35,plain,(
    ! [X38,X39,X40,X41] :
      ( ( ~ v3_pre_topc(X41,X39)
        | k1_tops_1(X39,X41) = X41
        | ~ m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(X39)))
        | ~ m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X38)))
        | ~ l1_pre_topc(X39)
        | ~ v2_pre_topc(X38)
        | ~ l1_pre_topc(X38) )
      & ( k1_tops_1(X38,X40) != X40
        | v3_pre_topc(X40,X38)
        | ~ m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(X39)))
        | ~ m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X38)))
        | ~ l1_pre_topc(X39)
        | ~ v2_pre_topc(X38)
        | ~ l1_pre_topc(X38) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_tops_1])])])])).

cnf(c_0_36,negated_conjecture,
    ( v3_pre_topc(esk2_0,esk1_0)
    | k2_tops_1(esk1_0,esk2_0) = k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_37,plain,
    ( k7_subset_1(X1,X2,X3) = k7_subset_1(X4,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X4)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_30])).

fof(c_0_38,plain,(
    ! [X34,X35] :
      ( ~ l1_pre_topc(X34)
      | ~ m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X34)))
      | m1_subset_1(k2_pre_topc(X34,X35),k1_zfmisc_1(u1_struct_0(X34))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).

cnf(c_0_39,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_40,plain,
    ( r1_tarski(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),X1) ),
    inference(rw,[status(thm)],[c_0_32,c_0_25])).

cnf(c_0_41,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k1_xboole_0))) = X1 ),
    inference(rw,[status(thm)],[c_0_33,c_0_25])).

cnf(c_0_42,plain,
    ( k1_setfam_1(k2_tarski(X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_34,c_0_22])).

fof(c_0_43,plain,(
    ! [X36,X37] :
      ( ~ l1_pre_topc(X36)
      | ~ m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X36)))
      | k2_tops_1(X36,X37) = k7_subset_1(u1_struct_0(X36),k2_pre_topc(X36,X37),k1_tops_1(X36,X37)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l78_tops_1])])])).

cnf(c_0_44,plain,
    ( k1_tops_1(X2,X1) = X1
    | ~ v3_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X4)
    | ~ l1_pre_topc(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_45,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_46,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_47,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_48,negated_conjecture,
    ( k7_subset_1(X1,k2_pre_topc(esk1_0,esk2_0),esk2_0) = k2_tops_1(esk1_0,esk2_0)
    | v3_pre_topc(esk2_0,esk1_0)
    | ~ m1_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_49,plain,
    ( m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_50,plain,
    ( m1_subset_1(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_51,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_52,plain,
    ( k2_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k1_tops_1(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_53,negated_conjecture,
    ( k1_tops_1(X1,X2) = X2
    | ~ v3_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_46]),c_0_47])])).

cnf(c_0_54,negated_conjecture,
    ( k7_subset_1(X1,k2_pre_topc(esk1_0,esk2_0),esk2_0) = k2_tops_1(esk1_0,esk2_0)
    | v3_pre_topc(esk2_0,esk1_0)
    | ~ m1_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_47]),c_0_45])])).

cnf(c_0_55,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_42]),c_0_51])).

cnf(c_0_56,negated_conjecture,
    ( ~ v3_pre_topc(esk2_0,esk1_0)
    | k2_tops_1(esk1_0,esk2_0) != k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_57,negated_conjecture,
    ( k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),X2) = k2_tops_1(X1,X2)
    | ~ v3_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

fof(c_0_58,plain,(
    ! [X15,X16] : k4_xboole_0(X15,k3_xboole_0(X15,X16)) = k4_xboole_0(X15,X16) ),
    inference(variable_rename,[status(thm)],[t47_xboole_1])).

fof(c_0_59,plain,(
    ! [X17,X18] : k4_xboole_0(X17,k4_xboole_0(X17,X18)) = k3_xboole_0(X17,X18) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_60,plain,(
    ! [X5] : k3_xboole_0(X5,X5) = X5 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

cnf(c_0_61,negated_conjecture,
    ( k7_subset_1(k2_pre_topc(esk1_0,esk2_0),k2_pre_topc(esk1_0,esk2_0),esk2_0) = k2_tops_1(esk1_0,esk2_0)
    | v3_pre_topc(esk2_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_62,negated_conjecture,
    ( ~ v3_pre_topc(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_47]),c_0_45])])).

fof(c_0_63,plain,(
    ! [X19,X20,X21] : k3_xboole_0(X19,k4_xboole_0(X20,X21)) = k4_xboole_0(k3_xboole_0(X19,X20),X21) ),
    inference(variable_rename,[status(thm)],[t49_xboole_1])).

fof(c_0_64,plain,(
    ! [X8,X9,X10] : k5_xboole_0(k3_xboole_0(X8,X9),k3_xboole_0(X10,X9)) = k3_xboole_0(k5_xboole_0(X8,X10),X9) ),
    inference(variable_rename,[status(thm)],[t112_xboole_1])).

cnf(c_0_65,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

fof(c_0_66,plain,(
    ! [X22,X23] : k2_tarski(X22,X23) = k2_tarski(X23,X22) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

cnf(c_0_67,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_68,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_69,negated_conjecture,
    ( k7_subset_1(k2_pre_topc(esk1_0,esk2_0),k2_pre_topc(esk1_0,esk2_0),esk2_0) = k2_tops_1(esk1_0,esk2_0) ),
    inference(sr,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_70,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_71,plain,
    ( k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2)) = k3_xboole_0(k5_xboole_0(X1,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_72,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k1_setfam_1(k2_tarski(X1,X2))))) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_65,c_0_22]),c_0_25]),c_0_25])).

cnf(c_0_73,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_74,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))))) = k1_setfam_1(k2_tarski(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_67,c_0_22]),c_0_25]),c_0_25])).

cnf(c_0_75,plain,
    ( k1_setfam_1(k2_tarski(X1,X1)) = X1 ),
    inference(rw,[status(thm)],[c_0_68,c_0_22])).

cnf(c_0_76,negated_conjecture,
    ( k7_subset_1(X1,k2_pre_topc(esk1_0,esk2_0),esk2_0) = k2_tops_1(esk1_0,esk2_0)
    | ~ m1_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_69]),c_0_55])])).

fof(c_0_77,plain,(
    ! [X42,X43] :
      ( ~ l1_pre_topc(X42)
      | ~ m1_subset_1(X43,k1_zfmisc_1(u1_struct_0(X42)))
      | k1_tops_1(X42,X43) = k7_subset_1(u1_struct_0(X42),X43,k2_tops_1(X42,X43)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t74_tops_1])])])).

cnf(c_0_78,plain,
    ( k1_setfam_1(k2_tarski(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X3))))) = k5_xboole_0(k1_setfam_1(k2_tarski(X1,X2)),k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(X1,X2)),X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_70,c_0_22]),c_0_22]),c_0_25]),c_0_25])).

cnf(c_0_79,plain,
    ( k5_xboole_0(k1_setfam_1(k2_tarski(X1,X2)),k1_setfam_1(k2_tarski(X3,X2))) = k1_setfam_1(k2_tarski(k5_xboole_0(X1,X3),X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_71,c_0_22]),c_0_22]),c_0_22])).

cnf(c_0_80,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k1_setfam_1(k2_tarski(X2,X1))))) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1))) ),
    inference(spm,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_81,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_42]),c_0_51]),c_0_75])).

cnf(c_0_82,plain,
    ( k1_setfam_1(k2_tarski(k1_xboole_0,X1)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_42,c_0_73])).

cnf(c_0_83,negated_conjecture,
    ( k5_xboole_0(k2_pre_topc(esk1_0,esk2_0),k1_setfam_1(k2_tarski(esk2_0,k2_pre_topc(esk1_0,esk2_0)))) = k2_tops_1(esk1_0,esk2_0)
    | ~ m1_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_76]),c_0_73])).

cnf(c_0_84,plain,
    ( v3_pre_topc(X2,X1)
    | k1_tops_1(X1,X2) != X2
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X4)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_85,plain,
    ( k1_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_77])).

cnf(c_0_86,plain,
    ( k1_setfam_1(k2_tarski(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X1,X2))))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_75]),c_0_79]),c_0_80]),c_0_81]),c_0_82])).

cnf(c_0_87,negated_conjecture,
    ( k5_xboole_0(k2_pre_topc(esk1_0,esk2_0),k1_setfam_1(k2_tarski(esk2_0,k2_pre_topc(esk1_0,esk2_0)))) = k2_tops_1(esk1_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_83,c_0_55])).

cnf(c_0_88,negated_conjecture,
    ( v3_pre_topc(X1,X2)
    | k1_tops_1(X2,X1) != X1
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_45]),c_0_47])])).

cnf(c_0_89,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k2_tops_1(X2,X1)))) = k1_tops_1(X2,X1)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(spm,[status(thm)],[c_0_30,c_0_85])).

cnf(c_0_90,negated_conjecture,
    ( k1_setfam_1(k2_tarski(esk2_0,k2_tops_1(esk1_0,esk2_0))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_86,c_0_87])).

cnf(c_0_91,negated_conjecture,
    ( v3_pre_topc(esk2_0,esk1_0)
    | k1_tops_1(esk1_0,esk2_0) != esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_45]),c_0_46]),c_0_47])])).

cnf(c_0_92,negated_conjecture,
    ( k1_tops_1(esk1_0,esk2_0) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_90]),c_0_51]),c_0_47]),c_0_45])])).

cnf(c_0_93,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_91,c_0_92])]),c_0_62]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 13:41:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.40  # AutoSched0-Mode selected heuristic G_E___302_C18_F1_URBAN_RG_S04BN
% 0.19/0.40  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.19/0.40  #
% 0.19/0.40  # Preprocessing time       : 0.028 s
% 0.19/0.40  
% 0.19/0.40  # Proof found!
% 0.19/0.40  # SZS status Theorem
% 0.19/0.40  # SZS output start CNFRefutation
% 0.19/0.40  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.19/0.40  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.19/0.40  fof(redefinition_k7_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k7_subset_1(X1,X2,X3)=k4_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 0.19/0.40  fof(t76_tops_1, conjecture, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>k2_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_tops_1)).
% 0.19/0.40  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.19/0.40  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 0.19/0.40  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 0.19/0.40  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.19/0.40  fof(t55_tops_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(l1_pre_topc(X2)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))=>((v3_pre_topc(X4,X2)=>k1_tops_1(X2,X4)=X4)&(k1_tops_1(X1,X3)=X3=>v3_pre_topc(X3,X1))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_tops_1)).
% 0.19/0.40  fof(dt_k2_pre_topc, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 0.19/0.40  fof(l78_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k2_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k1_tops_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l78_tops_1)).
% 0.19/0.40  fof(t47_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 0.19/0.40  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.19/0.40  fof(idempotence_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 0.19/0.40  fof(t49_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 0.19/0.40  fof(t112_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2))=k3_xboole_0(k5_xboole_0(X1,X3),X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t112_xboole_1)).
% 0.19/0.40  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 0.19/0.40  fof(t74_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k1_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_tops_1)).
% 0.19/0.40  fof(c_0_18, plain, ![X6, X7]:k4_xboole_0(X6,X7)=k5_xboole_0(X6,k3_xboole_0(X6,X7)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.19/0.40  fof(c_0_19, plain, ![X30, X31]:k1_setfam_1(k2_tarski(X30,X31))=k3_xboole_0(X30,X31), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.19/0.40  fof(c_0_20, plain, ![X27, X28, X29]:(~m1_subset_1(X28,k1_zfmisc_1(X27))|k7_subset_1(X27,X28,X29)=k4_xboole_0(X28,X29)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).
% 0.19/0.40  cnf(c_0_21, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.40  cnf(c_0_22, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.40  fof(c_0_23, negated_conjecture, ~(![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>k2_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),X2))))), inference(assume_negation,[status(cth)],[t76_tops_1])).
% 0.19/0.40  cnf(c_0_24, plain, (k7_subset_1(X2,X1,X3)=k4_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.40  cnf(c_0_25, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))), inference(rw,[status(thm)],[c_0_21, c_0_22])).
% 0.19/0.40  fof(c_0_26, plain, ![X12, X13]:r1_tarski(k4_xboole_0(X12,X13),X12), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.19/0.40  fof(c_0_27, plain, ![X14]:k4_xboole_0(X14,k1_xboole_0)=X14, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.19/0.40  fof(c_0_28, plain, ![X11]:k3_xboole_0(X11,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 0.19/0.40  fof(c_0_29, negated_conjecture, ((v2_pre_topc(esk1_0)&l1_pre_topc(esk1_0))&(m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&((~v3_pre_topc(esk2_0,esk1_0)|k2_tops_1(esk1_0,esk2_0)!=k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),esk2_0))&(v3_pre_topc(esk2_0,esk1_0)|k2_tops_1(esk1_0,esk2_0)=k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),esk2_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_23])])])).
% 0.19/0.40  cnf(c_0_30, plain, (k7_subset_1(X2,X1,X3)=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X3)))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_24, c_0_25])).
% 0.19/0.40  fof(c_0_31, plain, ![X32, X33]:((~m1_subset_1(X32,k1_zfmisc_1(X33))|r1_tarski(X32,X33))&(~r1_tarski(X32,X33)|m1_subset_1(X32,k1_zfmisc_1(X33)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.19/0.40  cnf(c_0_32, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.40  cnf(c_0_33, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.40  cnf(c_0_34, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.40  fof(c_0_35, plain, ![X38, X39, X40, X41]:((~v3_pre_topc(X41,X39)|k1_tops_1(X39,X41)=X41|~m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(X39)))|~m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X38)))|~l1_pre_topc(X39)|(~v2_pre_topc(X38)|~l1_pre_topc(X38)))&(k1_tops_1(X38,X40)!=X40|v3_pre_topc(X40,X38)|~m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(X39)))|~m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X38)))|~l1_pre_topc(X39)|(~v2_pre_topc(X38)|~l1_pre_topc(X38)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_tops_1])])])])).
% 0.19/0.40  cnf(c_0_36, negated_conjecture, (v3_pre_topc(esk2_0,esk1_0)|k2_tops_1(esk1_0,esk2_0)=k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),esk2_0)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.40  cnf(c_0_37, plain, (k7_subset_1(X1,X2,X3)=k7_subset_1(X4,X2,X3)|~m1_subset_1(X2,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X4))), inference(spm,[status(thm)],[c_0_30, c_0_30])).
% 0.19/0.40  fof(c_0_38, plain, ![X34, X35]:(~l1_pre_topc(X34)|~m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X34)))|m1_subset_1(k2_pre_topc(X34,X35),k1_zfmisc_1(u1_struct_0(X34)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).
% 0.19/0.40  cnf(c_0_39, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.40  cnf(c_0_40, plain, (r1_tarski(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),X1)), inference(rw,[status(thm)],[c_0_32, c_0_25])).
% 0.19/0.40  cnf(c_0_41, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k1_xboole_0)))=X1), inference(rw,[status(thm)],[c_0_33, c_0_25])).
% 0.19/0.40  cnf(c_0_42, plain, (k1_setfam_1(k2_tarski(X1,k1_xboole_0))=k1_xboole_0), inference(rw,[status(thm)],[c_0_34, c_0_22])).
% 0.19/0.40  fof(c_0_43, plain, ![X36, X37]:(~l1_pre_topc(X36)|(~m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X36)))|k2_tops_1(X36,X37)=k7_subset_1(u1_struct_0(X36),k2_pre_topc(X36,X37),k1_tops_1(X36,X37)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l78_tops_1])])])).
% 0.19/0.40  cnf(c_0_44, plain, (k1_tops_1(X2,X1)=X1|~v3_pre_topc(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))|~l1_pre_topc(X2)|~v2_pre_topc(X4)|~l1_pre_topc(X4)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.19/0.40  cnf(c_0_45, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.40  cnf(c_0_46, negated_conjecture, (v2_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.40  cnf(c_0_47, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.40  cnf(c_0_48, negated_conjecture, (k7_subset_1(X1,k2_pre_topc(esk1_0,esk2_0),esk2_0)=k2_tops_1(esk1_0,esk2_0)|v3_pre_topc(esk2_0,esk1_0)|~m1_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.19/0.40  cnf(c_0_49, plain, (m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.19/0.40  cnf(c_0_50, plain, (m1_subset_1(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.19/0.40  cnf(c_0_51, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[c_0_41, c_0_42])).
% 0.19/0.40  cnf(c_0_52, plain, (k2_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k1_tops_1(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.19/0.40  cnf(c_0_53, negated_conjecture, (k1_tops_1(X1,X2)=X2|~v3_pre_topc(X2,X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_46]), c_0_47])])).
% 0.19/0.40  cnf(c_0_54, negated_conjecture, (k7_subset_1(X1,k2_pre_topc(esk1_0,esk2_0),esk2_0)=k2_tops_1(esk1_0,esk2_0)|v3_pre_topc(esk2_0,esk1_0)|~m1_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_zfmisc_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_47]), c_0_45])])).
% 0.19/0.40  cnf(c_0_55, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_42]), c_0_51])).
% 0.19/0.40  cnf(c_0_56, negated_conjecture, (~v3_pre_topc(esk2_0,esk1_0)|k2_tops_1(esk1_0,esk2_0)!=k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),esk2_0)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.40  cnf(c_0_57, negated_conjecture, (k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),X2)=k2_tops_1(X1,X2)|~v3_pre_topc(X2,X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.19/0.40  fof(c_0_58, plain, ![X15, X16]:k4_xboole_0(X15,k3_xboole_0(X15,X16))=k4_xboole_0(X15,X16), inference(variable_rename,[status(thm)],[t47_xboole_1])).
% 0.19/0.40  fof(c_0_59, plain, ![X17, X18]:k4_xboole_0(X17,k4_xboole_0(X17,X18))=k3_xboole_0(X17,X18), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.19/0.40  fof(c_0_60, plain, ![X5]:k3_xboole_0(X5,X5)=X5, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).
% 0.19/0.40  cnf(c_0_61, negated_conjecture, (k7_subset_1(k2_pre_topc(esk1_0,esk2_0),k2_pre_topc(esk1_0,esk2_0),esk2_0)=k2_tops_1(esk1_0,esk2_0)|v3_pre_topc(esk2_0,esk1_0)), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.19/0.40  cnf(c_0_62, negated_conjecture, (~v3_pre_topc(esk2_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_47]), c_0_45])])).
% 0.19/0.40  fof(c_0_63, plain, ![X19, X20, X21]:k3_xboole_0(X19,k4_xboole_0(X20,X21))=k4_xboole_0(k3_xboole_0(X19,X20),X21), inference(variable_rename,[status(thm)],[t49_xboole_1])).
% 0.19/0.40  fof(c_0_64, plain, ![X8, X9, X10]:k5_xboole_0(k3_xboole_0(X8,X9),k3_xboole_0(X10,X9))=k3_xboole_0(k5_xboole_0(X8,X10),X9), inference(variable_rename,[status(thm)],[t112_xboole_1])).
% 0.19/0.40  cnf(c_0_65, plain, (k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.19/0.40  fof(c_0_66, plain, ![X22, X23]:k2_tarski(X22,X23)=k2_tarski(X23,X22), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 0.19/0.40  cnf(c_0_67, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.19/0.40  cnf(c_0_68, plain, (k3_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.19/0.40  cnf(c_0_69, negated_conjecture, (k7_subset_1(k2_pre_topc(esk1_0,esk2_0),k2_pre_topc(esk1_0,esk2_0),esk2_0)=k2_tops_1(esk1_0,esk2_0)), inference(sr,[status(thm)],[c_0_61, c_0_62])).
% 0.19/0.40  cnf(c_0_70, plain, (k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.19/0.40  cnf(c_0_71, plain, (k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2))=k3_xboole_0(k5_xboole_0(X1,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.19/0.40  cnf(c_0_72, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k1_setfam_1(k2_tarski(X1,X2)))))=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_65, c_0_22]), c_0_25]), c_0_25])).
% 0.19/0.40  cnf(c_0_73, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_66])).
% 0.19/0.40  cnf(c_0_74, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))))))=k1_setfam_1(k2_tarski(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_67, c_0_22]), c_0_25]), c_0_25])).
% 0.19/0.40  cnf(c_0_75, plain, (k1_setfam_1(k2_tarski(X1,X1))=X1), inference(rw,[status(thm)],[c_0_68, c_0_22])).
% 0.19/0.40  cnf(c_0_76, negated_conjecture, (k7_subset_1(X1,k2_pre_topc(esk1_0,esk2_0),esk2_0)=k2_tops_1(esk1_0,esk2_0)|~m1_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_zfmisc_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_69]), c_0_55])])).
% 0.19/0.40  fof(c_0_77, plain, ![X42, X43]:(~l1_pre_topc(X42)|(~m1_subset_1(X43,k1_zfmisc_1(u1_struct_0(X42)))|k1_tops_1(X42,X43)=k7_subset_1(u1_struct_0(X42),X43,k2_tops_1(X42,X43)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t74_tops_1])])])).
% 0.19/0.40  cnf(c_0_78, plain, (k1_setfam_1(k2_tarski(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X3)))))=k5_xboole_0(k1_setfam_1(k2_tarski(X1,X2)),k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(X1,X2)),X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_70, c_0_22]), c_0_22]), c_0_25]), c_0_25])).
% 0.19/0.40  cnf(c_0_79, plain, (k5_xboole_0(k1_setfam_1(k2_tarski(X1,X2)),k1_setfam_1(k2_tarski(X3,X2)))=k1_setfam_1(k2_tarski(k5_xboole_0(X1,X3),X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_71, c_0_22]), c_0_22]), c_0_22])).
% 0.19/0.40  cnf(c_0_80, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k1_setfam_1(k2_tarski(X2,X1)))))=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1)))), inference(spm,[status(thm)],[c_0_72, c_0_73])).
% 0.19/0.40  cnf(c_0_81, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_42]), c_0_51]), c_0_75])).
% 0.19/0.40  cnf(c_0_82, plain, (k1_setfam_1(k2_tarski(k1_xboole_0,X1))=k1_xboole_0), inference(spm,[status(thm)],[c_0_42, c_0_73])).
% 0.19/0.40  cnf(c_0_83, negated_conjecture, (k5_xboole_0(k2_pre_topc(esk1_0,esk2_0),k1_setfam_1(k2_tarski(esk2_0,k2_pre_topc(esk1_0,esk2_0))))=k2_tops_1(esk1_0,esk2_0)|~m1_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_zfmisc_1(X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_76]), c_0_73])).
% 0.19/0.40  cnf(c_0_84, plain, (v3_pre_topc(X2,X1)|k1_tops_1(X1,X2)!=X2|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X4)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.19/0.40  cnf(c_0_85, plain, (k1_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_77])).
% 0.19/0.40  cnf(c_0_86, plain, (k1_setfam_1(k2_tarski(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X1,X2)))))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_75]), c_0_79]), c_0_80]), c_0_81]), c_0_82])).
% 0.19/0.40  cnf(c_0_87, negated_conjecture, (k5_xboole_0(k2_pre_topc(esk1_0,esk2_0),k1_setfam_1(k2_tarski(esk2_0,k2_pre_topc(esk1_0,esk2_0))))=k2_tops_1(esk1_0,esk2_0)), inference(spm,[status(thm)],[c_0_83, c_0_55])).
% 0.19/0.40  cnf(c_0_88, negated_conjecture, (v3_pre_topc(X1,X2)|k1_tops_1(X2,X1)!=X1|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_45]), c_0_47])])).
% 0.19/0.40  cnf(c_0_89, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k2_tops_1(X2,X1))))=k1_tops_1(X2,X1)|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))), inference(spm,[status(thm)],[c_0_30, c_0_85])).
% 0.19/0.40  cnf(c_0_90, negated_conjecture, (k1_setfam_1(k2_tarski(esk2_0,k2_tops_1(esk1_0,esk2_0)))=k1_xboole_0), inference(spm,[status(thm)],[c_0_86, c_0_87])).
% 0.19/0.40  cnf(c_0_91, negated_conjecture, (v3_pre_topc(esk2_0,esk1_0)|k1_tops_1(esk1_0,esk2_0)!=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_45]), c_0_46]), c_0_47])])).
% 0.19/0.40  cnf(c_0_92, negated_conjecture, (k1_tops_1(esk1_0,esk2_0)=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_90]), c_0_51]), c_0_47]), c_0_45])])).
% 0.19/0.40  cnf(c_0_93, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_91, c_0_92])]), c_0_62]), ['proof']).
% 0.19/0.40  # SZS output end CNFRefutation
% 0.19/0.40  # Proof object total steps             : 94
% 0.19/0.40  # Proof object clause steps            : 57
% 0.19/0.40  # Proof object formula steps           : 37
% 0.19/0.40  # Proof object conjectures             : 23
% 0.19/0.40  # Proof object clause conjectures      : 20
% 0.19/0.40  # Proof object formula conjectures     : 3
% 0.19/0.40  # Proof object initial clauses used    : 23
% 0.19/0.40  # Proof object initial formulas used   : 18
% 0.19/0.40  # Proof object generating inferences   : 21
% 0.19/0.40  # Proof object simplifying inferences  : 52
% 0.19/0.40  # Training examples: 0 positive, 0 negative
% 0.19/0.40  # Parsed axioms                        : 19
% 0.19/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.40  # Initial clauses                      : 25
% 0.19/0.40  # Removed in clause preprocessing      : 2
% 0.19/0.40  # Initial clauses in saturation        : 23
% 0.19/0.40  # Processed clauses                    : 210
% 0.19/0.40  # ...of these trivial                  : 24
% 0.19/0.40  # ...subsumed                          : 50
% 0.19/0.40  # ...remaining for further processing  : 136
% 0.19/0.40  # Other redundant clauses eliminated   : 0
% 0.19/0.40  # Clauses deleted for lack of memory   : 0
% 0.19/0.40  # Backward-subsumed                    : 13
% 0.19/0.40  # Backward-rewritten                   : 19
% 0.19/0.40  # Generated clauses                    : 1463
% 0.19/0.40  # ...of the previous two non-trivial   : 1106
% 0.19/0.40  # Contextual simplify-reflections      : 1
% 0.19/0.40  # Paramodulations                      : 1458
% 0.19/0.40  # Factorizations                       : 0
% 0.19/0.40  # Equation resolutions                 : 0
% 0.19/0.40  # Propositional unsat checks           : 0
% 0.19/0.40  #    Propositional check models        : 0
% 0.19/0.40  #    Propositional check unsatisfiable : 0
% 0.19/0.40  #    Propositional clauses             : 0
% 0.19/0.40  #    Propositional clauses after purity: 0
% 0.19/0.40  #    Propositional unsat core size     : 0
% 0.19/0.40  #    Propositional preprocessing time  : 0.000
% 0.19/0.40  #    Propositional encoding time       : 0.000
% 0.19/0.40  #    Propositional solver time         : 0.000
% 0.19/0.40  #    Success case prop preproc time    : 0.000
% 0.19/0.40  #    Success case prop encoding time   : 0.000
% 0.19/0.40  #    Success case prop solver time     : 0.000
% 0.19/0.40  # Current number of processed clauses  : 99
% 0.19/0.40  #    Positive orientable unit clauses  : 55
% 0.19/0.40  #    Positive unorientable unit clauses: 2
% 0.19/0.40  #    Negative unit clauses             : 1
% 0.19/0.40  #    Non-unit-clauses                  : 41
% 0.19/0.40  # Current number of unprocessed clauses: 895
% 0.19/0.40  # ...number of literals in the above   : 1527
% 0.19/0.40  # Current number of archived formulas  : 0
% 0.19/0.40  # Current number of archived clauses   : 39
% 0.19/0.40  # Clause-clause subsumption calls (NU) : 492
% 0.19/0.40  # Rec. Clause-clause subsumption calls : 369
% 0.19/0.40  # Non-unit clause-clause subsumptions  : 56
% 0.19/0.40  # Unit Clause-clause subsumption calls : 40
% 0.19/0.40  # Rewrite failures with RHS unbound    : 0
% 0.19/0.40  # BW rewrite match attempts            : 121
% 0.19/0.40  # BW rewrite match successes           : 20
% 0.19/0.40  # Condensation attempts                : 0
% 0.19/0.40  # Condensation successes               : 0
% 0.19/0.40  # Termbank termtop insertions          : 27129
% 0.19/0.40  
% 0.19/0.40  # -------------------------------------------------
% 0.19/0.40  # User time                : 0.052 s
% 0.19/0.40  # System time              : 0.011 s
% 0.19/0.40  # Total time               : 0.063 s
% 0.19/0.40  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
