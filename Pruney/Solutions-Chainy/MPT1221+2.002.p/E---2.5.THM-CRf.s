%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:10:33 EST 2020

% Result     : Theorem 1.45s
% Output     : CNFRefutation 1.45s
% Verified   : 
% Statistics : Number of formulae       :  134 (52870 expanded)
%              Number of clauses        :   99 (25957 expanded)
%              Number of leaves         :   17 (13368 expanded)
%              Depth                    :   26
%              Number of atoms          :  309 (143791 expanded)
%              Number of equality atoms :   88 (54879 expanded)
%              Maximal formula depth    :   17 (   3 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(t29_tops_1,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v4_pre_topc(X2,X1)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X1),X2),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tops_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(dt_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(dt_k2_subset_1,axiom,(
    ! [X1] : m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(redefinition_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k3_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(t32_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => k7_subset_1(X1,X2,X3) = k9_subset_1(X1,X2,k3_subset_1(X1,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_subset_1)).

fof(d3_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => k2_struct_0(X1) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(d6_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v4_pre_topc(X2,X1)
          <=> v3_pre_topc(k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_pre_topc)).

fof(c_0_17,plain,(
    ! [X11,X12,X13,X14,X15,X16,X17,X18] :
      ( ( r2_hidden(X14,X11)
        | ~ r2_hidden(X14,X13)
        | X13 != k3_xboole_0(X11,X12) )
      & ( r2_hidden(X14,X12)
        | ~ r2_hidden(X14,X13)
        | X13 != k3_xboole_0(X11,X12) )
      & ( ~ r2_hidden(X15,X11)
        | ~ r2_hidden(X15,X12)
        | r2_hidden(X15,X13)
        | X13 != k3_xboole_0(X11,X12) )
      & ( ~ r2_hidden(esk2_3(X16,X17,X18),X18)
        | ~ r2_hidden(esk2_3(X16,X17,X18),X16)
        | ~ r2_hidden(esk2_3(X16,X17,X18),X17)
        | X18 = k3_xboole_0(X16,X17) )
      & ( r2_hidden(esk2_3(X16,X17,X18),X16)
        | r2_hidden(esk2_3(X16,X17,X18),X18)
        | X18 = k3_xboole_0(X16,X17) )
      & ( r2_hidden(esk2_3(X16,X17,X18),X17)
        | r2_hidden(esk2_3(X16,X17,X18),X18)
        | X18 = k3_xboole_0(X16,X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

fof(c_0_18,plain,(
    ! [X38,X39] : k1_setfam_1(k2_tarski(X38,X39)) = k3_xboole_0(X38,X39) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_19,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_20,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X4 != k3_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_21,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_22,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_23,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_24,plain,(
    ! [X40,X41] :
      ( ( ~ m1_subset_1(X40,k1_zfmisc_1(X41))
        | r1_tarski(X40,X41) )
      & ( ~ r1_tarski(X40,X41)
        | m1_subset_1(X40,k1_zfmisc_1(X41)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_25,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( v4_pre_topc(X2,X1)
            <=> v3_pre_topc(k3_subset_1(u1_struct_0(X1),X2),X1) ) ) ) ),
    inference(assume_negation,[status(cth)],[t29_tops_1])).

fof(c_0_26,plain,(
    ! [X20,X21] : k4_xboole_0(X20,X21) = k5_xboole_0(X20,k3_xboole_0(X20,X21)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_27,plain,
    ( r2_hidden(X1,X4)
    | X4 != k1_setfam_1(k2_tarski(X2,X3))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_28,plain,
    ( r2_hidden(esk1_2(X1,X2),X3)
    | r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_29,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_30,negated_conjecture,
    ( l1_pre_topc(esk3_0)
    & m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))
    & ( ~ v4_pre_topc(esk4_0,esk3_0)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(esk3_0),esk4_0),esk3_0) )
    & ( v4_pre_topc(esk4_0,esk3_0)
      | v3_pre_topc(k3_subset_1(u1_struct_0(esk3_0),esk4_0),esk3_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_25])])])).

fof(c_0_31,plain,(
    ! [X27,X28] :
      ( ~ m1_subset_1(X28,k1_zfmisc_1(X27))
      | k3_subset_1(X27,X28) = k4_xboole_0(X27,X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

cnf(c_0_32,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_33,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_34,plain,
    ( r2_hidden(X1,k1_setfam_1(k2_tarski(X2,X3)))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_27])).

cnf(c_0_35,plain,
    ( r2_hidden(esk1_2(X1,X2),X3)
    | r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_36,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_37,plain,(
    ! [X30,X31] :
      ( ~ m1_subset_1(X31,k1_zfmisc_1(X30))
      | m1_subset_1(k3_subset_1(X30,X31),k1_zfmisc_1(X30)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).

fof(c_0_38,plain,(
    ! [X29] : m1_subset_1(k2_subset_1(X29),k1_zfmisc_1(X29)) ),
    inference(variable_rename,[status(thm)],[dt_k2_subset_1])).

fof(c_0_39,plain,(
    ! [X26] : k2_subset_1(X26) = X26 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

cnf(c_0_40,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_41,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_32,c_0_21])).

fof(c_0_42,plain,(
    ! [X24,X25] : k2_tarski(X24,X25) = k2_tarski(X25,X24) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

cnf(c_0_43,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X2)
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | X3 = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_44,plain,
    ( r1_tarski(X1,k1_setfam_1(k2_tarski(X2,X3)))
    | ~ r2_hidden(esk1_2(X1,k1_setfam_1(k2_tarski(X2,X3))),X3)
    | ~ r2_hidden(esk1_2(X1,k1_setfam_1(k2_tarski(X2,X3))),X2) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(esk1_2(esk4_0,X1),u1_struct_0(esk3_0))
    | r1_tarski(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

fof(c_0_46,plain,(
    ! [X22,X23] : k4_xboole_0(X22,k4_xboole_0(X22,X23)) = k3_xboole_0(X22,X23) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_47,plain,(
    ! [X32,X33,X34] :
      ( ~ m1_subset_1(X34,k1_zfmisc_1(X32))
      | k9_subset_1(X32,X33,X34) = k3_xboole_0(X33,X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).

cnf(c_0_48,plain,
    ( m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_49,plain,
    ( m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_50,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_51,plain,
    ( k3_subset_1(X2,X1) = k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_52,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_53,plain,
    ( X3 = k1_setfam_1(k2_tarski(X1,X2))
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | r2_hidden(esk2_3(X1,X2,X3),X2) ),
    inference(rw,[status(thm)],[c_0_43,c_0_21])).

cnf(c_0_54,negated_conjecture,
    ( r1_tarski(esk4_0,k1_setfam_1(k2_tarski(X1,u1_struct_0(esk3_0))))
    | ~ r2_hidden(esk1_2(esk4_0,k1_setfam_1(k2_tarski(X1,u1_struct_0(esk3_0)))),X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_55,plain,
    ( X3 = k3_xboole_0(X1,X2)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X1)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_56,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

fof(c_0_57,plain,(
    ! [X35,X36,X37] :
      ( ~ m1_subset_1(X36,k1_zfmisc_1(X35))
      | ~ m1_subset_1(X37,k1_zfmisc_1(X35))
      | k7_subset_1(X35,X36,X37) = k9_subset_1(X35,X36,k3_subset_1(X35,X37)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t32_subset_1])])])).

cnf(c_0_58,plain,
    ( k9_subset_1(X2,X3,X1) = k3_xboole_0(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_59,plain,
    ( r2_hidden(esk1_2(k3_subset_1(X1,X2),X3),X1)
    | r1_tarski(k3_subset_1(X1,X2),X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_48])).

cnf(c_0_60,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_61,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_62,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1))) = k3_subset_1(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_63,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = X2
    | r2_hidden(esk2_3(X1,X2,X2),X2) ),
    inference(ef,[status(thm)],[c_0_53])).

cnf(c_0_64,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_65,negated_conjecture,
    ( r1_tarski(esk4_0,k1_setfam_1(k2_tarski(esk4_0,u1_struct_0(esk3_0)))) ),
    inference(spm,[status(thm)],[c_0_54,c_0_23])).

cnf(c_0_66,plain,
    ( X3 = k1_setfam_1(k2_tarski(X1,X2))
    | ~ r2_hidden(esk2_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X2)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X1) ),
    inference(rw,[status(thm)],[c_0_55,c_0_21])).

cnf(c_0_67,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))))) = k1_setfam_1(k2_tarski(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_21]),c_0_41]),c_0_41])).

cnf(c_0_68,plain,
    ( k7_subset_1(X2,X1,X3) = k9_subset_1(X2,X1,k3_subset_1(X2,X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_69,plain,
    ( k9_subset_1(X2,X3,X1) = k1_setfam_1(k2_tarski(X3,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_58,c_0_21])).

cnf(c_0_70,plain,
    ( r2_hidden(esk1_2(k3_subset_1(X1,X1),X2),X1)
    | r1_tarski(k3_subset_1(X1,X1),X2) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_71,plain,
    ( r2_hidden(X1,X2)
    | X3 != k1_setfam_1(k2_tarski(X2,X4))
    | ~ r2_hidden(X1,X3) ),
    inference(rw,[status(thm)],[c_0_61,c_0_21])).

cnf(c_0_72,plain,
    ( k5_xboole_0(X1,X1) = k3_subset_1(X1,X2)
    | r2_hidden(esk2_3(X2,X1,X1),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_73,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k1_setfam_1(k2_tarski(esk4_0,u1_struct_0(esk3_0))))) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_74,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = X2
    | ~ r2_hidden(esk2_3(X1,X2,X2),X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_63]),c_0_63])).

cnf(c_0_75,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k3_subset_1(X1,X1)))) = k1_setfam_1(k2_tarski(X1,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_62]),c_0_60])])).

cnf(c_0_76,plain,
    ( k1_setfam_1(k2_tarski(X1,k3_subset_1(X2,X3))) = k7_subset_1(X2,X1,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_48])).

cnf(c_0_77,plain,
    ( k5_xboole_0(X1,k9_subset_1(X2,X1,X3)) = k3_subset_1(X1,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_69])).

cnf(c_0_78,plain,
    ( r1_tarski(k3_subset_1(X1,X1),X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_70])).

cnf(c_0_79,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_setfam_1(k2_tarski(X2,X3))) ),
    inference(er,[status(thm)],[c_0_71])).

cnf(c_0_80,negated_conjecture,
    ( k5_xboole_0(k1_setfam_1(k2_tarski(esk4_0,u1_struct_0(esk3_0))),k1_setfam_1(k2_tarski(esk4_0,u1_struct_0(esk3_0)))) = k3_subset_1(k1_setfam_1(k2_tarski(esk4_0,u1_struct_0(esk3_0))),esk4_0)
    | r2_hidden(esk2_3(esk4_0,k1_setfam_1(k2_tarski(esk4_0,u1_struct_0(esk3_0))),k1_setfam_1(k2_tarski(esk4_0,u1_struct_0(esk3_0)))),k1_setfam_1(k2_tarski(esk4_0,u1_struct_0(esk3_0)))) ),
    inference(spm,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_81,plain,
    ( k1_setfam_1(k2_tarski(X1,X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_74,c_0_63])).

cnf(c_0_82,plain,
    ( k5_xboole_0(X1,k7_subset_1(X1,X1,X1)) = k1_setfam_1(k2_tarski(X1,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_60])])).

cnf(c_0_83,plain,
    ( k5_xboole_0(X1,k7_subset_1(X2,X1,X3)) = k3_subset_1(X1,k3_subset_1(X2,X3))
    | ~ m1_subset_1(k3_subset_1(X2,X3),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_68]),c_0_48])).

cnf(c_0_84,plain,
    ( m1_subset_1(k3_subset_1(X1,X1),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_64,c_0_78])).

cnf(c_0_85,negated_conjecture,
    ( k5_xboole_0(k1_setfam_1(k2_tarski(esk4_0,u1_struct_0(esk3_0))),k1_setfam_1(k2_tarski(esk4_0,u1_struct_0(esk3_0)))) = k3_subset_1(k1_setfam_1(k2_tarski(esk4_0,u1_struct_0(esk3_0))),esk4_0)
    | r2_hidden(esk2_3(esk4_0,k1_setfam_1(k2_tarski(esk4_0,u1_struct_0(esk3_0))),k1_setfam_1(k2_tarski(esk4_0,u1_struct_0(esk3_0)))),esk4_0) ),
    inference(spm,[status(thm)],[c_0_79,c_0_80])).

cnf(c_0_86,plain,
    ( k5_xboole_0(X1,X1) = k3_subset_1(X1,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_81]),c_0_60])])).

cnf(c_0_87,plain,
    ( k3_subset_1(X1,k3_subset_1(X1,X1)) = k1_setfam_1(k2_tarski(X1,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_84]),c_0_60])])).

cnf(c_0_88,negated_conjecture,
    ( k3_subset_1(k1_setfam_1(k2_tarski(esk4_0,u1_struct_0(esk3_0))),k1_setfam_1(k2_tarski(esk4_0,u1_struct_0(esk3_0)))) = k3_subset_1(k1_setfam_1(k2_tarski(esk4_0,u1_struct_0(esk3_0))),esk4_0)
    | r2_hidden(esk2_3(esk4_0,k1_setfam_1(k2_tarski(esk4_0,u1_struct_0(esk3_0))),k1_setfam_1(k2_tarski(esk4_0,u1_struct_0(esk3_0)))),esk4_0) ),
    inference(rw,[status(thm)],[c_0_85,c_0_86])).

cnf(c_0_89,plain,
    ( k3_subset_1(X1,k3_subset_1(X1,X1)) = X1 ),
    inference(rw,[status(thm)],[c_0_87,c_0_81])).

cnf(c_0_90,negated_conjecture,
    ( k3_subset_1(k1_setfam_1(k2_tarski(esk4_0,u1_struct_0(esk3_0))),k1_setfam_1(k2_tarski(esk4_0,u1_struct_0(esk3_0)))) = k3_subset_1(k1_setfam_1(k2_tarski(esk4_0,u1_struct_0(esk3_0))),esk4_0)
    | k1_setfam_1(k2_tarski(esk4_0,k1_setfam_1(k2_tarski(esk4_0,u1_struct_0(esk3_0))))) = k1_setfam_1(k2_tarski(esk4_0,u1_struct_0(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_74,c_0_88])).

cnf(c_0_91,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k5_xboole_0(X1,k7_subset_1(X2,X1,X3))))) = k7_subset_1(X2,X1,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_67,c_0_76])).

cnf(c_0_92,plain,
    ( k5_xboole_0(X1,k7_subset_1(X1,X1,X1)) = X1 ),
    inference(rw,[status(thm)],[c_0_82,c_0_81])).

cnf(c_0_93,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X1)
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | X3 = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_94,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k3_subset_1(X1,X2)))) = k1_setfam_1(k2_tarski(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_67,c_0_51])).

cnf(c_0_95,negated_conjecture,
    ( k3_subset_1(k1_setfam_1(k2_tarski(esk4_0,u1_struct_0(esk3_0))),k3_subset_1(k1_setfam_1(k2_tarski(esk4_0,u1_struct_0(esk3_0))),esk4_0)) = k1_setfam_1(k2_tarski(esk4_0,u1_struct_0(esk3_0)))
    | k1_setfam_1(k2_tarski(esk4_0,k1_setfam_1(k2_tarski(esk4_0,u1_struct_0(esk3_0))))) = k1_setfam_1(k2_tarski(esk4_0,u1_struct_0(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_89,c_0_90])).

cnf(c_0_96,negated_conjecture,
    ( k1_setfam_1(k2_tarski(esk4_0,k1_setfam_1(k2_tarski(esk4_0,u1_struct_0(esk3_0))))) = k1_setfam_1(k2_tarski(esk4_0,u1_struct_0(esk3_0)))
    | m1_subset_1(k3_subset_1(k1_setfam_1(k2_tarski(esk4_0,u1_struct_0(esk3_0))),esk4_0),k1_zfmisc_1(k1_setfam_1(k2_tarski(esk4_0,u1_struct_0(esk3_0))))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_90]),c_0_60])])).

cnf(c_0_97,plain,
    ( k7_subset_1(X1,X1,X1) = k3_subset_1(X1,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_92]),c_0_81]),c_0_86]),c_0_60])])).

cnf(c_0_98,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X4)
    | ~ r1_tarski(k1_setfam_1(k2_tarski(X4,X3)),X2) ),
    inference(spm,[status(thm)],[c_0_22,c_0_34])).

cnf(c_0_99,plain,
    ( X3 = k1_setfam_1(k2_tarski(X1,X2))
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | r2_hidden(esk2_3(X1,X2,X3),X1) ),
    inference(rw,[status(thm)],[c_0_93,c_0_21])).

cnf(c_0_100,negated_conjecture,
    ( k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(esk4_0,u1_struct_0(esk3_0))),k3_subset_1(k1_setfam_1(k2_tarski(esk4_0,u1_struct_0(esk3_0))),esk4_0))) = k3_subset_1(k1_setfam_1(k2_tarski(esk4_0,u1_struct_0(esk3_0))),k1_setfam_1(k2_tarski(esk4_0,u1_struct_0(esk3_0))))
    | k1_setfam_1(k2_tarski(esk4_0,k1_setfam_1(k2_tarski(esk4_0,u1_struct_0(esk3_0))))) = k1_setfam_1(k2_tarski(esk4_0,u1_struct_0(esk3_0))) ),
    inference(csr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_95]),c_0_81]),c_0_86]),c_0_96])).

cnf(c_0_101,plain,
    ( k5_xboole_0(X1,k3_subset_1(X1,X1)) = X1 ),
    inference(rw,[status(thm)],[c_0_92,c_0_97])).

cnf(c_0_102,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_tarski(k3_subset_1(X3,k3_subset_1(X3,X3)),X2) ),
    inference(spm,[status(thm)],[c_0_98,c_0_87])).

cnf(c_0_103,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = X1
    | r2_hidden(esk2_3(X1,X2,X1),X1) ),
    inference(ef,[status(thm)],[c_0_99])).

cnf(c_0_104,negated_conjecture,
    ( k1_setfam_1(k2_tarski(esk4_0,k1_setfam_1(k2_tarski(esk4_0,u1_struct_0(esk3_0))))) = k1_setfam_1(k2_tarski(esk4_0,u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_100]),c_0_101]),c_0_52]),c_0_73])])).

cnf(c_0_105,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_tarski(k1_setfam_1(k2_tarski(X3,X3)),X2) ),
    inference(spm,[status(thm)],[c_0_102,c_0_87])).

cnf(c_0_106,negated_conjecture,
    ( k1_setfam_1(k2_tarski(esk4_0,u1_struct_0(esk3_0))) = esk4_0
    | r2_hidden(esk2_3(esk4_0,k1_setfam_1(k2_tarski(esk4_0,u1_struct_0(esk3_0))),esk4_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_103,c_0_104])).

cnf(c_0_107,plain,
    ( r2_hidden(X1,X2)
    | ~ m1_subset_1(k1_setfam_1(k2_tarski(X3,X3)),k1_zfmisc_1(X2))
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_105,c_0_29])).

cnf(c_0_108,negated_conjecture,
    ( k1_setfam_1(k2_tarski(esk4_0,u1_struct_0(esk3_0))) = esk4_0
    | ~ r2_hidden(esk2_3(esk4_0,k1_setfam_1(k2_tarski(esk4_0,u1_struct_0(esk3_0))),esk4_0),k1_setfam_1(k2_tarski(esk4_0,u1_struct_0(esk3_0)))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_106]),c_0_104])]),c_0_79])).

cnf(c_0_109,plain,
    ( r2_hidden(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r2_hidden(X1,X3) ),
    inference(rw,[status(thm)],[c_0_107,c_0_81])).

cnf(c_0_110,negated_conjecture,
    ( k1_setfam_1(k2_tarski(esk4_0,u1_struct_0(esk3_0))) = esk4_0
    | ~ r2_hidden(esk2_3(esk4_0,k1_setfam_1(k2_tarski(esk4_0,u1_struct_0(esk3_0))),esk4_0),u1_struct_0(esk3_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_34]),c_0_106])).

cnf(c_0_111,negated_conjecture,
    ( r2_hidden(X1,u1_struct_0(esk3_0))
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_109,c_0_36])).

cnf(c_0_112,negated_conjecture,
    ( k1_setfam_1(k2_tarski(esk4_0,u1_struct_0(esk3_0))) = esk4_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_110,c_0_111]),c_0_106])).

fof(c_0_113,plain,(
    ! [X42] :
      ( ~ l1_struct_0(X42)
      | k2_struct_0(X42) = u1_struct_0(X42) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

fof(c_0_114,plain,(
    ! [X45] :
      ( ~ l1_pre_topc(X45)
      | l1_struct_0(X45) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_115,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1)))))) = k1_setfam_1(k2_tarski(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_67,c_0_52])).

cnf(c_0_116,negated_conjecture,
    ( k5_xboole_0(u1_struct_0(esk3_0),esk4_0) = k3_subset_1(u1_struct_0(esk3_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_112]),c_0_36])])).

fof(c_0_117,plain,(
    ! [X43,X44] :
      ( ( ~ v4_pre_topc(X44,X43)
        | v3_pre_topc(k7_subset_1(u1_struct_0(X43),k2_struct_0(X43),X44),X43)
        | ~ m1_subset_1(X44,k1_zfmisc_1(u1_struct_0(X43)))
        | ~ l1_pre_topc(X43) )
      & ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(X43),k2_struct_0(X43),X44),X43)
        | v4_pre_topc(X44,X43)
        | ~ m1_subset_1(X44,k1_zfmisc_1(u1_struct_0(X43)))
        | ~ l1_pre_topc(X43) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_pre_topc])])])])).

cnf(c_0_118,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_113])).

cnf(c_0_119,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_114])).

cnf(c_0_120,negated_conjecture,
    ( k5_xboole_0(u1_struct_0(esk3_0),k1_setfam_1(k2_tarski(u1_struct_0(esk3_0),k3_subset_1(u1_struct_0(esk3_0),esk4_0)))) = esk4_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115,c_0_112]),c_0_116])).

cnf(c_0_121,plain,
    ( v4_pre_topc(X2,X1)
    | ~ v3_pre_topc(k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_117])).

cnf(c_0_122,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_118,c_0_119])).

cnf(c_0_123,negated_conjecture,
    ( k5_xboole_0(u1_struct_0(esk3_0),k7_subset_1(u1_struct_0(esk3_0),u1_struct_0(esk3_0),esk4_0)) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120,c_0_76]),c_0_36]),c_0_60])])).

cnf(c_0_124,plain,
    ( v3_pre_topc(k7_subset_1(u1_struct_0(X2),k2_struct_0(X2),X1),X2)
    | ~ v4_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_117])).

cnf(c_0_125,plain,
    ( v4_pre_topc(X1,X2)
    | ~ v3_pre_topc(k7_subset_1(u1_struct_0(X2),u1_struct_0(X2),X1),X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(spm,[status(thm)],[c_0_121,c_0_122])).

cnf(c_0_126,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk3_0),u1_struct_0(esk3_0),esk4_0) = k3_subset_1(u1_struct_0(esk3_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_123]),c_0_52]),c_0_112]),c_0_116]),c_0_36]),c_0_60])])).

cnf(c_0_127,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_128,negated_conjecture,
    ( v4_pre_topc(esk4_0,esk3_0)
    | v3_pre_topc(k3_subset_1(u1_struct_0(esk3_0),esk4_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_129,plain,
    ( v3_pre_topc(k7_subset_1(u1_struct_0(X1),u1_struct_0(X1),X2),X1)
    | ~ v4_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_124,c_0_122])).

cnf(c_0_130,negated_conjecture,
    ( v4_pre_topc(esk4_0,esk3_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_125,c_0_126]),c_0_127]),c_0_36])]),c_0_128])).

cnf(c_0_131,negated_conjecture,
    ( ~ v4_pre_topc(esk4_0,esk3_0)
    | ~ v3_pre_topc(k3_subset_1(u1_struct_0(esk3_0),esk4_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_132,negated_conjecture,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(esk3_0),esk4_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_129,c_0_126]),c_0_127]),c_0_36])]),c_0_130])])).

cnf(c_0_133,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_131,c_0_130])]),c_0_132])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:19:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 1.45/1.68  # AutoSched0-Mode selected heuristic G_E___302_C18_F1_URBAN_RG_S04BN
% 1.45/1.68  # and selection function PSelectComplexExceptUniqMaxHorn.
% 1.45/1.68  #
% 1.45/1.68  # Preprocessing time       : 0.028 s
% 1.45/1.68  
% 1.45/1.68  # Proof found!
% 1.45/1.68  # SZS status Theorem
% 1.45/1.68  # SZS output start CNFRefutation
% 1.45/1.68  fof(d4_xboole_0, axiom, ![X1, X2, X3]:(X3=k3_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 1.45/1.68  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 1.45/1.68  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 1.45/1.68  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 1.45/1.68  fof(t29_tops_1, conjecture, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v4_pre_topc(X2,X1)<=>v3_pre_topc(k3_subset_1(u1_struct_0(X1),X2),X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_tops_1)).
% 1.45/1.68  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 1.45/1.68  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 1.45/1.68  fof(dt_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 1.45/1.68  fof(dt_k2_subset_1, axiom, ![X1]:m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 1.45/1.68  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 1.45/1.68  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 1.45/1.68  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 1.45/1.68  fof(redefinition_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k9_subset_1(X1,X2,X3)=k3_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 1.45/1.68  fof(t32_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k7_subset_1(X1,X2,X3)=k9_subset_1(X1,X2,k3_subset_1(X1,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_subset_1)).
% 1.45/1.68  fof(d3_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>k2_struct_0(X1)=u1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 1.45/1.68  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 1.45/1.68  fof(d6_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v4_pre_topc(X2,X1)<=>v3_pre_topc(k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2),X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_pre_topc)).
% 1.45/1.68  fof(c_0_17, plain, ![X11, X12, X13, X14, X15, X16, X17, X18]:((((r2_hidden(X14,X11)|~r2_hidden(X14,X13)|X13!=k3_xboole_0(X11,X12))&(r2_hidden(X14,X12)|~r2_hidden(X14,X13)|X13!=k3_xboole_0(X11,X12)))&(~r2_hidden(X15,X11)|~r2_hidden(X15,X12)|r2_hidden(X15,X13)|X13!=k3_xboole_0(X11,X12)))&((~r2_hidden(esk2_3(X16,X17,X18),X18)|(~r2_hidden(esk2_3(X16,X17,X18),X16)|~r2_hidden(esk2_3(X16,X17,X18),X17))|X18=k3_xboole_0(X16,X17))&((r2_hidden(esk2_3(X16,X17,X18),X16)|r2_hidden(esk2_3(X16,X17,X18),X18)|X18=k3_xboole_0(X16,X17))&(r2_hidden(esk2_3(X16,X17,X18),X17)|r2_hidden(esk2_3(X16,X17,X18),X18)|X18=k3_xboole_0(X16,X17))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).
% 1.45/1.68  fof(c_0_18, plain, ![X38, X39]:k1_setfam_1(k2_tarski(X38,X39))=k3_xboole_0(X38,X39), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 1.45/1.68  fof(c_0_19, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 1.45/1.68  cnf(c_0_20, plain, (r2_hidden(X1,X4)|~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X4!=k3_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 1.45/1.68  cnf(c_0_21, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 1.45/1.68  cnf(c_0_22, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 1.45/1.68  cnf(c_0_23, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 1.45/1.68  fof(c_0_24, plain, ![X40, X41]:((~m1_subset_1(X40,k1_zfmisc_1(X41))|r1_tarski(X40,X41))&(~r1_tarski(X40,X41)|m1_subset_1(X40,k1_zfmisc_1(X41)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 1.45/1.68  fof(c_0_25, negated_conjecture, ~(![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v4_pre_topc(X2,X1)<=>v3_pre_topc(k3_subset_1(u1_struct_0(X1),X2),X1))))), inference(assume_negation,[status(cth)],[t29_tops_1])).
% 1.45/1.68  fof(c_0_26, plain, ![X20, X21]:k4_xboole_0(X20,X21)=k5_xboole_0(X20,k3_xboole_0(X20,X21)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 1.45/1.68  cnf(c_0_27, plain, (r2_hidden(X1,X4)|X4!=k1_setfam_1(k2_tarski(X2,X3))|~r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_20, c_0_21])).
% 1.45/1.68  cnf(c_0_28, plain, (r2_hidden(esk1_2(X1,X2),X3)|r1_tarski(X1,X2)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 1.45/1.68  cnf(c_0_29, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 1.45/1.68  fof(c_0_30, negated_conjecture, (l1_pre_topc(esk3_0)&(m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))&((~v4_pre_topc(esk4_0,esk3_0)|~v3_pre_topc(k3_subset_1(u1_struct_0(esk3_0),esk4_0),esk3_0))&(v4_pre_topc(esk4_0,esk3_0)|v3_pre_topc(k3_subset_1(u1_struct_0(esk3_0),esk4_0),esk3_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_25])])])).
% 1.45/1.68  fof(c_0_31, plain, ![X27, X28]:(~m1_subset_1(X28,k1_zfmisc_1(X27))|k3_subset_1(X27,X28)=k4_xboole_0(X27,X28)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 1.45/1.68  cnf(c_0_32, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 1.45/1.68  cnf(c_0_33, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 1.45/1.68  cnf(c_0_34, plain, (r2_hidden(X1,k1_setfam_1(k2_tarski(X2,X3)))|~r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_27])).
% 1.45/1.68  cnf(c_0_35, plain, (r2_hidden(esk1_2(X1,X2),X3)|r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X3))), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 1.45/1.68  cnf(c_0_36, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 1.45/1.68  fof(c_0_37, plain, ![X30, X31]:(~m1_subset_1(X31,k1_zfmisc_1(X30))|m1_subset_1(k3_subset_1(X30,X31),k1_zfmisc_1(X30))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).
% 1.45/1.68  fof(c_0_38, plain, ![X29]:m1_subset_1(k2_subset_1(X29),k1_zfmisc_1(X29)), inference(variable_rename,[status(thm)],[dt_k2_subset_1])).
% 1.45/1.68  fof(c_0_39, plain, ![X26]:k2_subset_1(X26)=X26, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 1.45/1.68  cnf(c_0_40, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 1.45/1.68  cnf(c_0_41, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))), inference(rw,[status(thm)],[c_0_32, c_0_21])).
% 1.45/1.68  fof(c_0_42, plain, ![X24, X25]:k2_tarski(X24,X25)=k2_tarski(X25,X24), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 1.45/1.68  cnf(c_0_43, plain, (r2_hidden(esk2_3(X1,X2,X3),X2)|r2_hidden(esk2_3(X1,X2,X3),X3)|X3=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 1.45/1.68  cnf(c_0_44, plain, (r1_tarski(X1,k1_setfam_1(k2_tarski(X2,X3)))|~r2_hidden(esk1_2(X1,k1_setfam_1(k2_tarski(X2,X3))),X3)|~r2_hidden(esk1_2(X1,k1_setfam_1(k2_tarski(X2,X3))),X2)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 1.45/1.68  cnf(c_0_45, negated_conjecture, (r2_hidden(esk1_2(esk4_0,X1),u1_struct_0(esk3_0))|r1_tarski(esk4_0,X1)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 1.45/1.68  fof(c_0_46, plain, ![X22, X23]:k4_xboole_0(X22,k4_xboole_0(X22,X23))=k3_xboole_0(X22,X23), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 1.45/1.68  fof(c_0_47, plain, ![X32, X33, X34]:(~m1_subset_1(X34,k1_zfmisc_1(X32))|k9_subset_1(X32,X33,X34)=k3_xboole_0(X33,X34)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).
% 1.45/1.68  cnf(c_0_48, plain, (m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 1.45/1.68  cnf(c_0_49, plain, (m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 1.45/1.68  cnf(c_0_50, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_39])).
% 1.45/1.68  cnf(c_0_51, plain, (k3_subset_1(X2,X1)=k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_40, c_0_41])).
% 1.45/1.68  cnf(c_0_52, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 1.45/1.68  cnf(c_0_53, plain, (X3=k1_setfam_1(k2_tarski(X1,X2))|r2_hidden(esk2_3(X1,X2,X3),X3)|r2_hidden(esk2_3(X1,X2,X3),X2)), inference(rw,[status(thm)],[c_0_43, c_0_21])).
% 1.45/1.68  cnf(c_0_54, negated_conjecture, (r1_tarski(esk4_0,k1_setfam_1(k2_tarski(X1,u1_struct_0(esk3_0))))|~r2_hidden(esk1_2(esk4_0,k1_setfam_1(k2_tarski(X1,u1_struct_0(esk3_0)))),X1)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 1.45/1.68  cnf(c_0_55, plain, (X3=k3_xboole_0(X1,X2)|~r2_hidden(esk2_3(X1,X2,X3),X3)|~r2_hidden(esk2_3(X1,X2,X3),X1)|~r2_hidden(esk2_3(X1,X2,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 1.45/1.68  cnf(c_0_56, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 1.45/1.68  fof(c_0_57, plain, ![X35, X36, X37]:(~m1_subset_1(X36,k1_zfmisc_1(X35))|(~m1_subset_1(X37,k1_zfmisc_1(X35))|k7_subset_1(X35,X36,X37)=k9_subset_1(X35,X36,k3_subset_1(X35,X37)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t32_subset_1])])])).
% 1.45/1.68  cnf(c_0_58, plain, (k9_subset_1(X2,X3,X1)=k3_xboole_0(X3,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_47])).
% 1.45/1.68  cnf(c_0_59, plain, (r2_hidden(esk1_2(k3_subset_1(X1,X2),X3),X1)|r1_tarski(k3_subset_1(X1,X2),X3)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_35, c_0_48])).
% 1.45/1.68  cnf(c_0_60, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_49, c_0_50])).
% 1.45/1.68  cnf(c_0_61, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 1.45/1.68  cnf(c_0_62, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1)))=k3_subset_1(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 1.45/1.68  cnf(c_0_63, plain, (k1_setfam_1(k2_tarski(X1,X2))=X2|r2_hidden(esk2_3(X1,X2,X2),X2)), inference(ef,[status(thm)],[c_0_53])).
% 1.45/1.68  cnf(c_0_64, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 1.45/1.68  cnf(c_0_65, negated_conjecture, (r1_tarski(esk4_0,k1_setfam_1(k2_tarski(esk4_0,u1_struct_0(esk3_0))))), inference(spm,[status(thm)],[c_0_54, c_0_23])).
% 1.45/1.68  cnf(c_0_66, plain, (X3=k1_setfam_1(k2_tarski(X1,X2))|~r2_hidden(esk2_3(X1,X2,X3),X3)|~r2_hidden(esk2_3(X1,X2,X3),X2)|~r2_hidden(esk2_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[c_0_55, c_0_21])).
% 1.45/1.68  cnf(c_0_67, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))))))=k1_setfam_1(k2_tarski(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56, c_0_21]), c_0_41]), c_0_41])).
% 1.45/1.68  cnf(c_0_68, plain, (k7_subset_1(X2,X1,X3)=k9_subset_1(X2,X1,k3_subset_1(X2,X3))|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_57])).
% 1.45/1.68  cnf(c_0_69, plain, (k9_subset_1(X2,X3,X1)=k1_setfam_1(k2_tarski(X3,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_58, c_0_21])).
% 1.45/1.68  cnf(c_0_70, plain, (r2_hidden(esk1_2(k3_subset_1(X1,X1),X2),X1)|r1_tarski(k3_subset_1(X1,X1),X2)), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 1.45/1.68  cnf(c_0_71, plain, (r2_hidden(X1,X2)|X3!=k1_setfam_1(k2_tarski(X2,X4))|~r2_hidden(X1,X3)), inference(rw,[status(thm)],[c_0_61, c_0_21])).
% 1.45/1.68  cnf(c_0_72, plain, (k5_xboole_0(X1,X1)=k3_subset_1(X1,X2)|r2_hidden(esk2_3(X2,X1,X1),X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 1.45/1.68  cnf(c_0_73, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k1_setfam_1(k2_tarski(esk4_0,u1_struct_0(esk3_0)))))), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 1.45/1.68  cnf(c_0_74, plain, (k1_setfam_1(k2_tarski(X1,X2))=X2|~r2_hidden(esk2_3(X1,X2,X2),X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_63]), c_0_63])).
% 1.45/1.68  cnf(c_0_75, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k3_subset_1(X1,X1))))=k1_setfam_1(k2_tarski(X1,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_62]), c_0_60])])).
% 1.45/1.68  cnf(c_0_76, plain, (k1_setfam_1(k2_tarski(X1,k3_subset_1(X2,X3)))=k7_subset_1(X2,X1,X3)|~m1_subset_1(X3,k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_48])).
% 1.45/1.68  cnf(c_0_77, plain, (k5_xboole_0(X1,k9_subset_1(X2,X1,X3))=k3_subset_1(X1,X3)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_51, c_0_69])).
% 1.45/1.68  cnf(c_0_78, plain, (r1_tarski(k3_subset_1(X1,X1),X1)), inference(spm,[status(thm)],[c_0_33, c_0_70])).
% 1.45/1.68  cnf(c_0_79, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k1_setfam_1(k2_tarski(X2,X3)))), inference(er,[status(thm)],[c_0_71])).
% 1.45/1.68  cnf(c_0_80, negated_conjecture, (k5_xboole_0(k1_setfam_1(k2_tarski(esk4_0,u1_struct_0(esk3_0))),k1_setfam_1(k2_tarski(esk4_0,u1_struct_0(esk3_0))))=k3_subset_1(k1_setfam_1(k2_tarski(esk4_0,u1_struct_0(esk3_0))),esk4_0)|r2_hidden(esk2_3(esk4_0,k1_setfam_1(k2_tarski(esk4_0,u1_struct_0(esk3_0))),k1_setfam_1(k2_tarski(esk4_0,u1_struct_0(esk3_0)))),k1_setfam_1(k2_tarski(esk4_0,u1_struct_0(esk3_0))))), inference(spm,[status(thm)],[c_0_72, c_0_73])).
% 1.45/1.68  cnf(c_0_81, plain, (k1_setfam_1(k2_tarski(X1,X1))=X1), inference(spm,[status(thm)],[c_0_74, c_0_63])).
% 1.45/1.68  cnf(c_0_82, plain, (k5_xboole_0(X1,k7_subset_1(X1,X1,X1))=k1_setfam_1(k2_tarski(X1,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_76]), c_0_60])])).
% 1.45/1.68  cnf(c_0_83, plain, (k5_xboole_0(X1,k7_subset_1(X2,X1,X3))=k3_subset_1(X1,k3_subset_1(X2,X3))|~m1_subset_1(k3_subset_1(X2,X3),k1_zfmisc_1(X1))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_68]), c_0_48])).
% 1.45/1.68  cnf(c_0_84, plain, (m1_subset_1(k3_subset_1(X1,X1),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_64, c_0_78])).
% 1.45/1.68  cnf(c_0_85, negated_conjecture, (k5_xboole_0(k1_setfam_1(k2_tarski(esk4_0,u1_struct_0(esk3_0))),k1_setfam_1(k2_tarski(esk4_0,u1_struct_0(esk3_0))))=k3_subset_1(k1_setfam_1(k2_tarski(esk4_0,u1_struct_0(esk3_0))),esk4_0)|r2_hidden(esk2_3(esk4_0,k1_setfam_1(k2_tarski(esk4_0,u1_struct_0(esk3_0))),k1_setfam_1(k2_tarski(esk4_0,u1_struct_0(esk3_0)))),esk4_0)), inference(spm,[status(thm)],[c_0_79, c_0_80])).
% 1.45/1.68  cnf(c_0_86, plain, (k5_xboole_0(X1,X1)=k3_subset_1(X1,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_81]), c_0_60])])).
% 1.45/1.68  cnf(c_0_87, plain, (k3_subset_1(X1,k3_subset_1(X1,X1))=k1_setfam_1(k2_tarski(X1,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_83]), c_0_84]), c_0_60])])).
% 1.45/1.68  cnf(c_0_88, negated_conjecture, (k3_subset_1(k1_setfam_1(k2_tarski(esk4_0,u1_struct_0(esk3_0))),k1_setfam_1(k2_tarski(esk4_0,u1_struct_0(esk3_0))))=k3_subset_1(k1_setfam_1(k2_tarski(esk4_0,u1_struct_0(esk3_0))),esk4_0)|r2_hidden(esk2_3(esk4_0,k1_setfam_1(k2_tarski(esk4_0,u1_struct_0(esk3_0))),k1_setfam_1(k2_tarski(esk4_0,u1_struct_0(esk3_0)))),esk4_0)), inference(rw,[status(thm)],[c_0_85, c_0_86])).
% 1.45/1.68  cnf(c_0_89, plain, (k3_subset_1(X1,k3_subset_1(X1,X1))=X1), inference(rw,[status(thm)],[c_0_87, c_0_81])).
% 1.45/1.68  cnf(c_0_90, negated_conjecture, (k3_subset_1(k1_setfam_1(k2_tarski(esk4_0,u1_struct_0(esk3_0))),k1_setfam_1(k2_tarski(esk4_0,u1_struct_0(esk3_0))))=k3_subset_1(k1_setfam_1(k2_tarski(esk4_0,u1_struct_0(esk3_0))),esk4_0)|k1_setfam_1(k2_tarski(esk4_0,k1_setfam_1(k2_tarski(esk4_0,u1_struct_0(esk3_0)))))=k1_setfam_1(k2_tarski(esk4_0,u1_struct_0(esk3_0)))), inference(spm,[status(thm)],[c_0_74, c_0_88])).
% 1.45/1.68  cnf(c_0_91, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k5_xboole_0(X1,k7_subset_1(X2,X1,X3)))))=k7_subset_1(X2,X1,X3)|~m1_subset_1(X3,k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_67, c_0_76])).
% 1.45/1.68  cnf(c_0_92, plain, (k5_xboole_0(X1,k7_subset_1(X1,X1,X1))=X1), inference(rw,[status(thm)],[c_0_82, c_0_81])).
% 1.45/1.68  cnf(c_0_93, plain, (r2_hidden(esk2_3(X1,X2,X3),X1)|r2_hidden(esk2_3(X1,X2,X3),X3)|X3=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 1.45/1.68  cnf(c_0_94, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k3_subset_1(X1,X2))))=k1_setfam_1(k2_tarski(X1,X2))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_67, c_0_51])).
% 1.45/1.68  cnf(c_0_95, negated_conjecture, (k3_subset_1(k1_setfam_1(k2_tarski(esk4_0,u1_struct_0(esk3_0))),k3_subset_1(k1_setfam_1(k2_tarski(esk4_0,u1_struct_0(esk3_0))),esk4_0))=k1_setfam_1(k2_tarski(esk4_0,u1_struct_0(esk3_0)))|k1_setfam_1(k2_tarski(esk4_0,k1_setfam_1(k2_tarski(esk4_0,u1_struct_0(esk3_0)))))=k1_setfam_1(k2_tarski(esk4_0,u1_struct_0(esk3_0)))), inference(spm,[status(thm)],[c_0_89, c_0_90])).
% 1.45/1.68  cnf(c_0_96, negated_conjecture, (k1_setfam_1(k2_tarski(esk4_0,k1_setfam_1(k2_tarski(esk4_0,u1_struct_0(esk3_0)))))=k1_setfam_1(k2_tarski(esk4_0,u1_struct_0(esk3_0)))|m1_subset_1(k3_subset_1(k1_setfam_1(k2_tarski(esk4_0,u1_struct_0(esk3_0))),esk4_0),k1_zfmisc_1(k1_setfam_1(k2_tarski(esk4_0,u1_struct_0(esk3_0)))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_90]), c_0_60])])).
% 1.45/1.68  cnf(c_0_97, plain, (k7_subset_1(X1,X1,X1)=k3_subset_1(X1,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_92]), c_0_81]), c_0_86]), c_0_60])])).
% 1.45/1.68  cnf(c_0_98, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r2_hidden(X1,X4)|~r1_tarski(k1_setfam_1(k2_tarski(X4,X3)),X2)), inference(spm,[status(thm)],[c_0_22, c_0_34])).
% 1.45/1.68  cnf(c_0_99, plain, (X3=k1_setfam_1(k2_tarski(X1,X2))|r2_hidden(esk2_3(X1,X2,X3),X3)|r2_hidden(esk2_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[c_0_93, c_0_21])).
% 1.45/1.68  cnf(c_0_100, negated_conjecture, (k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(esk4_0,u1_struct_0(esk3_0))),k3_subset_1(k1_setfam_1(k2_tarski(esk4_0,u1_struct_0(esk3_0))),esk4_0)))=k3_subset_1(k1_setfam_1(k2_tarski(esk4_0,u1_struct_0(esk3_0))),k1_setfam_1(k2_tarski(esk4_0,u1_struct_0(esk3_0))))|k1_setfam_1(k2_tarski(esk4_0,k1_setfam_1(k2_tarski(esk4_0,u1_struct_0(esk3_0)))))=k1_setfam_1(k2_tarski(esk4_0,u1_struct_0(esk3_0)))), inference(csr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_95]), c_0_81]), c_0_86]), c_0_96])).
% 1.45/1.68  cnf(c_0_101, plain, (k5_xboole_0(X1,k3_subset_1(X1,X1))=X1), inference(rw,[status(thm)],[c_0_92, c_0_97])).
% 1.45/1.68  cnf(c_0_102, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_tarski(k3_subset_1(X3,k3_subset_1(X3,X3)),X2)), inference(spm,[status(thm)],[c_0_98, c_0_87])).
% 1.45/1.68  cnf(c_0_103, plain, (k1_setfam_1(k2_tarski(X1,X2))=X1|r2_hidden(esk2_3(X1,X2,X1),X1)), inference(ef,[status(thm)],[c_0_99])).
% 1.45/1.68  cnf(c_0_104, negated_conjecture, (k1_setfam_1(k2_tarski(esk4_0,k1_setfam_1(k2_tarski(esk4_0,u1_struct_0(esk3_0)))))=k1_setfam_1(k2_tarski(esk4_0,u1_struct_0(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_100]), c_0_101]), c_0_52]), c_0_73])])).
% 1.45/1.68  cnf(c_0_105, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_tarski(k1_setfam_1(k2_tarski(X3,X3)),X2)), inference(spm,[status(thm)],[c_0_102, c_0_87])).
% 1.45/1.68  cnf(c_0_106, negated_conjecture, (k1_setfam_1(k2_tarski(esk4_0,u1_struct_0(esk3_0)))=esk4_0|r2_hidden(esk2_3(esk4_0,k1_setfam_1(k2_tarski(esk4_0,u1_struct_0(esk3_0))),esk4_0),esk4_0)), inference(spm,[status(thm)],[c_0_103, c_0_104])).
% 1.45/1.68  cnf(c_0_107, plain, (r2_hidden(X1,X2)|~m1_subset_1(k1_setfam_1(k2_tarski(X3,X3)),k1_zfmisc_1(X2))|~r2_hidden(X1,X3)), inference(spm,[status(thm)],[c_0_105, c_0_29])).
% 1.45/1.68  cnf(c_0_108, negated_conjecture, (k1_setfam_1(k2_tarski(esk4_0,u1_struct_0(esk3_0)))=esk4_0|~r2_hidden(esk2_3(esk4_0,k1_setfam_1(k2_tarski(esk4_0,u1_struct_0(esk3_0))),esk4_0),k1_setfam_1(k2_tarski(esk4_0,u1_struct_0(esk3_0))))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_106]), c_0_104])]), c_0_79])).
% 1.45/1.68  cnf(c_0_109, plain, (r2_hidden(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r2_hidden(X1,X3)), inference(rw,[status(thm)],[c_0_107, c_0_81])).
% 1.45/1.68  cnf(c_0_110, negated_conjecture, (k1_setfam_1(k2_tarski(esk4_0,u1_struct_0(esk3_0)))=esk4_0|~r2_hidden(esk2_3(esk4_0,k1_setfam_1(k2_tarski(esk4_0,u1_struct_0(esk3_0))),esk4_0),u1_struct_0(esk3_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_108, c_0_34]), c_0_106])).
% 1.45/1.68  cnf(c_0_111, negated_conjecture, (r2_hidden(X1,u1_struct_0(esk3_0))|~r2_hidden(X1,esk4_0)), inference(spm,[status(thm)],[c_0_109, c_0_36])).
% 1.45/1.68  cnf(c_0_112, negated_conjecture, (k1_setfam_1(k2_tarski(esk4_0,u1_struct_0(esk3_0)))=esk4_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_110, c_0_111]), c_0_106])).
% 1.45/1.68  fof(c_0_113, plain, ![X42]:(~l1_struct_0(X42)|k2_struct_0(X42)=u1_struct_0(X42)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).
% 1.45/1.68  fof(c_0_114, plain, ![X45]:(~l1_pre_topc(X45)|l1_struct_0(X45)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 1.45/1.68  cnf(c_0_115, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1))))))=k1_setfam_1(k2_tarski(X2,X1))), inference(spm,[status(thm)],[c_0_67, c_0_52])).
% 1.45/1.68  cnf(c_0_116, negated_conjecture, (k5_xboole_0(u1_struct_0(esk3_0),esk4_0)=k3_subset_1(u1_struct_0(esk3_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_112]), c_0_36])])).
% 1.45/1.68  fof(c_0_117, plain, ![X43, X44]:((~v4_pre_topc(X44,X43)|v3_pre_topc(k7_subset_1(u1_struct_0(X43),k2_struct_0(X43),X44),X43)|~m1_subset_1(X44,k1_zfmisc_1(u1_struct_0(X43)))|~l1_pre_topc(X43))&(~v3_pre_topc(k7_subset_1(u1_struct_0(X43),k2_struct_0(X43),X44),X43)|v4_pre_topc(X44,X43)|~m1_subset_1(X44,k1_zfmisc_1(u1_struct_0(X43)))|~l1_pre_topc(X43))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_pre_topc])])])])).
% 1.45/1.68  cnf(c_0_118, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_113])).
% 1.45/1.68  cnf(c_0_119, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_114])).
% 1.45/1.68  cnf(c_0_120, negated_conjecture, (k5_xboole_0(u1_struct_0(esk3_0),k1_setfam_1(k2_tarski(u1_struct_0(esk3_0),k3_subset_1(u1_struct_0(esk3_0),esk4_0))))=esk4_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115, c_0_112]), c_0_116])).
% 1.45/1.68  cnf(c_0_121, plain, (v4_pre_topc(X2,X1)|~v3_pre_topc(k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2),X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_117])).
% 1.45/1.68  cnf(c_0_122, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_118, c_0_119])).
% 1.45/1.68  cnf(c_0_123, negated_conjecture, (k5_xboole_0(u1_struct_0(esk3_0),k7_subset_1(u1_struct_0(esk3_0),u1_struct_0(esk3_0),esk4_0))=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120, c_0_76]), c_0_36]), c_0_60])])).
% 1.45/1.68  cnf(c_0_124, plain, (v3_pre_topc(k7_subset_1(u1_struct_0(X2),k2_struct_0(X2),X1),X2)|~v4_pre_topc(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_117])).
% 1.45/1.68  cnf(c_0_125, plain, (v4_pre_topc(X1,X2)|~v3_pre_topc(k7_subset_1(u1_struct_0(X2),u1_struct_0(X2),X1),X2)|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))), inference(spm,[status(thm)],[c_0_121, c_0_122])).
% 1.45/1.68  cnf(c_0_126, negated_conjecture, (k7_subset_1(u1_struct_0(esk3_0),u1_struct_0(esk3_0),esk4_0)=k3_subset_1(u1_struct_0(esk3_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_123]), c_0_52]), c_0_112]), c_0_116]), c_0_36]), c_0_60])])).
% 1.45/1.68  cnf(c_0_127, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 1.45/1.68  cnf(c_0_128, negated_conjecture, (v4_pre_topc(esk4_0,esk3_0)|v3_pre_topc(k3_subset_1(u1_struct_0(esk3_0),esk4_0),esk3_0)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 1.45/1.68  cnf(c_0_129, plain, (v3_pre_topc(k7_subset_1(u1_struct_0(X1),u1_struct_0(X1),X2),X1)|~v4_pre_topc(X2,X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_124, c_0_122])).
% 1.45/1.68  cnf(c_0_130, negated_conjecture, (v4_pre_topc(esk4_0,esk3_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_125, c_0_126]), c_0_127]), c_0_36])]), c_0_128])).
% 1.45/1.68  cnf(c_0_131, negated_conjecture, (~v4_pre_topc(esk4_0,esk3_0)|~v3_pre_topc(k3_subset_1(u1_struct_0(esk3_0),esk4_0),esk3_0)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 1.45/1.68  cnf(c_0_132, negated_conjecture, (v3_pre_topc(k3_subset_1(u1_struct_0(esk3_0),esk4_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_129, c_0_126]), c_0_127]), c_0_36])]), c_0_130])])).
% 1.45/1.68  cnf(c_0_133, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_131, c_0_130])]), c_0_132])]), ['proof']).
% 1.45/1.68  # SZS output end CNFRefutation
% 1.45/1.68  # Proof object total steps             : 134
% 1.45/1.68  # Proof object clause steps            : 99
% 1.45/1.68  # Proof object formula steps           : 35
% 1.45/1.68  # Proof object conjectures             : 31
% 1.45/1.68  # Proof object clause conjectures      : 28
% 1.45/1.68  # Proof object formula conjectures     : 3
% 1.45/1.68  # Proof object initial clauses used    : 28
% 1.45/1.68  # Proof object initial formulas used   : 17
% 1.45/1.68  # Proof object generating inferences   : 55
% 1.45/1.68  # Proof object simplifying inferences  : 72
% 1.45/1.68  # Training examples: 0 positive, 0 negative
% 1.45/1.68  # Parsed axioms                        : 17
% 1.45/1.68  # Removed by relevancy pruning/SinE    : 0
% 1.45/1.68  # Initial clauses                      : 29
% 1.45/1.68  # Removed in clause preprocessing      : 3
% 1.45/1.68  # Initial clauses in saturation        : 26
% 1.45/1.68  # Processed clauses                    : 1288
% 1.45/1.68  # ...of these trivial                  : 35
% 1.45/1.68  # ...subsumed                          : 600
% 1.45/1.68  # ...remaining for further processing  : 652
% 1.45/1.68  # Other redundant clauses eliminated   : 596
% 1.45/1.68  # Clauses deleted for lack of memory   : 0
% 1.45/1.68  # Backward-subsumed                    : 28
% 1.45/1.68  # Backward-rewritten                   : 139
% 1.45/1.68  # Generated clauses                    : 63004
% 1.45/1.68  # ...of the previous two non-trivial   : 61239
% 1.45/1.68  # Contextual simplify-reflections      : 41
% 1.45/1.68  # Paramodulations                      : 61570
% 1.45/1.68  # Factorizations                       : 802
% 1.45/1.68  # Equation resolutions                 : 632
% 1.45/1.68  # Propositional unsat checks           : 0
% 1.45/1.68  #    Propositional check models        : 0
% 1.45/1.68  #    Propositional check unsatisfiable : 0
% 1.45/1.68  #    Propositional clauses             : 0
% 1.45/1.68  #    Propositional clauses after purity: 0
% 1.45/1.68  #    Propositional unsat core size     : 0
% 1.45/1.68  #    Propositional preprocessing time  : 0.000
% 1.45/1.68  #    Propositional encoding time       : 0.000
% 1.45/1.68  #    Propositional solver time         : 0.000
% 1.45/1.68  #    Success case prop preproc time    : 0.000
% 1.45/1.68  #    Success case prop encoding time   : 0.000
% 1.45/1.68  #    Success case prop solver time     : 0.000
% 1.45/1.68  # Current number of processed clauses  : 485
% 1.45/1.68  #    Positive orientable unit clauses  : 82
% 1.45/1.68  #    Positive unorientable unit clauses: 1
% 1.45/1.68  #    Negative unit clauses             : 0
% 1.45/1.68  #    Non-unit-clauses                  : 402
% 1.45/1.68  # Current number of unprocessed clauses: 59780
% 1.45/1.68  # ...number of literals in the above   : 395507
% 1.45/1.68  # Current number of archived formulas  : 0
% 1.45/1.68  # Current number of archived clauses   : 170
% 1.45/1.68  # Clause-clause subsumption calls (NU) : 44553
% 1.45/1.68  # Rec. Clause-clause subsumption calls : 16378
% 1.45/1.68  # Non-unit clause-clause subsumptions  : 663
% 1.45/1.68  # Unit Clause-clause subsumption calls : 2355
% 1.45/1.68  # Rewrite failures with RHS unbound    : 0
% 1.45/1.68  # BW rewrite match attempts            : 303
% 1.45/1.68  # BW rewrite match successes           : 37
% 1.45/1.68  # Condensation attempts                : 0
% 1.45/1.68  # Condensation successes               : 0
% 1.45/1.68  # Termbank termtop insertions          : 1643688
% 1.45/1.68  
% 1.45/1.68  # -------------------------------------------------
% 1.45/1.68  # User time                : 1.292 s
% 1.45/1.68  # System time              : 0.049 s
% 1.45/1.68  # Total time               : 1.341 s
% 1.45/1.68  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
