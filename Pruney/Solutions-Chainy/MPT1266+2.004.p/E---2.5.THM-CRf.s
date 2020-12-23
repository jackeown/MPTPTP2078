%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:11:59 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 617 expanded)
%              Number of clauses        :   73 ( 256 expanded)
%              Number of leaves         :   26 ( 161 expanded)
%              Depth                    :   14
%              Number of atoms          :  261 (1504 expanded)
%              Number of equality atoms :   76 ( 446 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t84_tops_1,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v2_tops_1(X2,X1)
          <=> k1_tops_1(X1,X2) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(dt_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(dt_k2_pre_topc,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(d1_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k1_tops_1(X1,X2) = k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_1)).

fof(t22_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = k3_subset_1(X1,k1_subset_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(d3_subset_1,axiom,(
    ! [X1] : k1_subset_1(X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

fof(cc2_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v1_xboole_0(X2)
           => v2_tops_1(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tops_1)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(involutiveness_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,k3_subset_1(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(d4_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v2_tops_1(X2,X1)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(X1),X2),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_1)).

fof(l13_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(fc8_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => v1_xboole_0(k1_tops_1(X1,k1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_tops_1)).

fof(dt_k2_subset_1,axiom,(
    ! [X1] : m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(d3_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v1_tops_1(X2,X1)
          <=> k2_pre_topc(X1,X2) = k2_struct_0(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tops_1)).

fof(projectivity_k1_tops_1,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => k1_tops_1(X1,k1_tops_1(X1,X2)) = k1_tops_1(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',projectivity_k1_tops_1)).

fof(t47_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => k1_tops_1(X1,k1_struct_0(X1)) = k1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_tops_1)).

fof(dt_k1_tops_1,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tops_1)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(t64_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => ( k3_subset_1(X1,X2) = k3_subset_1(X1,X3)
           => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_subset_1)).

fof(c_0_26,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( v2_tops_1(X2,X1)
            <=> k1_tops_1(X1,X2) = k1_xboole_0 ) ) ) ),
    inference(assume_negation,[status(cth)],[t84_tops_1])).

fof(c_0_27,plain,(
    ! [X27,X28] :
      ( ( ~ m1_subset_1(X27,k1_zfmisc_1(X28))
        | r1_tarski(X27,X28) )
      & ( ~ r1_tarski(X27,X28)
        | m1_subset_1(X27,k1_zfmisc_1(X28)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_28,negated_conjecture,
    ( l1_pre_topc(esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & ( ~ v2_tops_1(esk2_0,esk1_0)
      | k1_tops_1(esk1_0,esk2_0) != k1_xboole_0 )
    & ( v2_tops_1(esk2_0,esk1_0)
      | k1_tops_1(esk1_0,esk2_0) = k1_xboole_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_26])])])).

fof(c_0_29,plain,(
    ! [X11,X12] : r1_tarski(k4_xboole_0(X11,X12),X11) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

fof(c_0_30,plain,(
    ! [X5,X6] : k4_xboole_0(X5,X6) = k5_xboole_0(X5,k3_xboole_0(X5,X6)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_31,plain,(
    ! [X13,X14] : k4_xboole_0(X13,k4_xboole_0(X13,X14)) = k3_xboole_0(X13,X14) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_32,plain,(
    ! [X18,X19] :
      ( ~ m1_subset_1(X19,k1_zfmisc_1(X18))
      | m1_subset_1(k3_subset_1(X18,X19),k1_zfmisc_1(X18)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).

fof(c_0_33,plain,(
    ! [X7,X8,X9] :
      ( ~ r1_tarski(X7,X8)
      | ~ r1_tarski(X8,X9)
      | r1_tarski(X7,X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

cnf(c_0_34,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_35,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_36,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_37,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_38,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_39,plain,(
    ! [X32,X33] :
      ( ~ l1_pre_topc(X32)
      | ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))
      | m1_subset_1(k2_pre_topc(X32,X33),k1_zfmisc_1(u1_struct_0(X32))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).

cnf(c_0_40,plain,
    ( m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_41,plain,(
    ! [X36,X37] :
      ( ~ l1_pre_topc(X36)
      | ~ m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X36)))
      | k1_tops_1(X36,X37) = k3_subset_1(u1_struct_0(X36),k2_pre_topc(X36,k3_subset_1(u1_struct_0(X36),X37))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tops_1])])])).

cnf(c_0_42,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_43,negated_conjecture,
    ( r1_tarski(esk2_0,u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_44,plain,
    ( r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X1) ),
    inference(rw,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_45,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_37]),c_0_37])).

fof(c_0_46,plain,(
    ! [X22] : k2_subset_1(X22) = k3_subset_1(X22,k1_subset_1(X22)) ),
    inference(variable_rename,[status(thm)],[t22_subset_1])).

fof(c_0_47,plain,(
    ! [X16] : k2_subset_1(X16) = X16 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

fof(c_0_48,plain,(
    ! [X15] : k1_subset_1(X15) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[d3_subset_1])).

fof(c_0_49,plain,(
    ! [X34,X35] :
      ( ~ l1_pre_topc(X34)
      | ~ m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X34)))
      | ~ v1_xboole_0(X35)
      | v2_tops_1(X35,X34) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_tops_1])])])).

fof(c_0_50,plain,(
    ! [X23] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X23)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

fof(c_0_51,plain,(
    ! [X20,X21] :
      ( ~ m1_subset_1(X21,k1_zfmisc_1(X20))
      | k3_subset_1(X20,k3_subset_1(X20,X21)) = X21 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).

cnf(c_0_52,plain,
    ( m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_53,negated_conjecture,
    ( m1_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_40,c_0_35])).

cnf(c_0_54,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_55,plain,
    ( k1_tops_1(X1,X2) = k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

fof(c_0_56,plain,(
    ! [X40,X41] :
      ( ( ~ v2_tops_1(X41,X40)
        | v1_tops_1(k3_subset_1(u1_struct_0(X40),X41),X40)
        | ~ m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(X40)))
        | ~ l1_pre_topc(X40) )
      & ( ~ v1_tops_1(k3_subset_1(u1_struct_0(X40),X41),X40)
        | v2_tops_1(X41,X40)
        | ~ m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(X40)))
        | ~ l1_pre_topc(X40) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tops_1])])])])).

cnf(c_0_57,negated_conjecture,
    ( r1_tarski(X1,u1_struct_0(esk1_0))
    | ~ r1_tarski(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_58,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

fof(c_0_59,plain,(
    ! [X4] :
      ( ~ v1_xboole_0(X4)
      | X4 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).

fof(c_0_60,plain,(
    ! [X44] :
      ( ~ l1_pre_topc(X44)
      | v1_xboole_0(k1_tops_1(X44,k1_struct_0(X44))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc8_tops_1])])).

fof(c_0_61,plain,(
    ! [X17] : m1_subset_1(k2_subset_1(X17),k1_zfmisc_1(X17)) ),
    inference(variable_rename,[status(thm)],[dt_k2_subset_1])).

cnf(c_0_62,plain,
    ( k2_subset_1(X1) = k3_subset_1(X1,k1_subset_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_63,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_64,plain,
    ( k1_subset_1(X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_65,plain,
    ( v2_tops_1(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_66,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_67,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

fof(c_0_68,plain,(
    ! [X38,X39] :
      ( ( ~ v1_tops_1(X39,X38)
        | k2_pre_topc(X38,X39) = k2_struct_0(X38)
        | ~ m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(X38)))
        | ~ l1_pre_topc(X38) )
      & ( k2_pre_topc(X38,X39) != k2_struct_0(X38)
        | v1_tops_1(X39,X38)
        | ~ m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(X38)))
        | ~ l1_pre_topc(X38) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tops_1])])])])).

cnf(c_0_69,plain,
    ( k3_subset_1(X2,k3_subset_1(X2,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_70,negated_conjecture,
    ( m1_subset_1(k2_pre_topc(esk1_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0)),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_54])])).

cnf(c_0_71,negated_conjecture,
    ( k3_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0))) = k1_tops_1(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_35]),c_0_54])])).

cnf(c_0_72,plain,
    ( v1_tops_1(k3_subset_1(u1_struct_0(X2),X1),X2)
    | ~ v2_tops_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

fof(c_0_73,plain,(
    ! [X45,X46] :
      ( ~ l1_pre_topc(X45)
      | ~ m1_subset_1(X46,k1_zfmisc_1(u1_struct_0(X45)))
      | k1_tops_1(X45,k1_tops_1(X45,X46)) = k1_tops_1(X45,X46) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[projectivity_k1_tops_1])])).

cnf(c_0_74,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_75,negated_conjecture,
    ( r1_tarski(k3_xboole_0(esk2_0,X1),u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

fof(c_0_76,plain,(
    ! [X47] :
      ( ~ l1_pre_topc(X47)
      | k1_tops_1(X47,k1_struct_0(X47)) = k1_struct_0(X47) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t47_tops_1])])).

cnf(c_0_77,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_78,plain,
    ( v1_xboole_0(k1_tops_1(X1,k1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_79,plain,
    ( m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_80,plain,
    ( X1 = k3_subset_1(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_62,c_0_63]),c_0_64])).

cnf(c_0_81,plain,
    ( v2_tops_1(k1_xboole_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_67])])).

cnf(c_0_82,plain,
    ( k2_pre_topc(X2,X1) = k2_struct_0(X2)
    | ~ v1_tops_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_83,negated_conjecture,
    ( k2_pre_topc(esk1_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0)) = k3_subset_1(u1_struct_0(esk1_0),k1_tops_1(esk1_0,esk2_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_71])).

cnf(c_0_84,negated_conjecture,
    ( v1_tops_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),esk1_0)
    | ~ v2_tops_1(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_35]),c_0_54])])).

cnf(c_0_85,negated_conjecture,
    ( v2_tops_1(esk2_0,esk1_0)
    | k1_tops_1(esk1_0,esk2_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_86,plain,(
    ! [X42,X43] :
      ( ~ l1_pre_topc(X42)
      | ~ m1_subset_1(X43,k1_zfmisc_1(u1_struct_0(X42)))
      | m1_subset_1(k1_tops_1(X42,X43),k1_zfmisc_1(u1_struct_0(X42))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_tops_1])])).

cnf(c_0_87,plain,
    ( k1_tops_1(X1,k1_tops_1(X1,X2)) = k1_tops_1(X1,X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_88,negated_conjecture,
    ( m1_subset_1(k3_xboole_0(esk2_0,X1),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_74,c_0_75])).

fof(c_0_89,plain,(
    ! [X10] : k3_xboole_0(X10,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

cnf(c_0_90,plain,
    ( k1_tops_1(X1,k1_struct_0(X1)) = k1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_76])).

cnf(c_0_91,plain,
    ( k1_tops_1(X1,k1_struct_0(X1)) = k1_xboole_0
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_77,c_0_78])).

cnf(c_0_92,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_79,c_0_63])).

cnf(c_0_93,plain,
    ( v1_tops_1(u1_struct_0(X1),X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_66]),c_0_80]),c_0_81])).

cnf(c_0_94,negated_conjecture,
    ( k2_struct_0(esk1_0) = k3_subset_1(u1_struct_0(esk1_0),k1_tops_1(esk1_0,esk2_0))
    | ~ v1_tops_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),esk1_0) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_53]),c_0_54])]),c_0_83])).

cnf(c_0_95,negated_conjecture,
    ( k1_tops_1(esk1_0,esk2_0) = k1_xboole_0
    | v1_tops_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),esk1_0) ),
    inference(spm,[status(thm)],[c_0_84,c_0_85])).

cnf(c_0_96,plain,
    ( m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_86])).

cnf(c_0_97,negated_conjecture,
    ( k1_tops_1(esk1_0,k1_tops_1(esk1_0,k3_xboole_0(esk2_0,X1))) = k1_tops_1(esk1_0,k3_xboole_0(esk2_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_88]),c_0_54])])).

cnf(c_0_98,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_89])).

cnf(c_0_99,plain,
    ( k1_struct_0(X1) = k1_xboole_0
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_90,c_0_91])).

cnf(c_0_100,plain,
    ( k2_struct_0(X1) = k2_pre_topc(X1,u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_92]),c_0_93])).

cnf(c_0_101,negated_conjecture,
    ( k2_struct_0(esk1_0) = k3_subset_1(u1_struct_0(esk1_0),k1_tops_1(esk1_0,esk2_0))
    | k1_tops_1(esk1_0,esk2_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_94,c_0_95])).

cnf(c_0_102,negated_conjecture,
    ( m1_subset_1(k1_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_35]),c_0_54])])).

cnf(c_0_103,negated_conjecture,
    ( k1_tops_1(esk1_0,k1_tops_1(esk1_0,k1_xboole_0)) = k1_tops_1(esk1_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_97,c_0_98])).

cnf(c_0_104,plain,
    ( k1_tops_1(X1,k1_xboole_0) = k1_xboole_0
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_90,c_0_99])).

fof(c_0_105,plain,(
    ! [X24,X25,X26] :
      ( ~ m1_subset_1(X25,k1_zfmisc_1(X24))
      | ~ m1_subset_1(X26,k1_zfmisc_1(X24))
      | k3_subset_1(X24,X25) != k3_subset_1(X24,X26)
      | X25 = X26 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_subset_1])])])).

cnf(c_0_106,plain,
    ( v1_tops_1(X2,X1)
    | k2_pre_topc(X1,X2) != k2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_107,plain,
    ( k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,u1_struct_0(X1))) = k1_tops_1(X1,k1_xboole_0)
    | ~ l1_pre_topc(X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_66]),c_0_80])).

cnf(c_0_108,negated_conjecture,
    ( k2_pre_topc(esk1_0,u1_struct_0(esk1_0)) = k3_subset_1(u1_struct_0(esk1_0),k1_tops_1(esk1_0,esk2_0))
    | k1_tops_1(esk1_0,esk2_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_101]),c_0_54])])).

cnf(c_0_109,negated_conjecture,
    ( k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),k1_tops_1(esk1_0,esk2_0))) = k1_tops_1(esk1_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_69,c_0_102])).

cnf(c_0_110,negated_conjecture,
    ( k1_tops_1(esk1_0,k1_xboole_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_104]),c_0_54])])).

cnf(c_0_111,plain,
    ( X1 = X3
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | k3_subset_1(X2,X1) != k3_subset_1(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_105])).

cnf(c_0_112,plain,
    ( k3_subset_1(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_66]),c_0_80])).

cnf(c_0_113,plain,
    ( v1_tops_1(X1,X2)
    | k2_pre_topc(X2,X1) != k2_pre_topc(X2,u1_struct_0(X2))
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(spm,[status(thm)],[c_0_106,c_0_100])).

cnf(c_0_114,negated_conjecture,
    ( k1_tops_1(esk1_0,esk2_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_108]),c_0_109]),c_0_110]),c_0_54])])).

cnf(c_0_115,plain,
    ( X1 = X2
    | k3_subset_1(X2,X1) != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111,c_0_92]),c_0_112])).

cnf(c_0_116,plain,
    ( m1_subset_1(k2_pre_topc(X1,u1_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_52,c_0_92])).

cnf(c_0_117,plain,
    ( v2_tops_1(X2,X1)
    | ~ v1_tops_1(k3_subset_1(u1_struct_0(X1),X2),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_118,negated_conjecture,
    ( v1_tops_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),esk1_0)
    | k2_pre_topc(esk1_0,u1_struct_0(esk1_0)) != u1_struct_0(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113,c_0_53]),c_0_83]),c_0_114]),c_0_80]),c_0_54])])).

cnf(c_0_119,plain,
    ( k2_pre_topc(X1,u1_struct_0(X1)) = u1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_115,c_0_107]),c_0_116]),c_0_104])).

cnf(c_0_120,negated_conjecture,
    ( ~ v2_tops_1(esk2_0,esk1_0)
    | k1_tops_1(esk1_0,esk2_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_121,negated_conjecture,
    ( v2_tops_1(esk2_0,esk1_0)
    | ~ v1_tops_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117,c_0_35]),c_0_54])])).

cnf(c_0_122,negated_conjecture,
    ( v1_tops_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_118,c_0_119]),c_0_54])])).

cnf(c_0_123,negated_conjecture,
    ( ~ v2_tops_1(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_120,c_0_114])])).

cnf(c_0_124,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_121,c_0_122])]),c_0_123]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:27:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.52  # AutoSched0-Mode selected heuristic G_E___024_B31_F1_PI_AE_Q4_CS_SP_S2S
% 0.20/0.52  # and selection function SelectNewComplexAHP.
% 0.20/0.52  #
% 0.20/0.52  # Preprocessing time       : 0.028 s
% 0.20/0.52  
% 0.20/0.52  # Proof found!
% 0.20/0.52  # SZS status Theorem
% 0.20/0.52  # SZS output start CNFRefutation
% 0.20/0.52  fof(t84_tops_1, conjecture, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v2_tops_1(X2,X1)<=>k1_tops_1(X1,X2)=k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_tops_1)).
% 0.20/0.52  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.20/0.52  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.20/0.52  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.20/0.52  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.20/0.52  fof(dt_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 0.20/0.52  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 0.20/0.52  fof(dt_k2_pre_topc, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 0.20/0.52  fof(d1_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k1_tops_1(X1,X2)=k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tops_1)).
% 0.20/0.52  fof(t22_subset_1, axiom, ![X1]:k2_subset_1(X1)=k3_subset_1(X1,k1_subset_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_subset_1)).
% 0.20/0.52  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 0.20/0.52  fof(d3_subset_1, axiom, ![X1]:k1_subset_1(X1)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_subset_1)).
% 0.20/0.52  fof(cc2_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v1_xboole_0(X2)=>v2_tops_1(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_tops_1)).
% 0.20/0.52  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 0.20/0.52  fof(involutiveness_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,k3_subset_1(X1,X2))=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 0.20/0.52  fof(d4_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v2_tops_1(X2,X1)<=>v1_tops_1(k3_subset_1(u1_struct_0(X1),X2),X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tops_1)).
% 0.20/0.52  fof(l13_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)=>X1=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 0.20/0.52  fof(fc8_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>v1_xboole_0(k1_tops_1(X1,k1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc8_tops_1)).
% 0.20/0.52  fof(dt_k2_subset_1, axiom, ![X1]:m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 0.20/0.52  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.20/0.52  fof(d3_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v1_tops_1(X2,X1)<=>k2_pre_topc(X1,X2)=k2_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tops_1)).
% 0.20/0.52  fof(projectivity_k1_tops_1, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>k1_tops_1(X1,k1_tops_1(X1,X2))=k1_tops_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', projectivity_k1_tops_1)).
% 0.20/0.52  fof(t47_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>k1_tops_1(X1,k1_struct_0(X1))=k1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_tops_1)).
% 0.20/0.52  fof(dt_k1_tops_1, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tops_1)).
% 0.20/0.52  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 0.20/0.52  fof(t64_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(k3_subset_1(X1,X2)=k3_subset_1(X1,X3)=>X2=X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_subset_1)).
% 0.20/0.52  fof(c_0_26, negated_conjecture, ~(![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v2_tops_1(X2,X1)<=>k1_tops_1(X1,X2)=k1_xboole_0)))), inference(assume_negation,[status(cth)],[t84_tops_1])).
% 0.20/0.52  fof(c_0_27, plain, ![X27, X28]:((~m1_subset_1(X27,k1_zfmisc_1(X28))|r1_tarski(X27,X28))&(~r1_tarski(X27,X28)|m1_subset_1(X27,k1_zfmisc_1(X28)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.20/0.52  fof(c_0_28, negated_conjecture, (l1_pre_topc(esk1_0)&(m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&((~v2_tops_1(esk2_0,esk1_0)|k1_tops_1(esk1_0,esk2_0)!=k1_xboole_0)&(v2_tops_1(esk2_0,esk1_0)|k1_tops_1(esk1_0,esk2_0)=k1_xboole_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_26])])])).
% 0.20/0.52  fof(c_0_29, plain, ![X11, X12]:r1_tarski(k4_xboole_0(X11,X12),X11), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.20/0.52  fof(c_0_30, plain, ![X5, X6]:k4_xboole_0(X5,X6)=k5_xboole_0(X5,k3_xboole_0(X5,X6)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.20/0.52  fof(c_0_31, plain, ![X13, X14]:k4_xboole_0(X13,k4_xboole_0(X13,X14))=k3_xboole_0(X13,X14), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.20/0.52  fof(c_0_32, plain, ![X18, X19]:(~m1_subset_1(X19,k1_zfmisc_1(X18))|m1_subset_1(k3_subset_1(X18,X19),k1_zfmisc_1(X18))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).
% 0.20/0.52  fof(c_0_33, plain, ![X7, X8, X9]:(~r1_tarski(X7,X8)|~r1_tarski(X8,X9)|r1_tarski(X7,X9)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 0.20/0.52  cnf(c_0_34, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.52  cnf(c_0_35, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.52  cnf(c_0_36, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.20/0.52  cnf(c_0_37, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.52  cnf(c_0_38, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.20/0.52  fof(c_0_39, plain, ![X32, X33]:(~l1_pre_topc(X32)|~m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))|m1_subset_1(k2_pre_topc(X32,X33),k1_zfmisc_1(u1_struct_0(X32)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).
% 0.20/0.52  cnf(c_0_40, plain, (m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.52  fof(c_0_41, plain, ![X36, X37]:(~l1_pre_topc(X36)|(~m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X36)))|k1_tops_1(X36,X37)=k3_subset_1(u1_struct_0(X36),k2_pre_topc(X36,k3_subset_1(u1_struct_0(X36),X37))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tops_1])])])).
% 0.20/0.52  cnf(c_0_42, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.20/0.52  cnf(c_0_43, negated_conjecture, (r1_tarski(esk2_0,u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.20/0.52  cnf(c_0_44, plain, (r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X1)), inference(rw,[status(thm)],[c_0_36, c_0_37])).
% 0.20/0.52  cnf(c_0_45, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_37]), c_0_37])).
% 0.20/0.52  fof(c_0_46, plain, ![X22]:k2_subset_1(X22)=k3_subset_1(X22,k1_subset_1(X22)), inference(variable_rename,[status(thm)],[t22_subset_1])).
% 0.20/0.52  fof(c_0_47, plain, ![X16]:k2_subset_1(X16)=X16, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 0.20/0.52  fof(c_0_48, plain, ![X15]:k1_subset_1(X15)=k1_xboole_0, inference(variable_rename,[status(thm)],[d3_subset_1])).
% 0.20/0.52  fof(c_0_49, plain, ![X34, X35]:(~l1_pre_topc(X34)|(~m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X34)))|(~v1_xboole_0(X35)|v2_tops_1(X35,X34)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_tops_1])])])).
% 0.20/0.52  fof(c_0_50, plain, ![X23]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X23)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.20/0.52  fof(c_0_51, plain, ![X20, X21]:(~m1_subset_1(X21,k1_zfmisc_1(X20))|k3_subset_1(X20,k3_subset_1(X20,X21))=X21), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).
% 0.20/0.52  cnf(c_0_52, plain, (m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.20/0.52  cnf(c_0_53, negated_conjecture, (m1_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_40, c_0_35])).
% 0.20/0.52  cnf(c_0_54, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.52  cnf(c_0_55, plain, (k1_tops_1(X1,X2)=k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.20/0.52  fof(c_0_56, plain, ![X40, X41]:((~v2_tops_1(X41,X40)|v1_tops_1(k3_subset_1(u1_struct_0(X40),X41),X40)|~m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(X40)))|~l1_pre_topc(X40))&(~v1_tops_1(k3_subset_1(u1_struct_0(X40),X41),X40)|v2_tops_1(X41,X40)|~m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(X40)))|~l1_pre_topc(X40))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tops_1])])])])).
% 0.20/0.52  cnf(c_0_57, negated_conjecture, (r1_tarski(X1,u1_struct_0(esk1_0))|~r1_tarski(X1,esk2_0)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.20/0.52  cnf(c_0_58, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.20/0.52  fof(c_0_59, plain, ![X4]:(~v1_xboole_0(X4)|X4=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).
% 0.20/0.52  fof(c_0_60, plain, ![X44]:(~l1_pre_topc(X44)|v1_xboole_0(k1_tops_1(X44,k1_struct_0(X44)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc8_tops_1])])).
% 0.20/0.52  fof(c_0_61, plain, ![X17]:m1_subset_1(k2_subset_1(X17),k1_zfmisc_1(X17)), inference(variable_rename,[status(thm)],[dt_k2_subset_1])).
% 0.20/0.52  cnf(c_0_62, plain, (k2_subset_1(X1)=k3_subset_1(X1,k1_subset_1(X1))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.20/0.52  cnf(c_0_63, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.20/0.52  cnf(c_0_64, plain, (k1_subset_1(X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.20/0.52  cnf(c_0_65, plain, (v2_tops_1(X2,X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v1_xboole_0(X2)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.20/0.52  cnf(c_0_66, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.20/0.52  cnf(c_0_67, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.20/0.52  fof(c_0_68, plain, ![X38, X39]:((~v1_tops_1(X39,X38)|k2_pre_topc(X38,X39)=k2_struct_0(X38)|~m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(X38)))|~l1_pre_topc(X38))&(k2_pre_topc(X38,X39)!=k2_struct_0(X38)|v1_tops_1(X39,X38)|~m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(X38)))|~l1_pre_topc(X38))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tops_1])])])])).
% 0.20/0.52  cnf(c_0_69, plain, (k3_subset_1(X2,k3_subset_1(X2,X1))=X1|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.20/0.52  cnf(c_0_70, negated_conjecture, (m1_subset_1(k2_pre_topc(esk1_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0)),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_54])])).
% 0.20/0.52  cnf(c_0_71, negated_conjecture, (k3_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0)))=k1_tops_1(esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_35]), c_0_54])])).
% 0.20/0.52  cnf(c_0_72, plain, (v1_tops_1(k3_subset_1(u1_struct_0(X2),X1),X2)|~v2_tops_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.20/0.52  fof(c_0_73, plain, ![X45, X46]:(~l1_pre_topc(X45)|~m1_subset_1(X46,k1_zfmisc_1(u1_struct_0(X45)))|k1_tops_1(X45,k1_tops_1(X45,X46))=k1_tops_1(X45,X46)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[projectivity_k1_tops_1])])).
% 0.20/0.52  cnf(c_0_74, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.52  cnf(c_0_75, negated_conjecture, (r1_tarski(k3_xboole_0(esk2_0,X1),u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 0.20/0.52  fof(c_0_76, plain, ![X47]:(~l1_pre_topc(X47)|k1_tops_1(X47,k1_struct_0(X47))=k1_struct_0(X47)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t47_tops_1])])).
% 0.20/0.52  cnf(c_0_77, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.20/0.52  cnf(c_0_78, plain, (v1_xboole_0(k1_tops_1(X1,k1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.20/0.52  cnf(c_0_79, plain, (m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.20/0.52  cnf(c_0_80, plain, (X1=k3_subset_1(X1,k1_xboole_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_62, c_0_63]), c_0_64])).
% 0.20/0.52  cnf(c_0_81, plain, (v2_tops_1(k1_xboole_0,X1)|~l1_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_67])])).
% 0.20/0.52  cnf(c_0_82, plain, (k2_pre_topc(X2,X1)=k2_struct_0(X2)|~v1_tops_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.20/0.52  cnf(c_0_83, negated_conjecture, (k2_pre_topc(esk1_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0))=k3_subset_1(u1_struct_0(esk1_0),k1_tops_1(esk1_0,esk2_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_71])).
% 0.20/0.52  cnf(c_0_84, negated_conjecture, (v1_tops_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),esk1_0)|~v2_tops_1(esk2_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_35]), c_0_54])])).
% 0.20/0.52  cnf(c_0_85, negated_conjecture, (v2_tops_1(esk2_0,esk1_0)|k1_tops_1(esk1_0,esk2_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.52  fof(c_0_86, plain, ![X42, X43]:(~l1_pre_topc(X42)|~m1_subset_1(X43,k1_zfmisc_1(u1_struct_0(X42)))|m1_subset_1(k1_tops_1(X42,X43),k1_zfmisc_1(u1_struct_0(X42)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_tops_1])])).
% 0.20/0.52  cnf(c_0_87, plain, (k1_tops_1(X1,k1_tops_1(X1,X2))=k1_tops_1(X1,X2)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_73])).
% 0.20/0.52  cnf(c_0_88, negated_conjecture, (m1_subset_1(k3_xboole_0(esk2_0,X1),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_74, c_0_75])).
% 0.20/0.52  fof(c_0_89, plain, ![X10]:k3_xboole_0(X10,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 0.20/0.52  cnf(c_0_90, plain, (k1_tops_1(X1,k1_struct_0(X1))=k1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_76])).
% 0.20/0.52  cnf(c_0_91, plain, (k1_tops_1(X1,k1_struct_0(X1))=k1_xboole_0|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_77, c_0_78])).
% 0.20/0.52  cnf(c_0_92, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_79, c_0_63])).
% 0.20/0.52  cnf(c_0_93, plain, (v1_tops_1(u1_struct_0(X1),X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_66]), c_0_80]), c_0_81])).
% 0.20/0.52  cnf(c_0_94, negated_conjecture, (k2_struct_0(esk1_0)=k3_subset_1(u1_struct_0(esk1_0),k1_tops_1(esk1_0,esk2_0))|~v1_tops_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),esk1_0)), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_53]), c_0_54])]), c_0_83])).
% 0.20/0.52  cnf(c_0_95, negated_conjecture, (k1_tops_1(esk1_0,esk2_0)=k1_xboole_0|v1_tops_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),esk1_0)), inference(spm,[status(thm)],[c_0_84, c_0_85])).
% 0.20/0.52  cnf(c_0_96, plain, (m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_86])).
% 0.20/0.52  cnf(c_0_97, negated_conjecture, (k1_tops_1(esk1_0,k1_tops_1(esk1_0,k3_xboole_0(esk2_0,X1)))=k1_tops_1(esk1_0,k3_xboole_0(esk2_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_88]), c_0_54])])).
% 0.20/0.52  cnf(c_0_98, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_89])).
% 0.20/0.52  cnf(c_0_99, plain, (k1_struct_0(X1)=k1_xboole_0|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_90, c_0_91])).
% 0.20/0.52  cnf(c_0_100, plain, (k2_struct_0(X1)=k2_pre_topc(X1,u1_struct_0(X1))|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_92]), c_0_93])).
% 0.20/0.52  cnf(c_0_101, negated_conjecture, (k2_struct_0(esk1_0)=k3_subset_1(u1_struct_0(esk1_0),k1_tops_1(esk1_0,esk2_0))|k1_tops_1(esk1_0,esk2_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_94, c_0_95])).
% 0.20/0.52  cnf(c_0_102, negated_conjecture, (m1_subset_1(k1_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_35]), c_0_54])])).
% 0.20/0.52  cnf(c_0_103, negated_conjecture, (k1_tops_1(esk1_0,k1_tops_1(esk1_0,k1_xboole_0))=k1_tops_1(esk1_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_97, c_0_98])).
% 0.20/0.52  cnf(c_0_104, plain, (k1_tops_1(X1,k1_xboole_0)=k1_xboole_0|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_90, c_0_99])).
% 0.20/0.52  fof(c_0_105, plain, ![X24, X25, X26]:(~m1_subset_1(X25,k1_zfmisc_1(X24))|(~m1_subset_1(X26,k1_zfmisc_1(X24))|(k3_subset_1(X24,X25)!=k3_subset_1(X24,X26)|X25=X26))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_subset_1])])])).
% 0.20/0.52  cnf(c_0_106, plain, (v1_tops_1(X2,X1)|k2_pre_topc(X1,X2)!=k2_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.20/0.52  cnf(c_0_107, plain, (k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,u1_struct_0(X1)))=k1_tops_1(X1,k1_xboole_0)|~l1_pre_topc(X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_66]), c_0_80])).
% 0.20/0.52  cnf(c_0_108, negated_conjecture, (k2_pre_topc(esk1_0,u1_struct_0(esk1_0))=k3_subset_1(u1_struct_0(esk1_0),k1_tops_1(esk1_0,esk2_0))|k1_tops_1(esk1_0,esk2_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_101]), c_0_54])])).
% 0.20/0.52  cnf(c_0_109, negated_conjecture, (k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),k1_tops_1(esk1_0,esk2_0)))=k1_tops_1(esk1_0,esk2_0)), inference(spm,[status(thm)],[c_0_69, c_0_102])).
% 0.20/0.52  cnf(c_0_110, negated_conjecture, (k1_tops_1(esk1_0,k1_xboole_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103, c_0_104]), c_0_54])])).
% 0.20/0.52  cnf(c_0_111, plain, (X1=X3|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))|k3_subset_1(X2,X1)!=k3_subset_1(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_105])).
% 0.20/0.52  cnf(c_0_112, plain, (k3_subset_1(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_66]), c_0_80])).
% 0.20/0.52  cnf(c_0_113, plain, (v1_tops_1(X1,X2)|k2_pre_topc(X2,X1)!=k2_pre_topc(X2,u1_struct_0(X2))|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))), inference(spm,[status(thm)],[c_0_106, c_0_100])).
% 0.20/0.52  cnf(c_0_114, negated_conjecture, (k1_tops_1(esk1_0,esk2_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107, c_0_108]), c_0_109]), c_0_110]), c_0_54])])).
% 0.20/0.52  cnf(c_0_115, plain, (X1=X2|k3_subset_1(X2,X1)!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111, c_0_92]), c_0_112])).
% 0.20/0.52  cnf(c_0_116, plain, (m1_subset_1(k2_pre_topc(X1,u1_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_52, c_0_92])).
% 0.20/0.52  cnf(c_0_117, plain, (v2_tops_1(X2,X1)|~v1_tops_1(k3_subset_1(u1_struct_0(X1),X2),X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.20/0.52  cnf(c_0_118, negated_conjecture, (v1_tops_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),esk1_0)|k2_pre_topc(esk1_0,u1_struct_0(esk1_0))!=u1_struct_0(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113, c_0_53]), c_0_83]), c_0_114]), c_0_80]), c_0_54])])).
% 0.20/0.52  cnf(c_0_119, plain, (k2_pre_topc(X1,u1_struct_0(X1))=u1_struct_0(X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_115, c_0_107]), c_0_116]), c_0_104])).
% 0.20/0.52  cnf(c_0_120, negated_conjecture, (~v2_tops_1(esk2_0,esk1_0)|k1_tops_1(esk1_0,esk2_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.52  cnf(c_0_121, negated_conjecture, (v2_tops_1(esk2_0,esk1_0)|~v1_tops_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117, c_0_35]), c_0_54])])).
% 0.20/0.52  cnf(c_0_122, negated_conjecture, (v1_tops_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_118, c_0_119]), c_0_54])])).
% 0.20/0.52  cnf(c_0_123, negated_conjecture, (~v2_tops_1(esk2_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_120, c_0_114])])).
% 0.20/0.52  cnf(c_0_124, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_121, c_0_122])]), c_0_123]), ['proof']).
% 0.20/0.52  # SZS output end CNFRefutation
% 0.20/0.52  # Proof object total steps             : 125
% 0.20/0.52  # Proof object clause steps            : 73
% 0.20/0.52  # Proof object formula steps           : 52
% 0.20/0.52  # Proof object conjectures             : 31
% 0.20/0.52  # Proof object clause conjectures      : 28
% 0.20/0.52  # Proof object formula conjectures     : 3
% 0.20/0.52  # Proof object initial clauses used    : 32
% 0.20/0.52  # Proof object initial formulas used   : 26
% 0.20/0.52  # Proof object generating inferences   : 35
% 0.20/0.52  # Proof object simplifying inferences  : 52
% 0.20/0.52  # Training examples: 0 positive, 0 negative
% 0.20/0.52  # Parsed axioms                        : 27
% 0.20/0.52  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.52  # Initial clauses                      : 33
% 0.20/0.52  # Removed in clause preprocessing      : 3
% 0.20/0.52  # Initial clauses in saturation        : 30
% 0.20/0.52  # Processed clauses                    : 1479
% 0.20/0.52  # ...of these trivial                  : 76
% 0.20/0.52  # ...subsumed                          : 443
% 0.20/0.52  # ...remaining for further processing  : 960
% 0.20/0.52  # Other redundant clauses eliminated   : 0
% 0.20/0.52  # Clauses deleted for lack of memory   : 0
% 0.20/0.52  # Backward-subsumed                    : 4
% 0.20/0.52  # Backward-rewritten                   : 124
% 0.20/0.52  # Generated clauses                    : 9246
% 0.20/0.52  # ...of the previous two non-trivial   : 7173
% 0.20/0.52  # Contextual simplify-reflections      : 9
% 0.20/0.52  # Paramodulations                      : 9244
% 0.20/0.52  # Factorizations                       : 0
% 0.20/0.52  # Equation resolutions                 : 2
% 0.20/0.52  # Propositional unsat checks           : 0
% 0.20/0.52  #    Propositional check models        : 0
% 0.20/0.52  #    Propositional check unsatisfiable : 0
% 0.20/0.52  #    Propositional clauses             : 0
% 0.20/0.52  #    Propositional clauses after purity: 0
% 0.20/0.52  #    Propositional unsat core size     : 0
% 0.20/0.52  #    Propositional preprocessing time  : 0.000
% 0.20/0.52  #    Propositional encoding time       : 0.000
% 0.20/0.52  #    Propositional solver time         : 0.000
% 0.20/0.52  #    Success case prop preproc time    : 0.000
% 0.20/0.52  #    Success case prop encoding time   : 0.000
% 0.20/0.52  #    Success case prop solver time     : 0.000
% 0.20/0.52  # Current number of processed clauses  : 832
% 0.20/0.52  #    Positive orientable unit clauses  : 369
% 0.20/0.52  #    Positive unorientable unit clauses: 0
% 0.20/0.52  #    Negative unit clauses             : 1
% 0.20/0.52  #    Non-unit-clauses                  : 462
% 0.20/0.52  # Current number of unprocessed clauses: 5641
% 0.20/0.52  # ...number of literals in the above   : 10953
% 0.20/0.52  # Current number of archived formulas  : 0
% 0.20/0.52  # Current number of archived clauses   : 131
% 0.20/0.52  # Clause-clause subsumption calls (NU) : 16632
% 0.20/0.52  # Rec. Clause-clause subsumption calls : 15353
% 0.20/0.52  # Non-unit clause-clause subsumptions  : 456
% 0.20/0.52  # Unit Clause-clause subsumption calls : 501
% 0.20/0.52  # Rewrite failures with RHS unbound    : 0
% 0.20/0.52  # BW rewrite match attempts            : 1093
% 0.20/0.52  # BW rewrite match successes           : 14
% 0.20/0.52  # Condensation attempts                : 0
% 0.20/0.52  # Condensation successes               : 0
% 0.20/0.52  # Termbank termtop insertions          : 162965
% 0.20/0.52  
% 0.20/0.52  # -------------------------------------------------
% 0.20/0.52  # User time                : 0.172 s
% 0.20/0.52  # System time              : 0.009 s
% 0.20/0.52  # Total time               : 0.181 s
% 0.20/0.52  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
