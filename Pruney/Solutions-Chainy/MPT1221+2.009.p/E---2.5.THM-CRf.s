%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:10:34 EST 2020

% Result     : Theorem 1.62s
% Output     : CNFRefutation 1.62s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 249 expanded)
%              Number of clauses        :   33 (  97 expanded)
%              Number of leaves         :   13 (  65 expanded)
%              Depth                    :   13
%              Number of atoms          :  184 ( 809 expanded)
%              Number of equality atoms :   23 (  69 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal clause size      :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t29_tops_1,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v4_pre_topc(X2,X1)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X1),X2),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tops_1)).

fof(t25_pre_topc,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( ( k2_struct_0(X1) = k4_subset_1(u1_struct_0(X1),X2,X3)
                  & r1_xboole_0(X2,X3) )
               => X3 = k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_pre_topc)).

fof(t18_pre_topc,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k4_subset_1(u1_struct_0(X1),X2,k3_subset_1(u1_struct_0(X1),X2)) = k2_struct_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_pre_topc)).

fof(involutiveness_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,k3_subset_1(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(dt_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(d6_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v4_pre_topc(X2,X1)
          <=> v3_pre_topc(k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_pre_topc)).

fof(t22_pre_topc,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2)) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_pre_topc)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(t43_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => ( r1_xboole_0(X2,X3)
          <=> r1_tarski(X2,k3_subset_1(X1,X3)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_subset_1)).

fof(t42_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => r1_tarski(k3_subset_1(X1,X2),k3_subset_1(X1,k9_subset_1(X1,X2,X3))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_subset_1)).

fof(dt_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => m1_subset_1(k9_subset_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).

fof(idempotence_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X2) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k9_subset_1)).

fof(rc2_subset_1,axiom,(
    ! [X1] :
    ? [X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
      & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc2_subset_1)).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( v4_pre_topc(X2,X1)
            <=> v3_pre_topc(k3_subset_1(u1_struct_0(X1),X2),X1) ) ) ) ),
    inference(assume_negation,[status(cth)],[t29_tops_1])).

fof(c_0_14,plain,(
    ! [X60,X61,X62] :
      ( ~ l1_struct_0(X60)
      | ~ m1_subset_1(X61,k1_zfmisc_1(u1_struct_0(X60)))
      | ~ m1_subset_1(X62,k1_zfmisc_1(u1_struct_0(X60)))
      | k2_struct_0(X60) != k4_subset_1(u1_struct_0(X60),X61,X62)
      | ~ r1_xboole_0(X61,X62)
      | X62 = k7_subset_1(u1_struct_0(X60),k2_struct_0(X60),X61) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_pre_topc])])])).

fof(c_0_15,negated_conjecture,
    ( l1_pre_topc(esk4_0)
    & m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0)))
    & ( ~ v4_pre_topc(esk5_0,esk4_0)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(esk4_0),esk5_0),esk4_0) )
    & ( v4_pre_topc(esk5_0,esk4_0)
      | v3_pre_topc(k3_subset_1(u1_struct_0(esk4_0),esk5_0),esk4_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).

fof(c_0_16,plain,(
    ! [X54,X55] :
      ( ~ l1_struct_0(X54)
      | ~ m1_subset_1(X55,k1_zfmisc_1(u1_struct_0(X54)))
      | k4_subset_1(u1_struct_0(X54),X55,k3_subset_1(u1_struct_0(X54),X55)) = k2_struct_0(X54) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t18_pre_topc])])])).

fof(c_0_17,plain,(
    ! [X15,X16] :
      ( ~ m1_subset_1(X16,k1_zfmisc_1(X15))
      | k3_subset_1(X15,k3_subset_1(X15,X16)) = X16 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).

fof(c_0_18,plain,(
    ! [X7,X8] :
      ( ~ m1_subset_1(X8,k1_zfmisc_1(X7))
      | m1_subset_1(k3_subset_1(X7,X8),k1_zfmisc_1(X7)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).

fof(c_0_19,plain,(
    ! [X47,X48] :
      ( ( ~ v4_pre_topc(X48,X47)
        | v3_pre_topc(k7_subset_1(u1_struct_0(X47),k2_struct_0(X47),X48),X47)
        | ~ m1_subset_1(X48,k1_zfmisc_1(u1_struct_0(X47)))
        | ~ l1_pre_topc(X47) )
      & ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(X47),k2_struct_0(X47),X48),X47)
        | v4_pre_topc(X48,X47)
        | ~ m1_subset_1(X48,k1_zfmisc_1(u1_struct_0(X47)))
        | ~ l1_pre_topc(X47) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_pre_topc])])])])).

fof(c_0_20,plain,(
    ! [X56,X57] :
      ( ~ l1_struct_0(X56)
      | ~ m1_subset_1(X57,k1_zfmisc_1(u1_struct_0(X56)))
      | k7_subset_1(u1_struct_0(X56),k2_struct_0(X56),k7_subset_1(u1_struct_0(X56),k2_struct_0(X56),X57)) = X57 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t22_pre_topc])])])).

fof(c_0_21,plain,(
    ! [X52] :
      ( ~ l1_pre_topc(X52)
      | l1_struct_0(X52) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_22,plain,
    ( X3 = k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2)
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_struct_0(X1) != k4_subset_1(u1_struct_0(X1),X2,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,plain,
    ( k4_subset_1(u1_struct_0(X1),X2,k3_subset_1(u1_struct_0(X1),X2)) = k2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,plain,
    ( k3_subset_1(X2,k3_subset_1(X2,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,plain,
    ( m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_27,plain,(
    ! [X25,X26,X27] :
      ( ( ~ r1_xboole_0(X26,X27)
        | r1_tarski(X26,k3_subset_1(X25,X27))
        | ~ m1_subset_1(X27,k1_zfmisc_1(X25))
        | ~ m1_subset_1(X26,k1_zfmisc_1(X25)) )
      & ( ~ r1_tarski(X26,k3_subset_1(X25,X27))
        | r1_xboole_0(X26,X27)
        | ~ m1_subset_1(X27,k1_zfmisc_1(X25))
        | ~ m1_subset_1(X26,k1_zfmisc_1(X25)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_subset_1])])])])).

fof(c_0_28,plain,(
    ! [X22,X23,X24] :
      ( ~ m1_subset_1(X23,k1_zfmisc_1(X22))
      | ~ m1_subset_1(X24,k1_zfmisc_1(X22))
      | r1_tarski(k3_subset_1(X22,X23),k3_subset_1(X22,k9_subset_1(X22,X23,X24))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t42_subset_1])])])).

fof(c_0_29,plain,(
    ! [X9,X10,X11] :
      ( ~ m1_subset_1(X11,k1_zfmisc_1(X9))
      | m1_subset_1(k9_subset_1(X9,X10,X11),k1_zfmisc_1(X9)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k9_subset_1])])).

fof(c_0_30,plain,(
    ! [X12,X13,X14] :
      ( ~ m1_subset_1(X14,k1_zfmisc_1(X12))
      | k9_subset_1(X12,X13,X13) = X13 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[idempotence_k9_subset_1])])).

fof(c_0_31,plain,(
    ! [X17] :
      ( m1_subset_1(esk1_1(X17),k1_zfmisc_1(X17))
      & v1_xboole_0(esk1_1(X17)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[rc2_subset_1])])).

cnf(c_0_32,plain,
    ( v4_pre_topc(X2,X1)
    | ~ v3_pre_topc(k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_33,plain,
    ( k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2)) = X2
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_34,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_35,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk4_0),k2_struct_0(esk4_0),X1) = esk5_0
    | k4_subset_1(u1_struct_0(esk4_0),X1,esk5_0) != k2_struct_0(esk4_0)
    | ~ l1_struct_0(esk4_0)
    | ~ r1_xboole_0(X1,esk5_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_36,plain,
    ( k4_subset_1(u1_struct_0(X1),k3_subset_1(u1_struct_0(X1),X2),X2) = k2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26])).

cnf(c_0_37,plain,
    ( r1_xboole_0(X1,X3)
    | ~ r1_tarski(X1,k3_subset_1(X2,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_38,plain,
    ( r1_tarski(k3_subset_1(X2,X1),k3_subset_1(X2,k9_subset_1(X2,X1,X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_39,plain,
    ( m1_subset_1(k9_subset_1(X2,X3,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_40,plain,
    ( k9_subset_1(X2,X3,X3) = X3
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_41,plain,
    ( m1_subset_1(esk1_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_42,plain,
    ( v4_pre_topc(k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2),X1)
    | ~ v3_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34])).

cnf(c_0_43,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk4_0),k2_struct_0(esk4_0),k3_subset_1(u1_struct_0(esk4_0),esk5_0)) = esk5_0
    | ~ l1_struct_0(esk4_0)
    | ~ r1_xboole_0(k3_subset_1(u1_struct_0(esk4_0),esk5_0),esk5_0)
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(esk4_0),esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_23])])).

cnf(c_0_44,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_45,negated_conjecture,
    ( v4_pre_topc(esk5_0,esk4_0)
    | v3_pre_topc(k3_subset_1(u1_struct_0(esk4_0),esk5_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_46,plain,
    ( r1_xboole_0(k3_subset_1(X1,X2),k9_subset_1(X1,X2,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_26]),c_0_39])).

cnf(c_0_47,plain,
    ( k9_subset_1(X1,X2,X2) = X2 ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_48,negated_conjecture,
    ( v4_pre_topc(esk5_0,esk4_0)
    | ~ l1_struct_0(esk4_0)
    | ~ r1_xboole_0(k3_subset_1(u1_struct_0(esk4_0),esk5_0),esk5_0)
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(esk4_0),esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_44]),c_0_23])]),c_0_45])).

cnf(c_0_49,plain,
    ( r1_xboole_0(k3_subset_1(X1,X2),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_50,plain,
    ( v3_pre_topc(k7_subset_1(u1_struct_0(X2),k2_struct_0(X2),X1),X2)
    | ~ v4_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_51,negated_conjecture,
    ( v4_pre_topc(esk5_0,esk4_0)
    | ~ l1_struct_0(esk4_0)
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(esk4_0),esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_23])])).

cnf(c_0_52,plain,
    ( v3_pre_topc(X1,X2)
    | ~ v4_pre_topc(k7_subset_1(u1_struct_0(X2),k2_struct_0(X2),X1),X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(k7_subset_1(u1_struct_0(X2),k2_struct_0(X2),X1),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_33]),c_0_34])).

cnf(c_0_53,negated_conjecture,
    ( v4_pre_topc(esk5_0,esk4_0)
    | ~ l1_struct_0(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_26]),c_0_23])])).

cnf(c_0_54,negated_conjecture,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(esk4_0),esk5_0),esk4_0)
    | ~ l1_struct_0(esk4_0)
    | ~ r1_xboole_0(k3_subset_1(u1_struct_0(esk4_0),esk5_0),esk5_0)
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(esk4_0),esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_43]),c_0_44]),c_0_23])]),c_0_53])).

cnf(c_0_55,negated_conjecture,
    ( ~ v4_pre_topc(esk5_0,esk4_0)
    | ~ v3_pre_topc(k3_subset_1(u1_struct_0(esk4_0),esk5_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_56,negated_conjecture,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(esk4_0),esk5_0),esk4_0)
    | ~ l1_struct_0(esk4_0)
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(esk4_0),esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_49]),c_0_23])])).

cnf(c_0_57,negated_conjecture,
    ( ~ l1_struct_0(esk4_0)
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(esk4_0),esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_53])).

cnf(c_0_58,negated_conjecture,
    ( ~ l1_struct_0(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_26]),c_0_23])])).

cnf(c_0_59,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_34]),c_0_44])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:08:16 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 1.62/1.79  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 1.62/1.79  # and selection function SelectComplexExceptUniqMaxHorn.
% 1.62/1.79  #
% 1.62/1.79  # Preprocessing time       : 0.030 s
% 1.62/1.79  # Presaturation interreduction done
% 1.62/1.79  
% 1.62/1.79  # Proof found!
% 1.62/1.79  # SZS status Theorem
% 1.62/1.79  # SZS output start CNFRefutation
% 1.62/1.79  fof(t29_tops_1, conjecture, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v4_pre_topc(X2,X1)<=>v3_pre_topc(k3_subset_1(u1_struct_0(X1),X2),X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_tops_1)).
% 1.62/1.79  fof(t25_pre_topc, axiom, ![X1]:(l1_struct_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((k2_struct_0(X1)=k4_subset_1(u1_struct_0(X1),X2,X3)&r1_xboole_0(X2,X3))=>X3=k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_pre_topc)).
% 1.62/1.79  fof(t18_pre_topc, axiom, ![X1]:(l1_struct_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k4_subset_1(u1_struct_0(X1),X2,k3_subset_1(u1_struct_0(X1),X2))=k2_struct_0(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_pre_topc)).
% 1.62/1.79  fof(involutiveness_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,k3_subset_1(X1,X2))=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 1.62/1.79  fof(dt_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 1.62/1.79  fof(d6_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v4_pre_topc(X2,X1)<=>v3_pre_topc(k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2),X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_pre_topc)).
% 1.62/1.79  fof(t22_pre_topc, axiom, ![X1]:(l1_struct_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2))=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_pre_topc)).
% 1.62/1.79  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 1.62/1.79  fof(t43_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(r1_xboole_0(X2,X3)<=>r1_tarski(X2,k3_subset_1(X1,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_subset_1)).
% 1.62/1.79  fof(t42_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>r1_tarski(k3_subset_1(X1,X2),k3_subset_1(X1,k9_subset_1(X1,X2,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_subset_1)).
% 1.62/1.79  fof(dt_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>m1_subset_1(k9_subset_1(X1,X2,X3),k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 1.62/1.79  fof(idempotence_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k9_subset_1(X1,X2,X2)=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k9_subset_1)).
% 1.62/1.79  fof(rc2_subset_1, axiom, ![X1]:?[X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))&v1_xboole_0(X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc2_subset_1)).
% 1.62/1.79  fof(c_0_13, negated_conjecture, ~(![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v4_pre_topc(X2,X1)<=>v3_pre_topc(k3_subset_1(u1_struct_0(X1),X2),X1))))), inference(assume_negation,[status(cth)],[t29_tops_1])).
% 1.62/1.79  fof(c_0_14, plain, ![X60, X61, X62]:(~l1_struct_0(X60)|(~m1_subset_1(X61,k1_zfmisc_1(u1_struct_0(X60)))|(~m1_subset_1(X62,k1_zfmisc_1(u1_struct_0(X60)))|(k2_struct_0(X60)!=k4_subset_1(u1_struct_0(X60),X61,X62)|~r1_xboole_0(X61,X62)|X62=k7_subset_1(u1_struct_0(X60),k2_struct_0(X60),X61))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_pre_topc])])])).
% 1.62/1.79  fof(c_0_15, negated_conjecture, (l1_pre_topc(esk4_0)&(m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0)))&((~v4_pre_topc(esk5_0,esk4_0)|~v3_pre_topc(k3_subset_1(u1_struct_0(esk4_0),esk5_0),esk4_0))&(v4_pre_topc(esk5_0,esk4_0)|v3_pre_topc(k3_subset_1(u1_struct_0(esk4_0),esk5_0),esk4_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).
% 1.62/1.79  fof(c_0_16, plain, ![X54, X55]:(~l1_struct_0(X54)|(~m1_subset_1(X55,k1_zfmisc_1(u1_struct_0(X54)))|k4_subset_1(u1_struct_0(X54),X55,k3_subset_1(u1_struct_0(X54),X55))=k2_struct_0(X54))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t18_pre_topc])])])).
% 1.62/1.79  fof(c_0_17, plain, ![X15, X16]:(~m1_subset_1(X16,k1_zfmisc_1(X15))|k3_subset_1(X15,k3_subset_1(X15,X16))=X16), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).
% 1.62/1.79  fof(c_0_18, plain, ![X7, X8]:(~m1_subset_1(X8,k1_zfmisc_1(X7))|m1_subset_1(k3_subset_1(X7,X8),k1_zfmisc_1(X7))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).
% 1.62/1.79  fof(c_0_19, plain, ![X47, X48]:((~v4_pre_topc(X48,X47)|v3_pre_topc(k7_subset_1(u1_struct_0(X47),k2_struct_0(X47),X48),X47)|~m1_subset_1(X48,k1_zfmisc_1(u1_struct_0(X47)))|~l1_pre_topc(X47))&(~v3_pre_topc(k7_subset_1(u1_struct_0(X47),k2_struct_0(X47),X48),X47)|v4_pre_topc(X48,X47)|~m1_subset_1(X48,k1_zfmisc_1(u1_struct_0(X47)))|~l1_pre_topc(X47))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_pre_topc])])])])).
% 1.62/1.79  fof(c_0_20, plain, ![X56, X57]:(~l1_struct_0(X56)|(~m1_subset_1(X57,k1_zfmisc_1(u1_struct_0(X56)))|k7_subset_1(u1_struct_0(X56),k2_struct_0(X56),k7_subset_1(u1_struct_0(X56),k2_struct_0(X56),X57))=X57)), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t22_pre_topc])])])).
% 1.62/1.79  fof(c_0_21, plain, ![X52]:(~l1_pre_topc(X52)|l1_struct_0(X52)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 1.62/1.79  cnf(c_0_22, plain, (X3=k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2)|~l1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|k2_struct_0(X1)!=k4_subset_1(u1_struct_0(X1),X2,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 1.62/1.79  cnf(c_0_23, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 1.62/1.79  cnf(c_0_24, plain, (k4_subset_1(u1_struct_0(X1),X2,k3_subset_1(u1_struct_0(X1),X2))=k2_struct_0(X1)|~l1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 1.62/1.79  cnf(c_0_25, plain, (k3_subset_1(X2,k3_subset_1(X2,X1))=X1|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 1.62/1.79  cnf(c_0_26, plain, (m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 1.62/1.79  fof(c_0_27, plain, ![X25, X26, X27]:((~r1_xboole_0(X26,X27)|r1_tarski(X26,k3_subset_1(X25,X27))|~m1_subset_1(X27,k1_zfmisc_1(X25))|~m1_subset_1(X26,k1_zfmisc_1(X25)))&(~r1_tarski(X26,k3_subset_1(X25,X27))|r1_xboole_0(X26,X27)|~m1_subset_1(X27,k1_zfmisc_1(X25))|~m1_subset_1(X26,k1_zfmisc_1(X25)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_subset_1])])])])).
% 1.62/1.79  fof(c_0_28, plain, ![X22, X23, X24]:(~m1_subset_1(X23,k1_zfmisc_1(X22))|(~m1_subset_1(X24,k1_zfmisc_1(X22))|r1_tarski(k3_subset_1(X22,X23),k3_subset_1(X22,k9_subset_1(X22,X23,X24))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t42_subset_1])])])).
% 1.62/1.79  fof(c_0_29, plain, ![X9, X10, X11]:(~m1_subset_1(X11,k1_zfmisc_1(X9))|m1_subset_1(k9_subset_1(X9,X10,X11),k1_zfmisc_1(X9))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k9_subset_1])])).
% 1.62/1.79  fof(c_0_30, plain, ![X12, X13, X14]:(~m1_subset_1(X14,k1_zfmisc_1(X12))|k9_subset_1(X12,X13,X13)=X13), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[idempotence_k9_subset_1])])).
% 1.62/1.79  fof(c_0_31, plain, ![X17]:(m1_subset_1(esk1_1(X17),k1_zfmisc_1(X17))&v1_xboole_0(esk1_1(X17))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[rc2_subset_1])])).
% 1.62/1.79  cnf(c_0_32, plain, (v4_pre_topc(X2,X1)|~v3_pre_topc(k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2),X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 1.62/1.79  cnf(c_0_33, plain, (k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2))=X2|~l1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 1.62/1.79  cnf(c_0_34, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 1.62/1.79  cnf(c_0_35, negated_conjecture, (k7_subset_1(u1_struct_0(esk4_0),k2_struct_0(esk4_0),X1)=esk5_0|k4_subset_1(u1_struct_0(esk4_0),X1,esk5_0)!=k2_struct_0(esk4_0)|~l1_struct_0(esk4_0)|~r1_xboole_0(X1,esk5_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 1.62/1.79  cnf(c_0_36, plain, (k4_subset_1(u1_struct_0(X1),k3_subset_1(u1_struct_0(X1),X2),X2)=k2_struct_0(X1)|~l1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_26])).
% 1.62/1.79  cnf(c_0_37, plain, (r1_xboole_0(X1,X3)|~r1_tarski(X1,k3_subset_1(X2,X3))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 1.62/1.79  cnf(c_0_38, plain, (r1_tarski(k3_subset_1(X2,X1),k3_subset_1(X2,k9_subset_1(X2,X1,X3)))|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 1.62/1.79  cnf(c_0_39, plain, (m1_subset_1(k9_subset_1(X2,X3,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 1.62/1.79  cnf(c_0_40, plain, (k9_subset_1(X2,X3,X3)=X3|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 1.62/1.79  cnf(c_0_41, plain, (m1_subset_1(esk1_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 1.62/1.79  cnf(c_0_42, plain, (v4_pre_topc(k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2),X1)|~v3_pre_topc(X2,X1)|~l1_pre_topc(X1)|~m1_subset_1(k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2),k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_34])).
% 1.62/1.79  cnf(c_0_43, negated_conjecture, (k7_subset_1(u1_struct_0(esk4_0),k2_struct_0(esk4_0),k3_subset_1(u1_struct_0(esk4_0),esk5_0))=esk5_0|~l1_struct_0(esk4_0)|~r1_xboole_0(k3_subset_1(u1_struct_0(esk4_0),esk5_0),esk5_0)|~m1_subset_1(k3_subset_1(u1_struct_0(esk4_0),esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_23])])).
% 1.62/1.79  cnf(c_0_44, negated_conjecture, (l1_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 1.62/1.79  cnf(c_0_45, negated_conjecture, (v4_pre_topc(esk5_0,esk4_0)|v3_pre_topc(k3_subset_1(u1_struct_0(esk4_0),esk5_0),esk4_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 1.62/1.79  cnf(c_0_46, plain, (r1_xboole_0(k3_subset_1(X1,X2),k9_subset_1(X1,X2,X3))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_26]), c_0_39])).
% 1.62/1.79  cnf(c_0_47, plain, (k9_subset_1(X1,X2,X2)=X2), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 1.62/1.79  cnf(c_0_48, negated_conjecture, (v4_pre_topc(esk5_0,esk4_0)|~l1_struct_0(esk4_0)|~r1_xboole_0(k3_subset_1(u1_struct_0(esk4_0),esk5_0),esk5_0)|~m1_subset_1(k3_subset_1(u1_struct_0(esk4_0),esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_44]), c_0_23])]), c_0_45])).
% 1.62/1.79  cnf(c_0_49, plain, (r1_xboole_0(k3_subset_1(X1,X2),X2)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 1.62/1.79  cnf(c_0_50, plain, (v3_pre_topc(k7_subset_1(u1_struct_0(X2),k2_struct_0(X2),X1),X2)|~v4_pre_topc(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 1.62/1.79  cnf(c_0_51, negated_conjecture, (v4_pre_topc(esk5_0,esk4_0)|~l1_struct_0(esk4_0)|~m1_subset_1(k3_subset_1(u1_struct_0(esk4_0),esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_23])])).
% 1.62/1.79  cnf(c_0_52, plain, (v3_pre_topc(X1,X2)|~v4_pre_topc(k7_subset_1(u1_struct_0(X2),k2_struct_0(X2),X1),X2)|~l1_pre_topc(X2)|~m1_subset_1(k7_subset_1(u1_struct_0(X2),k2_struct_0(X2),X1),k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_33]), c_0_34])).
% 1.62/1.79  cnf(c_0_53, negated_conjecture, (v4_pre_topc(esk5_0,esk4_0)|~l1_struct_0(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_26]), c_0_23])])).
% 1.62/1.79  cnf(c_0_54, negated_conjecture, (v3_pre_topc(k3_subset_1(u1_struct_0(esk4_0),esk5_0),esk4_0)|~l1_struct_0(esk4_0)|~r1_xboole_0(k3_subset_1(u1_struct_0(esk4_0),esk5_0),esk5_0)|~m1_subset_1(k3_subset_1(u1_struct_0(esk4_0),esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_43]), c_0_44]), c_0_23])]), c_0_53])).
% 1.62/1.79  cnf(c_0_55, negated_conjecture, (~v4_pre_topc(esk5_0,esk4_0)|~v3_pre_topc(k3_subset_1(u1_struct_0(esk4_0),esk5_0),esk4_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 1.62/1.79  cnf(c_0_56, negated_conjecture, (v3_pre_topc(k3_subset_1(u1_struct_0(esk4_0),esk5_0),esk4_0)|~l1_struct_0(esk4_0)|~m1_subset_1(k3_subset_1(u1_struct_0(esk4_0),esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_49]), c_0_23])])).
% 1.62/1.79  cnf(c_0_57, negated_conjecture, (~l1_struct_0(esk4_0)|~m1_subset_1(k3_subset_1(u1_struct_0(esk4_0),esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_53])).
% 1.62/1.79  cnf(c_0_58, negated_conjecture, (~l1_struct_0(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_26]), c_0_23])])).
% 1.62/1.79  cnf(c_0_59, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_34]), c_0_44])]), ['proof']).
% 1.62/1.79  # SZS output end CNFRefutation
% 1.62/1.79  # Proof object total steps             : 60
% 1.62/1.79  # Proof object clause steps            : 33
% 1.62/1.79  # Proof object formula steps           : 27
% 1.62/1.79  # Proof object conjectures             : 17
% 1.62/1.79  # Proof object clause conjectures      : 14
% 1.62/1.79  # Proof object formula conjectures     : 3
% 1.62/1.79  # Proof object initial clauses used    : 17
% 1.62/1.79  # Proof object initial formulas used   : 13
% 1.62/1.79  # Proof object generating inferences   : 16
% 1.62/1.79  # Proof object simplifying inferences  : 26
% 1.62/1.79  # Training examples: 0 positive, 0 negative
% 1.62/1.79  # Parsed axioms                        : 28
% 1.62/1.79  # Removed by relevancy pruning/SinE    : 0
% 1.62/1.79  # Initial clauses                      : 43
% 1.62/1.79  # Removed in clause preprocessing      : 0
% 1.62/1.79  # Initial clauses in saturation        : 43
% 1.62/1.79  # Processed clauses                    : 13868
% 1.62/1.79  # ...of these trivial                  : 18
% 1.62/1.79  # ...subsumed                          : 10078
% 1.62/1.79  # ...remaining for further processing  : 3772
% 1.62/1.79  # Other redundant clauses eliminated   : 2
% 1.62/1.79  # Clauses deleted for lack of memory   : 0
% 1.62/1.79  # Backward-subsumed                    : 689
% 1.62/1.79  # Backward-rewritten                   : 901
% 1.62/1.79  # Generated clauses                    : 102227
% 1.62/1.79  # ...of the previous two non-trivial   : 93215
% 1.62/1.79  # Contextual simplify-reflections      : 460
% 1.62/1.79  # Paramodulations                      : 102216
% 1.62/1.79  # Factorizations                       : 6
% 1.62/1.79  # Equation resolutions                 : 2
% 1.62/1.79  # Propositional unsat checks           : 0
% 1.62/1.79  #    Propositional check models        : 0
% 1.62/1.79  #    Propositional check unsatisfiable : 0
% 1.62/1.79  #    Propositional clauses             : 0
% 1.62/1.79  #    Propositional clauses after purity: 0
% 1.62/1.79  #    Propositional unsat core size     : 0
% 1.62/1.79  #    Propositional preprocessing time  : 0.000
% 1.62/1.79  #    Propositional encoding time       : 0.000
% 1.62/1.79  #    Propositional solver time         : 0.000
% 1.62/1.79  #    Success case prop preproc time    : 0.000
% 1.62/1.79  #    Success case prop encoding time   : 0.000
% 1.62/1.79  #    Success case prop solver time     : 0.000
% 1.62/1.79  # Current number of processed clauses  : 2137
% 1.62/1.79  #    Positive orientable unit clauses  : 27
% 1.62/1.79  #    Positive unorientable unit clauses: 0
% 1.62/1.79  #    Negative unit clauses             : 3
% 1.62/1.79  #    Non-unit-clauses                  : 2107
% 1.62/1.79  # Current number of unprocessed clauses: 77916
% 1.62/1.79  # ...number of literals in the above   : 302267
% 1.62/1.79  # Current number of archived formulas  : 0
% 1.62/1.79  # Current number of archived clauses   : 1634
% 1.62/1.79  # Clause-clause subsumption calls (NU) : 1159359
% 1.62/1.79  # Rec. Clause-clause subsumption calls : 647927
% 1.62/1.79  # Non-unit clause-clause subsumptions  : 10099
% 1.62/1.79  # Unit Clause-clause subsumption calls : 8357
% 1.62/1.79  # Rewrite failures with RHS unbound    : 0
% 1.62/1.79  # BW rewrite match attempts            : 35
% 1.62/1.79  # BW rewrite match successes           : 31
% 1.62/1.79  # Condensation attempts                : 0
% 1.62/1.79  # Condensation successes               : 0
% 1.62/1.79  # Termbank termtop insertions          : 2577718
% 1.64/1.80  
% 1.64/1.80  # -------------------------------------------------
% 1.64/1.80  # User time                : 1.402 s
% 1.64/1.80  # System time              : 0.046 s
% 1.64/1.80  # Total time               : 1.448 s
% 1.64/1.80  # Maximum resident set size: 1604 pages
%------------------------------------------------------------------------------
