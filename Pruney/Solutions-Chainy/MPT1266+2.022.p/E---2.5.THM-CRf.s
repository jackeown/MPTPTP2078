%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:12:02 EST 2020

% Result     : Theorem 0.50s
% Output     : CNFRefutation 0.50s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 595 expanded)
%              Number of clauses        :   46 ( 243 expanded)
%              Number of leaves         :   14 ( 160 expanded)
%              Depth                    :   11
%              Number of atoms          :  172 (1224 expanded)
%              Number of equality atoms :   52 ( 480 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t84_tops_1,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v2_tops_1(X2,X1)
          <=> k1_tops_1(X1,X2) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).

fof(d3_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v1_tops_1(X2,X1)
          <=> k2_pre_topc(X1,X2) = k2_struct_0(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_1)).

fof(dt_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(d4_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v2_tops_1(X2,X1)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(X1),X2),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_1)).

fof(t25_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k4_subset_1(X1,X2,k3_subset_1(X1,X2)) = k2_subset_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(t22_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = k3_subset_1(X1,k1_subset_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).

fof(d3_subset_1,axiom,(
    ! [X1] : k1_subset_1(X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

fof(d1_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k1_tops_1(X1,X2) = k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(t18_pre_topc,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k4_subset_1(u1_struct_0(X1),X2,k3_subset_1(u1_struct_0(X1),X2)) = k2_struct_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_pre_topc)).

fof(involutiveness_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,k3_subset_1(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(dt_k2_pre_topc,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( v2_tops_1(X2,X1)
            <=> k1_tops_1(X1,X2) = k1_xboole_0 ) ) ) ),
    inference(assume_negation,[status(cth)],[t84_tops_1])).

fof(c_0_15,plain,(
    ! [X24,X25] :
      ( ( ~ v1_tops_1(X25,X24)
        | k2_pre_topc(X24,X25) = k2_struct_0(X24)
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))
        | ~ l1_pre_topc(X24) )
      & ( k2_pre_topc(X24,X25) != k2_struct_0(X24)
        | v1_tops_1(X25,X24)
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))
        | ~ l1_pre_topc(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tops_1])])])])).

fof(c_0_16,plain,(
    ! [X6,X7] :
      ( ~ m1_subset_1(X7,k1_zfmisc_1(X6))
      | m1_subset_1(k3_subset_1(X6,X7),k1_zfmisc_1(X6)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).

fof(c_0_17,plain,(
    ! [X26,X27] :
      ( ( ~ v2_tops_1(X27,X26)
        | v1_tops_1(k3_subset_1(u1_struct_0(X26),X27),X26)
        | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))
        | ~ l1_pre_topc(X26) )
      & ( ~ v1_tops_1(k3_subset_1(u1_struct_0(X26),X27),X26)
        | v2_tops_1(X27,X26)
        | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))
        | ~ l1_pre_topc(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tops_1])])])])).

fof(c_0_18,negated_conjecture,
    ( l1_pre_topc(esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & ( ~ v2_tops_1(esk2_0,esk1_0)
      | k1_tops_1(esk1_0,esk2_0) != k1_xboole_0 )
    & ( v2_tops_1(esk2_0,esk1_0)
      | k1_tops_1(esk1_0,esk2_0) = k1_xboole_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).

fof(c_0_19,plain,(
    ! [X11,X12] :
      ( ~ m1_subset_1(X12,k1_zfmisc_1(X11))
      | k4_subset_1(X11,X12,k3_subset_1(X11,X12)) = k2_subset_1(X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_subset_1])])).

fof(c_0_20,plain,(
    ! [X5] : k2_subset_1(X5) = X5 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

fof(c_0_21,plain,(
    ! [X10] : k2_subset_1(X10) = k3_subset_1(X10,k1_subset_1(X10)) ),
    inference(variable_rename,[status(thm)],[t22_subset_1])).

fof(c_0_22,plain,(
    ! [X4] : k1_subset_1(X4) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[d3_subset_1])).

fof(c_0_23,plain,(
    ! [X22,X23] :
      ( ~ l1_pre_topc(X22)
      | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))
      | k1_tops_1(X22,X23) = k3_subset_1(u1_struct_0(X22),k2_pre_topc(X22,k3_subset_1(u1_struct_0(X22),X23))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tops_1])])])).

cnf(c_0_24,plain,
    ( k2_pre_topc(X2,X1) = k2_struct_0(X2)
    | ~ v1_tops_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_25,plain,
    ( m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_26,plain,
    ( v1_tops_1(k3_subset_1(u1_struct_0(X2),X1),X2)
    | ~ v2_tops_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_28,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_29,plain,
    ( k4_subset_1(X2,X1,k3_subset_1(X2,X1)) = k2_subset_1(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_30,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_31,plain,(
    ! [X13] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X13)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

cnf(c_0_32,plain,
    ( k2_subset_1(X1) = k3_subset_1(X1,k1_subset_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_33,plain,
    ( k1_subset_1(X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_34,plain,(
    ! [X19] :
      ( ~ l1_pre_topc(X19)
      | l1_struct_0(X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_35,plain,
    ( k1_tops_1(X1,X2) = k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_36,plain,
    ( k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2)) = k2_struct_0(X1)
    | ~ v1_tops_1(k3_subset_1(u1_struct_0(X1),X2),X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_37,negated_conjecture,
    ( v1_tops_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),esk1_0)
    | ~ v2_tops_1(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28])])).

fof(c_0_38,plain,(
    ! [X20,X21] :
      ( ~ l1_struct_0(X20)
      | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))
      | k4_subset_1(u1_struct_0(X20),X21,k3_subset_1(u1_struct_0(X20),X21)) = k2_struct_0(X20) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t18_pre_topc])])])).

cnf(c_0_39,plain,
    ( k4_subset_1(X2,X1,k3_subset_1(X2,X1)) = X2
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_40,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_41,plain,
    ( X1 = k3_subset_1(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_30]),c_0_33])).

fof(c_0_42,plain,(
    ! [X8,X9] :
      ( ~ m1_subset_1(X9,k1_zfmisc_1(X8))
      | k3_subset_1(X8,k3_subset_1(X8,X9)) = X9 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).

cnf(c_0_43,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_44,negated_conjecture,
    ( k3_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0))) = k1_tops_1(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_27]),c_0_28])])).

cnf(c_0_45,negated_conjecture,
    ( k2_pre_topc(esk1_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0)) = k2_struct_0(esk1_0)
    | ~ v2_tops_1(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_28]),c_0_27])])).

cnf(c_0_46,plain,
    ( k4_subset_1(u1_struct_0(X1),X2,k3_subset_1(u1_struct_0(X1),X2)) = k2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_47,plain,
    ( k4_subset_1(X1,k1_xboole_0,X1) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_41])).

cnf(c_0_48,plain,
    ( k3_subset_1(X2,k3_subset_1(X2,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

fof(c_0_49,plain,(
    ! [X17,X18] :
      ( ~ l1_pre_topc(X17)
      | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))
      | m1_subset_1(k2_pre_topc(X17,X18),k1_zfmisc_1(u1_struct_0(X17))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).

cnf(c_0_50,negated_conjecture,
    ( k4_subset_1(u1_struct_0(esk1_0),esk2_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0)) = u1_struct_0(esk1_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_27])).

cnf(c_0_51,negated_conjecture,
    ( l1_struct_0(esk1_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_28])).

cnf(c_0_52,negated_conjecture,
    ( k3_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0)) = k1_tops_1(esk1_0,esk2_0)
    | ~ v2_tops_1(esk2_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_53,plain,
    ( u1_struct_0(X1) = k2_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_40]),c_0_41]),c_0_47])).

cnf(c_0_54,plain,
    ( k3_subset_1(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_40]),c_0_41])).

cnf(c_0_55,negated_conjecture,
    ( v2_tops_1(esk2_0,esk1_0)
    | k1_tops_1(esk1_0,esk2_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_56,plain,
    ( m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_57,plain,
    ( v1_tops_1(X2,X1)
    | k2_pre_topc(X1,X2) != k2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_58,plain,
    ( v2_tops_1(X2,X1)
    | ~ v1_tops_1(k3_subset_1(u1_struct_0(X1),X2),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_59,negated_conjecture,
    ( u1_struct_0(esk1_0) = k2_struct_0(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_27]),c_0_50]),c_0_51])])).

cnf(c_0_60,negated_conjecture,
    ( ~ v2_tops_1(esk2_0,esk1_0)
    | k1_tops_1(esk1_0,esk2_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_61,negated_conjecture,
    ( k1_tops_1(esk1_0,esk2_0) = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_54]),c_0_51])]),c_0_55])).

cnf(c_0_62,plain,
    ( k3_subset_1(u1_struct_0(X1),k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2))) = k2_pre_topc(X1,X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_48,c_0_56])).

cnf(c_0_63,plain,
    ( v1_tops_1(k3_subset_1(u1_struct_0(X1),X2),X1)
    | k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2)) != k2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_57,c_0_25])).

cnf(c_0_64,negated_conjecture,
    ( v2_tops_1(X1,esk1_0)
    | ~ v1_tops_1(k3_subset_1(k2_struct_0(esk1_0),X1),esk1_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_28])])).

cnf(c_0_65,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(k2_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_53]),c_0_51])])).

cnf(c_0_66,negated_conjecture,
    ( ~ v2_tops_1(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_60,c_0_61])])).

cnf(c_0_67,plain,
    ( k3_subset_1(k2_struct_0(X1),k3_subset_1(k2_struct_0(X1),k2_pre_topc(X1,X2))) = k2_pre_topc(X1,X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_53]),c_0_43])).

cnf(c_0_68,negated_conjecture,
    ( k3_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_44,c_0_61])).

cnf(c_0_69,plain,
    ( v1_tops_1(k3_subset_1(k2_struct_0(X1),X2),X1)
    | k2_pre_topc(X1,k3_subset_1(k2_struct_0(X1),X2)) != k2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_53]),c_0_43])).

cnf(c_0_70,negated_conjecture,
    ( ~ v1_tops_1(k3_subset_1(k2_struct_0(esk1_0),esk2_0),esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_66])).

cnf(c_0_71,plain,
    ( k3_subset_1(k2_struct_0(X1),k3_subset_1(k2_struct_0(X1),k2_pre_topc(X1,k3_subset_1(k2_struct_0(X1),X2)))) = k2_pre_topc(X1,k3_subset_1(k2_struct_0(X1),X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_67,c_0_25])).

cnf(c_0_72,negated_conjecture,
    ( k3_subset_1(k2_struct_0(esk1_0),k2_pre_topc(esk1_0,k3_subset_1(k2_struct_0(esk1_0),esk2_0))) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_53]),c_0_51])])).

cnf(c_0_73,negated_conjecture,
    ( k2_pre_topc(esk1_0,k3_subset_1(k2_struct_0(esk1_0),esk2_0)) != k2_struct_0(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_65]),c_0_28])]),c_0_70])).

cnf(c_0_74,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_65]),c_0_72]),c_0_41]),c_0_28])]),c_0_73]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:26:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.50/0.72  # AutoSched0-Mode selected heuristic G_E___107_C36_F1_PI_AE_Q4_CS_SP_PS_S0Y
% 0.50/0.72  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.50/0.72  #
% 0.50/0.72  # Preprocessing time       : 0.028 s
% 0.50/0.72  # Presaturation interreduction done
% 0.50/0.72  
% 0.50/0.72  # Proof found!
% 0.50/0.72  # SZS status Theorem
% 0.50/0.72  # SZS output start CNFRefutation
% 0.50/0.72  fof(t84_tops_1, conjecture, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v2_tops_1(X2,X1)<=>k1_tops_1(X1,X2)=k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_tops_1)).
% 0.50/0.72  fof(d3_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v1_tops_1(X2,X1)<=>k2_pre_topc(X1,X2)=k2_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tops_1)).
% 0.50/0.72  fof(dt_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 0.50/0.72  fof(d4_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v2_tops_1(X2,X1)<=>v1_tops_1(k3_subset_1(u1_struct_0(X1),X2),X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tops_1)).
% 0.50/0.72  fof(t25_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k4_subset_1(X1,X2,k3_subset_1(X1,X2))=k2_subset_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_subset_1)).
% 0.50/0.72  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 0.50/0.72  fof(t22_subset_1, axiom, ![X1]:k2_subset_1(X1)=k3_subset_1(X1,k1_subset_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_subset_1)).
% 0.50/0.72  fof(d3_subset_1, axiom, ![X1]:k1_subset_1(X1)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 0.50/0.72  fof(d1_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k1_tops_1(X1,X2)=k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tops_1)).
% 0.50/0.72  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 0.50/0.72  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.50/0.72  fof(t18_pre_topc, axiom, ![X1]:(l1_struct_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k4_subset_1(u1_struct_0(X1),X2,k3_subset_1(u1_struct_0(X1),X2))=k2_struct_0(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_pre_topc)).
% 0.50/0.72  fof(involutiveness_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,k3_subset_1(X1,X2))=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 0.50/0.72  fof(dt_k2_pre_topc, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 0.50/0.72  fof(c_0_14, negated_conjecture, ~(![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v2_tops_1(X2,X1)<=>k1_tops_1(X1,X2)=k1_xboole_0)))), inference(assume_negation,[status(cth)],[t84_tops_1])).
% 0.50/0.72  fof(c_0_15, plain, ![X24, X25]:((~v1_tops_1(X25,X24)|k2_pre_topc(X24,X25)=k2_struct_0(X24)|~m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))|~l1_pre_topc(X24))&(k2_pre_topc(X24,X25)!=k2_struct_0(X24)|v1_tops_1(X25,X24)|~m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))|~l1_pre_topc(X24))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tops_1])])])])).
% 0.50/0.72  fof(c_0_16, plain, ![X6, X7]:(~m1_subset_1(X7,k1_zfmisc_1(X6))|m1_subset_1(k3_subset_1(X6,X7),k1_zfmisc_1(X6))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).
% 0.50/0.72  fof(c_0_17, plain, ![X26, X27]:((~v2_tops_1(X27,X26)|v1_tops_1(k3_subset_1(u1_struct_0(X26),X27),X26)|~m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))|~l1_pre_topc(X26))&(~v1_tops_1(k3_subset_1(u1_struct_0(X26),X27),X26)|v2_tops_1(X27,X26)|~m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))|~l1_pre_topc(X26))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tops_1])])])])).
% 0.50/0.72  fof(c_0_18, negated_conjecture, (l1_pre_topc(esk1_0)&(m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&((~v2_tops_1(esk2_0,esk1_0)|k1_tops_1(esk1_0,esk2_0)!=k1_xboole_0)&(v2_tops_1(esk2_0,esk1_0)|k1_tops_1(esk1_0,esk2_0)=k1_xboole_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).
% 0.50/0.72  fof(c_0_19, plain, ![X11, X12]:(~m1_subset_1(X12,k1_zfmisc_1(X11))|k4_subset_1(X11,X12,k3_subset_1(X11,X12))=k2_subset_1(X11)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_subset_1])])).
% 0.50/0.72  fof(c_0_20, plain, ![X5]:k2_subset_1(X5)=X5, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 0.50/0.72  fof(c_0_21, plain, ![X10]:k2_subset_1(X10)=k3_subset_1(X10,k1_subset_1(X10)), inference(variable_rename,[status(thm)],[t22_subset_1])).
% 0.50/0.72  fof(c_0_22, plain, ![X4]:k1_subset_1(X4)=k1_xboole_0, inference(variable_rename,[status(thm)],[d3_subset_1])).
% 0.50/0.72  fof(c_0_23, plain, ![X22, X23]:(~l1_pre_topc(X22)|(~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))|k1_tops_1(X22,X23)=k3_subset_1(u1_struct_0(X22),k2_pre_topc(X22,k3_subset_1(u1_struct_0(X22),X23))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tops_1])])])).
% 0.50/0.72  cnf(c_0_24, plain, (k2_pre_topc(X2,X1)=k2_struct_0(X2)|~v1_tops_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.50/0.72  cnf(c_0_25, plain, (m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.50/0.72  cnf(c_0_26, plain, (v1_tops_1(k3_subset_1(u1_struct_0(X2),X1),X2)|~v2_tops_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.50/0.72  cnf(c_0_27, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.50/0.72  cnf(c_0_28, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.50/0.72  cnf(c_0_29, plain, (k4_subset_1(X2,X1,k3_subset_1(X2,X1))=k2_subset_1(X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.50/0.72  cnf(c_0_30, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.50/0.72  fof(c_0_31, plain, ![X13]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X13)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.50/0.72  cnf(c_0_32, plain, (k2_subset_1(X1)=k3_subset_1(X1,k1_subset_1(X1))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.50/0.72  cnf(c_0_33, plain, (k1_subset_1(X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.50/0.72  fof(c_0_34, plain, ![X19]:(~l1_pre_topc(X19)|l1_struct_0(X19)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.50/0.72  cnf(c_0_35, plain, (k1_tops_1(X1,X2)=k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.50/0.72  cnf(c_0_36, plain, (k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2))=k2_struct_0(X1)|~v1_tops_1(k3_subset_1(u1_struct_0(X1),X2),X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.50/0.72  cnf(c_0_37, negated_conjecture, (v1_tops_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),esk1_0)|~v2_tops_1(esk2_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28])])).
% 0.50/0.72  fof(c_0_38, plain, ![X20, X21]:(~l1_struct_0(X20)|(~m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))|k4_subset_1(u1_struct_0(X20),X21,k3_subset_1(u1_struct_0(X20),X21))=k2_struct_0(X20))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t18_pre_topc])])])).
% 0.50/0.72  cnf(c_0_39, plain, (k4_subset_1(X2,X1,k3_subset_1(X2,X1))=X2|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_29, c_0_30])).
% 0.50/0.72  cnf(c_0_40, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.50/0.72  cnf(c_0_41, plain, (X1=k3_subset_1(X1,k1_xboole_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_30]), c_0_33])).
% 0.50/0.72  fof(c_0_42, plain, ![X8, X9]:(~m1_subset_1(X9,k1_zfmisc_1(X8))|k3_subset_1(X8,k3_subset_1(X8,X9))=X9), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).
% 0.50/0.72  cnf(c_0_43, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.50/0.72  cnf(c_0_44, negated_conjecture, (k3_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0)))=k1_tops_1(esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_27]), c_0_28])])).
% 0.50/0.72  cnf(c_0_45, negated_conjecture, (k2_pre_topc(esk1_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0))=k2_struct_0(esk1_0)|~v2_tops_1(esk2_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_28]), c_0_27])])).
% 0.50/0.72  cnf(c_0_46, plain, (k4_subset_1(u1_struct_0(X1),X2,k3_subset_1(u1_struct_0(X1),X2))=k2_struct_0(X1)|~l1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.50/0.72  cnf(c_0_47, plain, (k4_subset_1(X1,k1_xboole_0,X1)=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_41])).
% 0.50/0.72  cnf(c_0_48, plain, (k3_subset_1(X2,k3_subset_1(X2,X1))=X1|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.50/0.72  fof(c_0_49, plain, ![X17, X18]:(~l1_pre_topc(X17)|~m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))|m1_subset_1(k2_pre_topc(X17,X18),k1_zfmisc_1(u1_struct_0(X17)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).
% 0.50/0.72  cnf(c_0_50, negated_conjecture, (k4_subset_1(u1_struct_0(esk1_0),esk2_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0))=u1_struct_0(esk1_0)), inference(spm,[status(thm)],[c_0_39, c_0_27])).
% 0.50/0.72  cnf(c_0_51, negated_conjecture, (l1_struct_0(esk1_0)), inference(spm,[status(thm)],[c_0_43, c_0_28])).
% 0.50/0.72  cnf(c_0_52, negated_conjecture, (k3_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0))=k1_tops_1(esk1_0,esk2_0)|~v2_tops_1(esk2_0,esk1_0)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.50/0.72  cnf(c_0_53, plain, (u1_struct_0(X1)=k2_struct_0(X1)|~l1_struct_0(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_40]), c_0_41]), c_0_47])).
% 0.50/0.72  cnf(c_0_54, plain, (k3_subset_1(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_40]), c_0_41])).
% 0.50/0.72  cnf(c_0_55, negated_conjecture, (v2_tops_1(esk2_0,esk1_0)|k1_tops_1(esk1_0,esk2_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.50/0.72  cnf(c_0_56, plain, (m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.50/0.72  cnf(c_0_57, plain, (v1_tops_1(X2,X1)|k2_pre_topc(X1,X2)!=k2_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.50/0.72  cnf(c_0_58, plain, (v2_tops_1(X2,X1)|~v1_tops_1(k3_subset_1(u1_struct_0(X1),X2),X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.50/0.72  cnf(c_0_59, negated_conjecture, (u1_struct_0(esk1_0)=k2_struct_0(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_27]), c_0_50]), c_0_51])])).
% 0.50/0.72  cnf(c_0_60, negated_conjecture, (~v2_tops_1(esk2_0,esk1_0)|k1_tops_1(esk1_0,esk2_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.50/0.72  cnf(c_0_61, negated_conjecture, (k1_tops_1(esk1_0,esk2_0)=k1_xboole_0), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_54]), c_0_51])]), c_0_55])).
% 0.50/0.72  cnf(c_0_62, plain, (k3_subset_1(u1_struct_0(X1),k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2)))=k2_pre_topc(X1,X2)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_48, c_0_56])).
% 0.50/0.72  cnf(c_0_63, plain, (v1_tops_1(k3_subset_1(u1_struct_0(X1),X2),X1)|k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2))!=k2_struct_0(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_57, c_0_25])).
% 0.50/0.72  cnf(c_0_64, negated_conjecture, (v2_tops_1(X1,esk1_0)|~v1_tops_1(k3_subset_1(k2_struct_0(esk1_0),X1),esk1_0)|~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_28])])).
% 0.50/0.72  cnf(c_0_65, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(k2_struct_0(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_53]), c_0_51])])).
% 0.50/0.72  cnf(c_0_66, negated_conjecture, (~v2_tops_1(esk2_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_60, c_0_61])])).
% 0.50/0.72  cnf(c_0_67, plain, (k3_subset_1(k2_struct_0(X1),k3_subset_1(k2_struct_0(X1),k2_pre_topc(X1,X2)))=k2_pre_topc(X1,X2)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_53]), c_0_43])).
% 0.50/0.72  cnf(c_0_68, negated_conjecture, (k3_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0)))=k1_xboole_0), inference(rw,[status(thm)],[c_0_44, c_0_61])).
% 0.50/0.72  cnf(c_0_69, plain, (v1_tops_1(k3_subset_1(k2_struct_0(X1),X2),X1)|k2_pre_topc(X1,k3_subset_1(k2_struct_0(X1),X2))!=k2_struct_0(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_53]), c_0_43])).
% 0.50/0.72  cnf(c_0_70, negated_conjecture, (~v1_tops_1(k3_subset_1(k2_struct_0(esk1_0),esk2_0),esk1_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_66])).
% 0.50/0.72  cnf(c_0_71, plain, (k3_subset_1(k2_struct_0(X1),k3_subset_1(k2_struct_0(X1),k2_pre_topc(X1,k3_subset_1(k2_struct_0(X1),X2))))=k2_pre_topc(X1,k3_subset_1(k2_struct_0(X1),X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(X1)))), inference(spm,[status(thm)],[c_0_67, c_0_25])).
% 0.50/0.72  cnf(c_0_72, negated_conjecture, (k3_subset_1(k2_struct_0(esk1_0),k2_pre_topc(esk1_0,k3_subset_1(k2_struct_0(esk1_0),esk2_0)))=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_53]), c_0_51])])).
% 0.50/0.72  cnf(c_0_73, negated_conjecture, (k2_pre_topc(esk1_0,k3_subset_1(k2_struct_0(esk1_0),esk2_0))!=k2_struct_0(esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_65]), c_0_28])]), c_0_70])).
% 0.50/0.72  cnf(c_0_74, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_65]), c_0_72]), c_0_41]), c_0_28])]), c_0_73]), ['proof']).
% 0.50/0.72  # SZS output end CNFRefutation
% 0.50/0.72  # Proof object total steps             : 75
% 0.50/0.72  # Proof object clause steps            : 46
% 0.50/0.72  # Proof object formula steps           : 29
% 0.50/0.72  # Proof object conjectures             : 23
% 0.50/0.72  # Proof object clause conjectures      : 20
% 0.50/0.72  # Proof object formula conjectures     : 3
% 0.50/0.72  # Proof object initial clauses used    : 19
% 0.50/0.72  # Proof object initial formulas used   : 14
% 0.50/0.72  # Proof object generating inferences   : 23
% 0.50/0.72  # Proof object simplifying inferences  : 41
% 0.50/0.72  # Training examples: 0 positive, 0 negative
% 0.50/0.72  # Parsed axioms                        : 15
% 0.50/0.72  # Removed by relevancy pruning/SinE    : 0
% 0.50/0.72  # Initial clauses                      : 20
% 0.50/0.72  # Removed in clause preprocessing      : 2
% 0.50/0.72  # Initial clauses in saturation        : 18
% 0.50/0.72  # Processed clauses                    : 3834
% 0.50/0.72  # ...of these trivial                  : 91
% 0.50/0.72  # ...subsumed                          : 2557
% 0.50/0.72  # ...remaining for further processing  : 1186
% 0.50/0.72  # Other redundant clauses eliminated   : 0
% 0.50/0.72  # Clauses deleted for lack of memory   : 0
% 0.50/0.72  # Backward-subsumed                    : 76
% 0.50/0.72  # Backward-rewritten                   : 28
% 0.50/0.72  # Generated clauses                    : 23385
% 0.50/0.72  # ...of the previous two non-trivial   : 20419
% 0.50/0.72  # Contextual simplify-reflections      : 106
% 0.50/0.72  # Paramodulations                      : 23385
% 0.50/0.72  # Factorizations                       : 0
% 0.50/0.72  # Equation resolutions                 : 0
% 0.50/0.72  # Propositional unsat checks           : 0
% 0.50/0.72  #    Propositional check models        : 0
% 0.50/0.72  #    Propositional check unsatisfiable : 0
% 0.50/0.72  #    Propositional clauses             : 0
% 0.50/0.72  #    Propositional clauses after purity: 0
% 0.50/0.72  #    Propositional unsat core size     : 0
% 0.50/0.72  #    Propositional preprocessing time  : 0.000
% 0.50/0.72  #    Propositional encoding time       : 0.000
% 0.50/0.72  #    Propositional solver time         : 0.000
% 0.50/0.72  #    Success case prop preproc time    : 0.000
% 0.50/0.72  #    Success case prop encoding time   : 0.000
% 0.50/0.72  #    Success case prop solver time     : 0.000
% 0.50/0.72  # Current number of processed clauses  : 1064
% 0.50/0.72  #    Positive orientable unit clauses  : 34
% 0.50/0.72  #    Positive unorientable unit clauses: 0
% 0.50/0.72  #    Negative unit clauses             : 4
% 0.50/0.72  #    Non-unit-clauses                  : 1026
% 0.50/0.72  # Current number of unprocessed clauses: 16331
% 0.50/0.72  # ...number of literals in the above   : 68896
% 0.50/0.72  # Current number of archived formulas  : 0
% 0.50/0.72  # Current number of archived clauses   : 124
% 0.50/0.72  # Clause-clause subsumption calls (NU) : 120030
% 0.50/0.72  # Rec. Clause-clause subsumption calls : 63273
% 0.50/0.72  # Non-unit clause-clause subsumptions  : 2685
% 0.50/0.72  # Unit Clause-clause subsumption calls : 205
% 0.50/0.72  # Rewrite failures with RHS unbound    : 0
% 0.50/0.72  # BW rewrite match attempts            : 58
% 0.50/0.72  # BW rewrite match successes           : 16
% 0.50/0.72  # Condensation attempts                : 0
% 0.50/0.72  # Condensation successes               : 0
% 0.50/0.72  # Termbank termtop insertions          : 547315
% 0.50/0.72  
% 0.50/0.72  # -------------------------------------------------
% 0.50/0.72  # User time                : 0.369 s
% 0.50/0.72  # System time              : 0.012 s
% 0.50/0.72  # Total time               : 0.381 s
% 0.50/0.72  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
