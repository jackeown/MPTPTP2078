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
% DateTime   : Thu Dec  3 11:12:27 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 401 expanded)
%              Number of clauses        :   57 ( 160 expanded)
%              Number of leaves         :   18 ( 102 expanded)
%              Depth                    :   12
%              Number of atoms          :  244 (1341 expanded)
%              Number of equality atoms :   47 ( 237 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :    9 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t97_tops_1,conjecture,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( ( v3_pre_topc(X2,X1)
              & v3_tops_1(X2,X1) )
           => X2 = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_tops_1)).

fof(t92_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_tops_1(X2,X1)
           => v2_tops_1(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_tops_1)).

fof(t84_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v2_tops_1(X2,X1)
          <=> k1_tops_1(X1,X2) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(dt_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(d4_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v2_tops_1(X2,X1)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(X1),X2),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_1)).

fof(involutiveness_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,k3_subset_1(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(projectivity_k1_tops_1,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => k1_tops_1(X1,k1_tops_1(X1,X2)) = k1_tops_1(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',projectivity_k1_tops_1)).

fof(t39_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ( r1_tarski(k3_subset_1(X1,X2),X2)
      <=> X2 = k2_subset_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(d3_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v1_tops_1(X2,X1)
          <=> k2_pre_topc(X1,X2) = k2_struct_0(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tops_1)).

fof(t29_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v4_pre_topc(X2,X1)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X1),X2),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tops_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

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

fof(dt_k2_subset_1,axiom,(
    ! [X1] : m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(fc9_tops_1,axiom,(
    ! [X1,X2] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => v3_pre_topc(k1_tops_1(X1,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

fof(c_0_18,negated_conjecture,(
    ~ ! [X1] :
        ( ( v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( ( v3_pre_topc(X2,X1)
                & v3_tops_1(X2,X1) )
             => X2 = k1_xboole_0 ) ) ) ),
    inference(assume_negation,[status(cth)],[t97_tops_1])).

fof(c_0_19,plain,(
    ! [X40,X41] :
      ( ~ l1_pre_topc(X40)
      | ~ m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(X40)))
      | ~ v3_tops_1(X41,X40)
      | v2_tops_1(X41,X40) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t92_tops_1])])])).

fof(c_0_20,negated_conjecture,
    ( v2_pre_topc(esk3_0)
    & l1_pre_topc(esk3_0)
    & m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))
    & v3_pre_topc(esk4_0,esk3_0)
    & v3_tops_1(esk4_0,esk3_0)
    & esk4_0 != k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).

fof(c_0_21,plain,(
    ! [X38,X39] :
      ( ( ~ v2_tops_1(X39,X38)
        | k1_tops_1(X38,X39) = k1_xboole_0
        | ~ m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(X38)))
        | ~ l1_pre_topc(X38) )
      & ( k1_tops_1(X38,X39) != k1_xboole_0
        | v2_tops_1(X39,X38)
        | ~ m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(X38)))
        | ~ l1_pre_topc(X38) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t84_tops_1])])])])).

cnf(c_0_22,plain,
    ( v2_tops_1(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_tops_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_23,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_24,negated_conjecture,
    ( v3_tops_1(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_25,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_26,plain,(
    ! [X4,X5,X6] :
      ( ( ~ v1_xboole_0(X4)
        | ~ r2_hidden(X5,X4) )
      & ( r2_hidden(esk1_1(X6),X6)
        | v1_xboole_0(X6) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_27,plain,(
    ! [X8,X9,X10,X11,X12] :
      ( ( ~ r1_tarski(X8,X9)
        | ~ r2_hidden(X10,X8)
        | r2_hidden(X10,X9) )
      & ( r2_hidden(esk2_2(X11,X12),X11)
        | r1_tarski(X11,X12) )
      & ( ~ r2_hidden(esk2_2(X11,X12),X12)
        | r1_tarski(X11,X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_28,plain,(
    ! [X16,X17] :
      ( ~ m1_subset_1(X17,k1_zfmisc_1(X16))
      | m1_subset_1(k3_subset_1(X16,X17),k1_zfmisc_1(X16)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).

fof(c_0_29,plain,(
    ! [X30,X31] :
      ( ( ~ v2_tops_1(X31,X30)
        | v1_tops_1(k3_subset_1(u1_struct_0(X30),X31),X30)
        | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))
        | ~ l1_pre_topc(X30) )
      & ( ~ v1_tops_1(k3_subset_1(u1_struct_0(X30),X31),X30)
        | v2_tops_1(X31,X30)
        | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))
        | ~ l1_pre_topc(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tops_1])])])])).

fof(c_0_30,plain,(
    ! [X18,X19] :
      ( ~ m1_subset_1(X19,k1_zfmisc_1(X18))
      | k3_subset_1(X18,k3_subset_1(X18,X19)) = X19 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).

fof(c_0_31,plain,(
    ! [X34,X35] :
      ( ~ l1_pre_topc(X34)
      | ~ m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X34)))
      | k1_tops_1(X34,k1_tops_1(X34,X35)) = k1_tops_1(X34,X35) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[projectivity_k1_tops_1])])).

cnf(c_0_32,plain,
    ( k1_tops_1(X2,X1) = k1_xboole_0
    | ~ v2_tops_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_33,negated_conjecture,
    ( v2_tops_1(esk4_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24]),c_0_25])])).

fof(c_0_34,plain,(
    ! [X20,X21] :
      ( ( ~ r1_tarski(k3_subset_1(X20,X21),X21)
        | X21 = k2_subset_1(X20)
        | ~ m1_subset_1(X21,k1_zfmisc_1(X20)) )
      & ( X21 != k2_subset_1(X20)
        | r1_tarski(k3_subset_1(X20,X21),X21)
        | ~ m1_subset_1(X21,k1_zfmisc_1(X20)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t39_subset_1])])])).

fof(c_0_35,plain,(
    ! [X14] : k2_subset_1(X14) = X14 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

fof(c_0_36,plain,(
    ! [X22] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X22)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

cnf(c_0_37,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_38,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_39,plain,(
    ! [X28,X29] :
      ( ( ~ v1_tops_1(X29,X28)
        | k2_pre_topc(X28,X29) = k2_struct_0(X28)
        | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))
        | ~ l1_pre_topc(X28) )
      & ( k2_pre_topc(X28,X29) != k2_struct_0(X28)
        | v1_tops_1(X29,X28)
        | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))
        | ~ l1_pre_topc(X28) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tops_1])])])])).

cnf(c_0_40,plain,
    ( m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_41,plain,
    ( v1_tops_1(k3_subset_1(u1_struct_0(X2),X1),X2)
    | ~ v2_tops_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_42,plain,(
    ! [X36,X37] :
      ( ( ~ v4_pre_topc(X37,X36)
        | v3_pre_topc(k3_subset_1(u1_struct_0(X36),X37),X36)
        | ~ m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X36)))
        | ~ l1_pre_topc(X36) )
      & ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X36),X37),X36)
        | v4_pre_topc(X37,X36)
        | ~ m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X36)))
        | ~ l1_pre_topc(X36) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_tops_1])])])])).

cnf(c_0_43,plain,
    ( k3_subset_1(X2,k3_subset_1(X2,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_44,plain,
    ( k1_tops_1(X1,k1_tops_1(X1,X2)) = k1_tops_1(X1,X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_45,negated_conjecture,
    ( k1_tops_1(esk3_0,esk4_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_23]),c_0_33]),c_0_25])])).

cnf(c_0_46,plain,
    ( X2 = k2_subset_1(X1)
    | ~ r1_tarski(k3_subset_1(X1,X2),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_47,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_48,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_49,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_50,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

fof(c_0_51,plain,(
    ! [X26,X27] :
      ( ( ~ v4_pre_topc(X27,X26)
        | k2_pre_topc(X26,X27) = X27
        | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))
        | ~ l1_pre_topc(X26) )
      & ( ~ v2_pre_topc(X26)
        | k2_pre_topc(X26,X27) != X27
        | v4_pre_topc(X27,X26)
        | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))
        | ~ l1_pre_topc(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t52_pre_topc])])])])).

cnf(c_0_52,plain,
    ( k2_pre_topc(X2,X1) = k2_struct_0(X2)
    | ~ v1_tops_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_53,negated_conjecture,
    ( m1_subset_1(k3_subset_1(u1_struct_0(esk3_0),esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_40,c_0_23])).

cnf(c_0_54,negated_conjecture,
    ( v1_tops_1(k3_subset_1(u1_struct_0(esk3_0),esk4_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_23]),c_0_33]),c_0_25])])).

cnf(c_0_55,plain,
    ( v4_pre_topc(X2,X1)
    | ~ v3_pre_topc(k3_subset_1(u1_struct_0(X1),X2),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_56,negated_conjecture,
    ( k3_subset_1(u1_struct_0(esk3_0),k3_subset_1(u1_struct_0(esk3_0),esk4_0)) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_43,c_0_23])).

cnf(c_0_57,negated_conjecture,
    ( v3_pre_topc(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_58,plain,(
    ! [X15] : m1_subset_1(k2_subset_1(X15),k1_zfmisc_1(X15)) ),
    inference(variable_rename,[status(thm)],[dt_k2_subset_1])).

cnf(c_0_59,plain,
    ( v2_tops_1(X2,X1)
    | k1_tops_1(X1,X2) != k1_xboole_0
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_60,negated_conjecture,
    ( k1_tops_1(esk3_0,k1_xboole_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_23]),c_0_45]),c_0_45]),c_0_25])])).

fof(c_0_61,plain,(
    ! [X32,X33] :
      ( ~ v2_pre_topc(X32)
      | ~ l1_pre_topc(X32)
      | ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))
      | v3_pre_topc(k1_tops_1(X32,X33),X32) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc9_tops_1])])).

cnf(c_0_62,plain,
    ( X1 = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_tarski(k3_subset_1(X1,X2),X2) ),
    inference(rw,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_63,plain,
    ( m1_subset_1(k3_subset_1(X1,k1_xboole_0),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_48])).

cnf(c_0_64,plain,
    ( k3_subset_1(X1,k3_subset_1(X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_43,c_0_48])).

cnf(c_0_65,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_66,plain,
    ( k2_pre_topc(X2,X1) = X1
    | ~ v4_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_67,negated_conjecture,
    ( k2_pre_topc(esk3_0,k3_subset_1(u1_struct_0(esk3_0),esk4_0)) = k2_struct_0(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_25])]),c_0_54])])).

cnf(c_0_68,negated_conjecture,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(esk3_0),esk4_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_53]),c_0_25])]),c_0_56]),c_0_57])])).

cnf(c_0_69,plain,
    ( m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_70,plain,
    ( v1_tops_1(k3_subset_1(u1_struct_0(X1),k1_xboole_0),X1)
    | ~ v2_tops_1(k1_xboole_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_48])).

cnf(c_0_71,negated_conjecture,
    ( v2_tops_1(k1_xboole_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_25]),c_0_48])])).

cnf(c_0_72,plain,
    ( v3_pre_topc(k1_tops_1(X1,X2),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_73,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_74,plain,
    ( k3_subset_1(X1,k1_xboole_0) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_64]),c_0_65])])).

cnf(c_0_75,negated_conjecture,
    ( k3_subset_1(u1_struct_0(esk3_0),esk4_0) = k2_struct_0(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_53]),c_0_25])]),c_0_67]),c_0_68])])).

cnf(c_0_76,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_69,c_0_47])).

cnf(c_0_77,negated_conjecture,
    ( v1_tops_1(k3_subset_1(u1_struct_0(esk3_0),k1_xboole_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_25])])).

cnf(c_0_78,negated_conjecture,
    ( v3_pre_topc(k1_xboole_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_23]),c_0_45]),c_0_73]),c_0_25])])).

cnf(c_0_79,plain,
    ( k3_subset_1(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_64,c_0_74])).

cnf(c_0_80,negated_conjecture,
    ( esk4_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_81,negated_conjecture,
    ( esk4_0 = k3_subset_1(u1_struct_0(esk3_0),k2_struct_0(esk3_0)) ),
    inference(rw,[status(thm)],[c_0_56,c_0_75])).

cnf(c_0_82,plain,
    ( k2_struct_0(X1) = k2_pre_topc(X1,u1_struct_0(X1))
    | ~ v1_tops_1(u1_struct_0(X1),X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_52,c_0_76])).

cnf(c_0_83,negated_conjecture,
    ( v1_tops_1(u1_struct_0(esk3_0),esk3_0) ),
    inference(rw,[status(thm)],[c_0_77,c_0_74])).

cnf(c_0_84,plain,
    ( v4_pre_topc(u1_struct_0(X1),X1)
    | ~ v3_pre_topc(k3_subset_1(u1_struct_0(X1),u1_struct_0(X1)),X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_55,c_0_76])).

cnf(c_0_85,negated_conjecture,
    ( v3_pre_topc(k3_subset_1(X1,X1),esk3_0) ),
    inference(spm,[status(thm)],[c_0_78,c_0_79])).

cnf(c_0_86,negated_conjecture,
    ( k3_subset_1(u1_struct_0(esk3_0),k2_struct_0(esk3_0)) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_80,c_0_81])).

cnf(c_0_87,negated_conjecture,
    ( k2_struct_0(esk3_0) = k2_pre_topc(esk3_0,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_25])])).

cnf(c_0_88,plain,
    ( k2_pre_topc(X1,u1_struct_0(X1)) = u1_struct_0(X1)
    | ~ v4_pre_topc(u1_struct_0(X1),X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_66,c_0_76])).

cnf(c_0_89,negated_conjecture,
    ( v4_pre_topc(u1_struct_0(esk3_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_85]),c_0_25])])).

cnf(c_0_90,negated_conjecture,
    ( k3_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,u1_struct_0(esk3_0))) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_86,c_0_87])).

cnf(c_0_91,negated_conjecture,
    ( k2_pre_topc(esk3_0,u1_struct_0(esk3_0)) = u1_struct_0(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_89]),c_0_25])])).

cnf(c_0_92,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_90,c_0_91]),c_0_79])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:34:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.38  # AutoSched0-Mode selected heuristic G_E___208_B07_F1_SE_CS_SP_PS_S2q
% 0.19/0.38  # and selection function SelectCQArNTNp.
% 0.19/0.38  #
% 0.19/0.38  # Preprocessing time       : 0.028 s
% 0.19/0.38  # Presaturation interreduction done
% 0.19/0.38  
% 0.19/0.38  # Proof found!
% 0.19/0.38  # SZS status Theorem
% 0.19/0.38  # SZS output start CNFRefutation
% 0.19/0.38  fof(t97_tops_1, conjecture, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>((v3_pre_topc(X2,X1)&v3_tops_1(X2,X1))=>X2=k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_tops_1)).
% 0.19/0.38  fof(t92_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_tops_1(X2,X1)=>v2_tops_1(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_tops_1)).
% 0.19/0.38  fof(t84_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v2_tops_1(X2,X1)<=>k1_tops_1(X1,X2)=k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_tops_1)).
% 0.19/0.38  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.19/0.38  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.19/0.38  fof(dt_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 0.19/0.38  fof(d4_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v2_tops_1(X2,X1)<=>v1_tops_1(k3_subset_1(u1_struct_0(X1),X2),X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tops_1)).
% 0.19/0.38  fof(involutiveness_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,k3_subset_1(X1,X2))=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 0.19/0.38  fof(projectivity_k1_tops_1, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>k1_tops_1(X1,k1_tops_1(X1,X2))=k1_tops_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', projectivity_k1_tops_1)).
% 0.19/0.38  fof(t39_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>(r1_tarski(k3_subset_1(X1,X2),X2)<=>X2=k2_subset_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_subset_1)).
% 0.19/0.38  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 0.19/0.38  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 0.19/0.38  fof(d3_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v1_tops_1(X2,X1)<=>k2_pre_topc(X1,X2)=k2_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tops_1)).
% 0.19/0.38  fof(t29_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v4_pre_topc(X2,X1)<=>v3_pre_topc(k3_subset_1(u1_struct_0(X1),X2),X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_tops_1)).
% 0.19/0.38  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.19/0.38  fof(t52_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>((v4_pre_topc(X2,X1)=>k2_pre_topc(X1,X2)=X2)&((v2_pre_topc(X1)&k2_pre_topc(X1,X2)=X2)=>v4_pre_topc(X2,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 0.19/0.38  fof(dt_k2_subset_1, axiom, ![X1]:m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 0.19/0.38  fof(fc9_tops_1, axiom, ![X1, X2]:(((v2_pre_topc(X1)&l1_pre_topc(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>v3_pre_topc(k1_tops_1(X1,X2),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_tops_1)).
% 0.19/0.38  fof(c_0_18, negated_conjecture, ~(![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>((v3_pre_topc(X2,X1)&v3_tops_1(X2,X1))=>X2=k1_xboole_0)))), inference(assume_negation,[status(cth)],[t97_tops_1])).
% 0.19/0.39  fof(c_0_19, plain, ![X40, X41]:(~l1_pre_topc(X40)|(~m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(X40)))|(~v3_tops_1(X41,X40)|v2_tops_1(X41,X40)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t92_tops_1])])])).
% 0.19/0.39  fof(c_0_20, negated_conjecture, ((v2_pre_topc(esk3_0)&l1_pre_topc(esk3_0))&(m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))&((v3_pre_topc(esk4_0,esk3_0)&v3_tops_1(esk4_0,esk3_0))&esk4_0!=k1_xboole_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).
% 0.19/0.39  fof(c_0_21, plain, ![X38, X39]:((~v2_tops_1(X39,X38)|k1_tops_1(X38,X39)=k1_xboole_0|~m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(X38)))|~l1_pre_topc(X38))&(k1_tops_1(X38,X39)!=k1_xboole_0|v2_tops_1(X39,X38)|~m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(X38)))|~l1_pre_topc(X38))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t84_tops_1])])])])).
% 0.19/0.39  cnf(c_0_22, plain, (v2_tops_1(X2,X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v3_tops_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.39  cnf(c_0_23, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.39  cnf(c_0_24, negated_conjecture, (v3_tops_1(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.39  cnf(c_0_25, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.39  fof(c_0_26, plain, ![X4, X5, X6]:((~v1_xboole_0(X4)|~r2_hidden(X5,X4))&(r2_hidden(esk1_1(X6),X6)|v1_xboole_0(X6))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.19/0.39  fof(c_0_27, plain, ![X8, X9, X10, X11, X12]:((~r1_tarski(X8,X9)|(~r2_hidden(X10,X8)|r2_hidden(X10,X9)))&((r2_hidden(esk2_2(X11,X12),X11)|r1_tarski(X11,X12))&(~r2_hidden(esk2_2(X11,X12),X12)|r1_tarski(X11,X12)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.19/0.39  fof(c_0_28, plain, ![X16, X17]:(~m1_subset_1(X17,k1_zfmisc_1(X16))|m1_subset_1(k3_subset_1(X16,X17),k1_zfmisc_1(X16))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).
% 0.19/0.39  fof(c_0_29, plain, ![X30, X31]:((~v2_tops_1(X31,X30)|v1_tops_1(k3_subset_1(u1_struct_0(X30),X31),X30)|~m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))|~l1_pre_topc(X30))&(~v1_tops_1(k3_subset_1(u1_struct_0(X30),X31),X30)|v2_tops_1(X31,X30)|~m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))|~l1_pre_topc(X30))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tops_1])])])])).
% 0.19/0.39  fof(c_0_30, plain, ![X18, X19]:(~m1_subset_1(X19,k1_zfmisc_1(X18))|k3_subset_1(X18,k3_subset_1(X18,X19))=X19), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).
% 0.19/0.39  fof(c_0_31, plain, ![X34, X35]:(~l1_pre_topc(X34)|~m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X34)))|k1_tops_1(X34,k1_tops_1(X34,X35))=k1_tops_1(X34,X35)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[projectivity_k1_tops_1])])).
% 0.19/0.39  cnf(c_0_32, plain, (k1_tops_1(X2,X1)=k1_xboole_0|~v2_tops_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.39  cnf(c_0_33, negated_conjecture, (v2_tops_1(esk4_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24]), c_0_25])])).
% 0.19/0.39  fof(c_0_34, plain, ![X20, X21]:((~r1_tarski(k3_subset_1(X20,X21),X21)|X21=k2_subset_1(X20)|~m1_subset_1(X21,k1_zfmisc_1(X20)))&(X21!=k2_subset_1(X20)|r1_tarski(k3_subset_1(X20,X21),X21)|~m1_subset_1(X21,k1_zfmisc_1(X20)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t39_subset_1])])])).
% 0.19/0.39  fof(c_0_35, plain, ![X14]:k2_subset_1(X14)=X14, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 0.19/0.39  fof(c_0_36, plain, ![X22]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X22)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.19/0.39  cnf(c_0_37, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.39  cnf(c_0_38, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.39  fof(c_0_39, plain, ![X28, X29]:((~v1_tops_1(X29,X28)|k2_pre_topc(X28,X29)=k2_struct_0(X28)|~m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))|~l1_pre_topc(X28))&(k2_pre_topc(X28,X29)!=k2_struct_0(X28)|v1_tops_1(X29,X28)|~m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))|~l1_pre_topc(X28))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tops_1])])])])).
% 0.19/0.39  cnf(c_0_40, plain, (m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.39  cnf(c_0_41, plain, (v1_tops_1(k3_subset_1(u1_struct_0(X2),X1),X2)|~v2_tops_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.39  fof(c_0_42, plain, ![X36, X37]:((~v4_pre_topc(X37,X36)|v3_pre_topc(k3_subset_1(u1_struct_0(X36),X37),X36)|~m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X36)))|~l1_pre_topc(X36))&(~v3_pre_topc(k3_subset_1(u1_struct_0(X36),X37),X36)|v4_pre_topc(X37,X36)|~m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X36)))|~l1_pre_topc(X36))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_tops_1])])])])).
% 0.19/0.39  cnf(c_0_43, plain, (k3_subset_1(X2,k3_subset_1(X2,X1))=X1|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.39  cnf(c_0_44, plain, (k1_tops_1(X1,k1_tops_1(X1,X2))=k1_tops_1(X1,X2)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.39  cnf(c_0_45, negated_conjecture, (k1_tops_1(esk3_0,esk4_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_23]), c_0_33]), c_0_25])])).
% 0.19/0.39  cnf(c_0_46, plain, (X2=k2_subset_1(X1)|~r1_tarski(k3_subset_1(X1,X2),X2)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.19/0.39  cnf(c_0_47, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.19/0.39  cnf(c_0_48, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.19/0.39  cnf(c_0_49, plain, (r1_tarski(X1,X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.19/0.39  cnf(c_0_50, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.19/0.39  fof(c_0_51, plain, ![X26, X27]:((~v4_pre_topc(X27,X26)|k2_pre_topc(X26,X27)=X27|~m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))|~l1_pre_topc(X26))&(~v2_pre_topc(X26)|k2_pre_topc(X26,X27)!=X27|v4_pre_topc(X27,X26)|~m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))|~l1_pre_topc(X26))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t52_pre_topc])])])])).
% 0.19/0.39  cnf(c_0_52, plain, (k2_pre_topc(X2,X1)=k2_struct_0(X2)|~v1_tops_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.19/0.39  cnf(c_0_53, negated_conjecture, (m1_subset_1(k3_subset_1(u1_struct_0(esk3_0),esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(spm,[status(thm)],[c_0_40, c_0_23])).
% 0.19/0.39  cnf(c_0_54, negated_conjecture, (v1_tops_1(k3_subset_1(u1_struct_0(esk3_0),esk4_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_23]), c_0_33]), c_0_25])])).
% 0.19/0.39  cnf(c_0_55, plain, (v4_pre_topc(X2,X1)|~v3_pre_topc(k3_subset_1(u1_struct_0(X1),X2),X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.19/0.39  cnf(c_0_56, negated_conjecture, (k3_subset_1(u1_struct_0(esk3_0),k3_subset_1(u1_struct_0(esk3_0),esk4_0))=esk4_0), inference(spm,[status(thm)],[c_0_43, c_0_23])).
% 0.19/0.39  cnf(c_0_57, negated_conjecture, (v3_pre_topc(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.39  fof(c_0_58, plain, ![X15]:m1_subset_1(k2_subset_1(X15),k1_zfmisc_1(X15)), inference(variable_rename,[status(thm)],[dt_k2_subset_1])).
% 0.19/0.39  cnf(c_0_59, plain, (v2_tops_1(X2,X1)|k1_tops_1(X1,X2)!=k1_xboole_0|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.39  cnf(c_0_60, negated_conjecture, (k1_tops_1(esk3_0,k1_xboole_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_23]), c_0_45]), c_0_45]), c_0_25])])).
% 0.19/0.39  fof(c_0_61, plain, ![X32, X33]:(~v2_pre_topc(X32)|~l1_pre_topc(X32)|~m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))|v3_pre_topc(k1_tops_1(X32,X33),X32)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc9_tops_1])])).
% 0.19/0.39  cnf(c_0_62, plain, (X1=X2|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_tarski(k3_subset_1(X1,X2),X2)), inference(rw,[status(thm)],[c_0_46, c_0_47])).
% 0.19/0.39  cnf(c_0_63, plain, (m1_subset_1(k3_subset_1(X1,k1_xboole_0),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_40, c_0_48])).
% 0.19/0.39  cnf(c_0_64, plain, (k3_subset_1(X1,k3_subset_1(X1,k1_xboole_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_43, c_0_48])).
% 0.19/0.39  cnf(c_0_65, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.19/0.39  cnf(c_0_66, plain, (k2_pre_topc(X2,X1)=X1|~v4_pre_topc(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.19/0.39  cnf(c_0_67, negated_conjecture, (k2_pre_topc(esk3_0,k3_subset_1(u1_struct_0(esk3_0),esk4_0))=k2_struct_0(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_25])]), c_0_54])])).
% 0.19/0.39  cnf(c_0_68, negated_conjecture, (v4_pre_topc(k3_subset_1(u1_struct_0(esk3_0),esk4_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_53]), c_0_25])]), c_0_56]), c_0_57])])).
% 0.19/0.39  cnf(c_0_69, plain, (m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.19/0.39  cnf(c_0_70, plain, (v1_tops_1(k3_subset_1(u1_struct_0(X1),k1_xboole_0),X1)|~v2_tops_1(k1_xboole_0,X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_41, c_0_48])).
% 0.19/0.39  cnf(c_0_71, negated_conjecture, (v2_tops_1(k1_xboole_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_25]), c_0_48])])).
% 0.19/0.39  cnf(c_0_72, plain, (v3_pre_topc(k1_tops_1(X1,X2),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.19/0.39  cnf(c_0_73, negated_conjecture, (v2_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.39  cnf(c_0_74, plain, (k3_subset_1(X1,k1_xboole_0)=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_64]), c_0_65])])).
% 0.19/0.39  cnf(c_0_75, negated_conjecture, (k3_subset_1(u1_struct_0(esk3_0),esk4_0)=k2_struct_0(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_53]), c_0_25])]), c_0_67]), c_0_68])])).
% 0.19/0.39  cnf(c_0_76, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_69, c_0_47])).
% 0.19/0.39  cnf(c_0_77, negated_conjecture, (v1_tops_1(k3_subset_1(u1_struct_0(esk3_0),k1_xboole_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_71]), c_0_25])])).
% 0.19/0.39  cnf(c_0_78, negated_conjecture, (v3_pre_topc(k1_xboole_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_23]), c_0_45]), c_0_73]), c_0_25])])).
% 0.19/0.39  cnf(c_0_79, plain, (k3_subset_1(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[c_0_64, c_0_74])).
% 0.19/0.39  cnf(c_0_80, negated_conjecture, (esk4_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.39  cnf(c_0_81, negated_conjecture, (esk4_0=k3_subset_1(u1_struct_0(esk3_0),k2_struct_0(esk3_0))), inference(rw,[status(thm)],[c_0_56, c_0_75])).
% 0.19/0.39  cnf(c_0_82, plain, (k2_struct_0(X1)=k2_pre_topc(X1,u1_struct_0(X1))|~v1_tops_1(u1_struct_0(X1),X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_52, c_0_76])).
% 0.19/0.39  cnf(c_0_83, negated_conjecture, (v1_tops_1(u1_struct_0(esk3_0),esk3_0)), inference(rw,[status(thm)],[c_0_77, c_0_74])).
% 0.19/0.39  cnf(c_0_84, plain, (v4_pre_topc(u1_struct_0(X1),X1)|~v3_pre_topc(k3_subset_1(u1_struct_0(X1),u1_struct_0(X1)),X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_55, c_0_76])).
% 0.19/0.39  cnf(c_0_85, negated_conjecture, (v3_pre_topc(k3_subset_1(X1,X1),esk3_0)), inference(spm,[status(thm)],[c_0_78, c_0_79])).
% 0.19/0.39  cnf(c_0_86, negated_conjecture, (k3_subset_1(u1_struct_0(esk3_0),k2_struct_0(esk3_0))!=k1_xboole_0), inference(rw,[status(thm)],[c_0_80, c_0_81])).
% 0.19/0.39  cnf(c_0_87, negated_conjecture, (k2_struct_0(esk3_0)=k2_pre_topc(esk3_0,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_83]), c_0_25])])).
% 0.19/0.39  cnf(c_0_88, plain, (k2_pre_topc(X1,u1_struct_0(X1))=u1_struct_0(X1)|~v4_pre_topc(u1_struct_0(X1),X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_66, c_0_76])).
% 0.19/0.39  cnf(c_0_89, negated_conjecture, (v4_pre_topc(u1_struct_0(esk3_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_85]), c_0_25])])).
% 0.19/0.39  cnf(c_0_90, negated_conjecture, (k3_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,u1_struct_0(esk3_0)))!=k1_xboole_0), inference(rw,[status(thm)],[c_0_86, c_0_87])).
% 0.19/0.39  cnf(c_0_91, negated_conjecture, (k2_pre_topc(esk3_0,u1_struct_0(esk3_0))=u1_struct_0(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_89]), c_0_25])])).
% 0.19/0.39  cnf(c_0_92, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_90, c_0_91]), c_0_79])]), ['proof']).
% 0.19/0.39  # SZS output end CNFRefutation
% 0.19/0.39  # Proof object total steps             : 93
% 0.19/0.39  # Proof object clause steps            : 57
% 0.19/0.39  # Proof object formula steps           : 36
% 0.19/0.39  # Proof object conjectures             : 30
% 0.19/0.39  # Proof object clause conjectures      : 27
% 0.19/0.39  # Proof object formula conjectures     : 3
% 0.19/0.39  # Proof object initial clauses used    : 24
% 0.19/0.39  # Proof object initial formulas used   : 18
% 0.19/0.39  # Proof object generating inferences   : 25
% 0.19/0.39  # Proof object simplifying inferences  : 55
% 0.19/0.39  # Training examples: 0 positive, 0 negative
% 0.19/0.39  # Parsed axioms                        : 19
% 0.19/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.39  # Initial clauses                      : 33
% 0.19/0.39  # Removed in clause preprocessing      : 1
% 0.19/0.39  # Initial clauses in saturation        : 32
% 0.19/0.39  # Processed clauses                    : 211
% 0.19/0.39  # ...of these trivial                  : 14
% 0.19/0.39  # ...subsumed                          : 17
% 0.19/0.39  # ...remaining for further processing  : 180
% 0.19/0.39  # Other redundant clauses eliminated   : 1
% 0.19/0.39  # Clauses deleted for lack of memory   : 0
% 0.19/0.39  # Backward-subsumed                    : 2
% 0.19/0.39  # Backward-rewritten                   : 75
% 0.19/0.39  # Generated clauses                    : 270
% 0.19/0.39  # ...of the previous two non-trivial   : 296
% 0.19/0.39  # Contextual simplify-reflections      : 0
% 0.19/0.39  # Paramodulations                      : 269
% 0.19/0.39  # Factorizations                       : 0
% 0.19/0.39  # Equation resolutions                 : 1
% 0.19/0.39  # Propositional unsat checks           : 0
% 0.19/0.39  #    Propositional check models        : 0
% 0.19/0.39  #    Propositional check unsatisfiable : 0
% 0.19/0.39  #    Propositional clauses             : 0
% 0.19/0.39  #    Propositional clauses after purity: 0
% 0.19/0.39  #    Propositional unsat core size     : 0
% 0.19/0.39  #    Propositional preprocessing time  : 0.000
% 0.19/0.39  #    Propositional encoding time       : 0.000
% 0.19/0.39  #    Propositional solver time         : 0.000
% 0.19/0.39  #    Success case prop preproc time    : 0.000
% 0.19/0.39  #    Success case prop encoding time   : 0.000
% 0.19/0.39  #    Success case prop solver time     : 0.000
% 0.19/0.39  # Current number of processed clauses  : 70
% 0.19/0.39  #    Positive orientable unit clauses  : 20
% 0.19/0.39  #    Positive unorientable unit clauses: 1
% 0.19/0.39  #    Negative unit clauses             : 0
% 0.19/0.39  #    Non-unit-clauses                  : 49
% 0.19/0.39  # Current number of unprocessed clauses: 138
% 0.19/0.39  # ...number of literals in the above   : 327
% 0.19/0.39  # Current number of archived formulas  : 0
% 0.19/0.39  # Current number of archived clauses   : 110
% 0.19/0.39  # Clause-clause subsumption calls (NU) : 556
% 0.19/0.39  # Rec. Clause-clause subsumption calls : 338
% 0.19/0.39  # Non-unit clause-clause subsumptions  : 19
% 0.19/0.39  # Unit Clause-clause subsumption calls : 44
% 0.19/0.39  # Rewrite failures with RHS unbound    : 3
% 0.19/0.39  # BW rewrite match attempts            : 39
% 0.19/0.39  # BW rewrite match successes           : 14
% 0.19/0.39  # Condensation attempts                : 0
% 0.19/0.39  # Condensation successes               : 0
% 0.19/0.39  # Termbank termtop insertions          : 6962
% 0.19/0.39  
% 0.19/0.39  # -------------------------------------------------
% 0.19/0.39  # User time                : 0.042 s
% 0.19/0.39  # System time              : 0.002 s
% 0.19/0.39  # Total time               : 0.044 s
% 0.19/0.39  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
