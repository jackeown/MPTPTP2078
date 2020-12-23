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
% DateTime   : Thu Dec  3 11:10:32 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 124 expanded)
%              Number of clauses        :   41 (  57 expanded)
%              Number of leaves         :   16 (  32 expanded)
%              Depth                    :   10
%              Number of atoms          :  190 ( 295 expanded)
%              Number of equality atoms :   21 (  42 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(dt_k2_subset_1,axiom,(
    ! [X1] : m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(dt_k2_pre_topc,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(dt_k2_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_struct_0)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(t48_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => r1_tarski(X2,k2_pre_topc(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_pre_topc)).

fof(t43_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => ( r1_xboole_0(X2,X3)
          <=> r1_tarski(X2,k3_subset_1(X1,X3)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_subset_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t3_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X2) ) )
      & ~ ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(X3,X2) )
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(fc3_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => v1_xboole_0(k1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_struct_0)).

fof(t27_tops_1,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => k2_pre_topc(X1,k2_struct_0(X1)) = k2_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_tops_1)).

fof(t27_pre_topc,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => k2_struct_0(X1) = k3_subset_1(u1_struct_0(X1),k1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_pre_topc)).

fof(c_0_16,plain,(
    ! [X22] : m1_subset_1(k2_subset_1(X22),k1_zfmisc_1(X22)) ),
    inference(variable_rename,[status(thm)],[dt_k2_subset_1])).

fof(c_0_17,plain,(
    ! [X21] : k2_subset_1(X21) = X21 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

fof(c_0_18,plain,(
    ! [X26,X27] :
      ( ( ~ m1_subset_1(X26,k1_zfmisc_1(X27))
        | r1_tarski(X26,X27) )
      & ( ~ r1_tarski(X26,X27)
        | m1_subset_1(X26,k1_zfmisc_1(X27)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_19,plain,(
    ! [X31,X32] :
      ( ~ l1_pre_topc(X31)
      | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))
      | m1_subset_1(k2_pre_topc(X31,X32),k1_zfmisc_1(u1_struct_0(X31))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).

fof(c_0_20,plain,(
    ! [X28,X29,X30] :
      ( ~ r2_hidden(X28,X29)
      | ~ m1_subset_1(X29,k1_zfmisc_1(X30))
      | ~ v1_xboole_0(X30) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

cnf(c_0_21,plain,
    ( m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,plain,
    ( m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_25,plain,(
    ! [X33] :
      ( ~ l1_struct_0(X33)
      | m1_subset_1(k2_struct_0(X33),k1_zfmisc_1(u1_struct_0(X33))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_struct_0])])).

fof(c_0_26,plain,(
    ! [X34] :
      ( ~ l1_pre_topc(X34)
      | l1_struct_0(X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

fof(c_0_27,plain,(
    ! [X37,X38] :
      ( ~ l1_pre_topc(X37)
      | ~ m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(X37)))
      | r1_tarski(X38,k2_pre_topc(X37,X38)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_pre_topc])])])).

fof(c_0_28,plain,(
    ! [X23,X24,X25] :
      ( ( ~ r1_xboole_0(X24,X25)
        | r1_tarski(X24,k3_subset_1(X23,X25))
        | ~ m1_subset_1(X25,k1_zfmisc_1(X23))
        | ~ m1_subset_1(X24,k1_zfmisc_1(X23)) )
      & ( ~ r1_tarski(X24,k3_subset_1(X23,X25))
        | r1_xboole_0(X24,X25)
        | ~ m1_subset_1(X25,k1_zfmisc_1(X23))
        | ~ m1_subset_1(X24,k1_zfmisc_1(X23)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_subset_1])])])])).

cnf(c_0_29,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_30,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_21,c_0_22])).

fof(c_0_31,plain,(
    ! [X4,X5,X6,X7,X8] :
      ( ( ~ r1_tarski(X4,X5)
        | ~ r2_hidden(X6,X4)
        | r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_2(X7,X8),X7)
        | r1_tarski(X7,X8) )
      & ( ~ r2_hidden(esk1_2(X7,X8),X8)
        | r1_tarski(X7,X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_32,plain,(
    ! [X10,X11,X13,X14,X15] :
      ( ( r2_hidden(esk2_2(X10,X11),X10)
        | r1_xboole_0(X10,X11) )
      & ( r2_hidden(esk2_2(X10,X11),X11)
        | r1_xboole_0(X10,X11) )
      & ( ~ r2_hidden(X15,X13)
        | ~ r2_hidden(X15,X14)
        | ~ r1_xboole_0(X13,X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

fof(c_0_33,plain,(
    ! [X16,X17] :
      ( ( r1_tarski(X16,X17)
        | X16 != X17 )
      & ( r1_tarski(X17,X16)
        | X16 != X17 )
      & ( ~ r1_tarski(X16,X17)
        | ~ r1_tarski(X17,X16)
        | X16 = X17 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_34,plain,
    ( r1_tarski(k2_pre_topc(X1,X2),u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_35,plain,
    ( m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_36,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_37,plain,(
    ! [X18,X19,X20] :
      ( ~ r1_tarski(X18,X19)
      | ~ r1_tarski(X19,X20)
      | r1_tarski(X18,X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

cnf(c_0_38,plain,
    ( r1_tarski(X2,k2_pre_topc(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_39,plain,
    ( r1_tarski(X1,k3_subset_1(X3,X2))
    | ~ r1_xboole_0(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_40,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_41,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_42,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_43,plain,(
    ! [X35] :
      ( ~ l1_struct_0(X35)
      | v1_xboole_0(k1_struct_0(X35)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc3_struct_0])])).

cnf(c_0_44,plain,
    ( r2_hidden(esk2_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_45,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => k2_pre_topc(X1,k2_struct_0(X1)) = k2_struct_0(X1) ) ),
    inference(assume_negation,[status(cth)],[t27_tops_1])).

cnf(c_0_46,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_47,plain,
    ( r1_tarski(k2_pre_topc(X1,k2_struct_0(X1)),u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36])).

cnf(c_0_48,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_49,plain,
    ( r1_tarski(k2_struct_0(X1),k2_pre_topc(X1,k2_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_35]),c_0_36])).

cnf(c_0_50,plain,
    ( r1_tarski(X1,k3_subset_1(X2,X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(X1,X3)
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

fof(c_0_51,plain,(
    ! [X36] :
      ( ~ l1_struct_0(X36)
      | k2_struct_0(X36) = k3_subset_1(u1_struct_0(X36),k1_struct_0(X36)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t27_pre_topc])])).

cnf(c_0_52,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_53,plain,
    ( v1_xboole_0(k1_struct_0(X1))
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_54,plain,
    ( r1_xboole_0(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_41,c_0_44])).

fof(c_0_55,negated_conjecture,
    ( l1_pre_topc(esk3_0)
    & k2_pre_topc(esk3_0,k2_struct_0(esk3_0)) != k2_struct_0(esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_45])])])).

cnf(c_0_56,plain,
    ( k2_pre_topc(X1,k2_struct_0(X1)) = u1_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ r1_tarski(u1_struct_0(X1),k2_pre_topc(X1,k2_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_57,plain,
    ( r1_tarski(X1,k2_pre_topc(X2,k2_struct_0(X2)))
    | ~ l1_pre_topc(X2)
    | ~ r1_tarski(X1,k2_struct_0(X2)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_58,plain,
    ( r1_tarski(k2_struct_0(X1),u1_struct_0(X1))
    | ~ l1_struct_0(X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_35])).

cnf(c_0_59,plain,
    ( r1_tarski(X1,k3_subset_1(X1,X2))
    | ~ r1_xboole_0(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_50,c_0_30])).

cnf(c_0_60,plain,
    ( k2_struct_0(X1) = k3_subset_1(u1_struct_0(X1),k1_struct_0(X1))
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_61,plain,
    ( r1_tarski(k1_struct_0(X1),X2)
    | ~ l1_struct_0(X1) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_62,plain,
    ( r1_xboole_0(X1,k1_struct_0(X2))
    | ~ l1_struct_0(X2) ),
    inference(spm,[status(thm)],[c_0_54,c_0_53])).

cnf(c_0_63,negated_conjecture,
    ( k2_pre_topc(esk3_0,k2_struct_0(esk3_0)) != k2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_64,plain,
    ( k2_pre_topc(X1,k2_struct_0(X1)) = u1_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ r1_tarski(u1_struct_0(X1),k2_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_65,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_66,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ r1_tarski(u1_struct_0(X1),k2_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_58])).

cnf(c_0_67,plain,
    ( r1_tarski(u1_struct_0(X1),k2_struct_0(X1))
    | ~ l1_struct_0(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_61]),c_0_62])).

cnf(c_0_68,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_69,negated_conjecture,
    ( k2_struct_0(esk3_0) != u1_struct_0(esk3_0)
    | ~ r1_tarski(u1_struct_0(esk3_0),k2_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_65])])).

cnf(c_0_70,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_71,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_68])).

cnf(c_0_72,negated_conjecture,
    ( ~ l1_struct_0(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_71])])).

cnf(c_0_73,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_36]),c_0_65])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n017.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:33:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.50  # AutoSched0-Mode selected heuristic G_E___208_C12_11_nc_F1_SE_CS_SP_PS_S063N
% 0.19/0.50  # and selection function SelectMaxLComplexAvoidPosUPred.
% 0.19/0.50  #
% 0.19/0.50  # Preprocessing time       : 0.028 s
% 0.19/0.50  # Presaturation interreduction done
% 0.19/0.50  
% 0.19/0.50  # Proof found!
% 0.19/0.50  # SZS status Theorem
% 0.19/0.50  # SZS output start CNFRefutation
% 0.19/0.50  fof(dt_k2_subset_1, axiom, ![X1]:m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 0.19/0.50  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 0.19/0.50  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.19/0.50  fof(dt_k2_pre_topc, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 0.19/0.50  fof(t5_subset, axiom, ![X1, X2, X3]:~(((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))&v1_xboole_0(X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 0.19/0.50  fof(dt_k2_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_struct_0)).
% 0.19/0.50  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.19/0.50  fof(t48_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>r1_tarski(X2,k2_pre_topc(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_pre_topc)).
% 0.19/0.50  fof(t43_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(r1_xboole_0(X2,X3)<=>r1_tarski(X2,k3_subset_1(X1,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_subset_1)).
% 0.19/0.50  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.19/0.50  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.19/0.50  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.19/0.50  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 0.19/0.50  fof(fc3_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>v1_xboole_0(k1_struct_0(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_struct_0)).
% 0.19/0.50  fof(t27_tops_1, conjecture, ![X1]:(l1_pre_topc(X1)=>k2_pre_topc(X1,k2_struct_0(X1))=k2_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_tops_1)).
% 0.19/0.50  fof(t27_pre_topc, axiom, ![X1]:(l1_struct_0(X1)=>k2_struct_0(X1)=k3_subset_1(u1_struct_0(X1),k1_struct_0(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_pre_topc)).
% 0.19/0.50  fof(c_0_16, plain, ![X22]:m1_subset_1(k2_subset_1(X22),k1_zfmisc_1(X22)), inference(variable_rename,[status(thm)],[dt_k2_subset_1])).
% 0.19/0.50  fof(c_0_17, plain, ![X21]:k2_subset_1(X21)=X21, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 0.19/0.50  fof(c_0_18, plain, ![X26, X27]:((~m1_subset_1(X26,k1_zfmisc_1(X27))|r1_tarski(X26,X27))&(~r1_tarski(X26,X27)|m1_subset_1(X26,k1_zfmisc_1(X27)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.19/0.50  fof(c_0_19, plain, ![X31, X32]:(~l1_pre_topc(X31)|~m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))|m1_subset_1(k2_pre_topc(X31,X32),k1_zfmisc_1(u1_struct_0(X31)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).
% 0.19/0.50  fof(c_0_20, plain, ![X28, X29, X30]:(~r2_hidden(X28,X29)|~m1_subset_1(X29,k1_zfmisc_1(X30))|~v1_xboole_0(X30)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).
% 0.19/0.50  cnf(c_0_21, plain, (m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.50  cnf(c_0_22, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.50  cnf(c_0_23, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.50  cnf(c_0_24, plain, (m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.50  fof(c_0_25, plain, ![X33]:(~l1_struct_0(X33)|m1_subset_1(k2_struct_0(X33),k1_zfmisc_1(u1_struct_0(X33)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_struct_0])])).
% 0.19/0.50  fof(c_0_26, plain, ![X34]:(~l1_pre_topc(X34)|l1_struct_0(X34)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.19/0.50  fof(c_0_27, plain, ![X37, X38]:(~l1_pre_topc(X37)|(~m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(X37)))|r1_tarski(X38,k2_pre_topc(X37,X38)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_pre_topc])])])).
% 0.19/0.50  fof(c_0_28, plain, ![X23, X24, X25]:((~r1_xboole_0(X24,X25)|r1_tarski(X24,k3_subset_1(X23,X25))|~m1_subset_1(X25,k1_zfmisc_1(X23))|~m1_subset_1(X24,k1_zfmisc_1(X23)))&(~r1_tarski(X24,k3_subset_1(X23,X25))|r1_xboole_0(X24,X25)|~m1_subset_1(X25,k1_zfmisc_1(X23))|~m1_subset_1(X24,k1_zfmisc_1(X23)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_subset_1])])])])).
% 0.19/0.50  cnf(c_0_29, plain, (~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.50  cnf(c_0_30, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_21, c_0_22])).
% 0.19/0.50  fof(c_0_31, plain, ![X4, X5, X6, X7, X8]:((~r1_tarski(X4,X5)|(~r2_hidden(X6,X4)|r2_hidden(X6,X5)))&((r2_hidden(esk1_2(X7,X8),X7)|r1_tarski(X7,X8))&(~r2_hidden(esk1_2(X7,X8),X8)|r1_tarski(X7,X8)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.19/0.50  fof(c_0_32, plain, ![X10, X11, X13, X14, X15]:(((r2_hidden(esk2_2(X10,X11),X10)|r1_xboole_0(X10,X11))&(r2_hidden(esk2_2(X10,X11),X11)|r1_xboole_0(X10,X11)))&(~r2_hidden(X15,X13)|~r2_hidden(X15,X14)|~r1_xboole_0(X13,X14))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.19/0.50  fof(c_0_33, plain, ![X16, X17]:(((r1_tarski(X16,X17)|X16!=X17)&(r1_tarski(X17,X16)|X16!=X17))&(~r1_tarski(X16,X17)|~r1_tarski(X17,X16)|X16=X17)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.19/0.50  cnf(c_0_34, plain, (r1_tarski(k2_pre_topc(X1,X2),u1_struct_0(X1))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.19/0.50  cnf(c_0_35, plain, (m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.50  cnf(c_0_36, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.50  fof(c_0_37, plain, ![X18, X19, X20]:(~r1_tarski(X18,X19)|~r1_tarski(X19,X20)|r1_tarski(X18,X20)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 0.19/0.50  cnf(c_0_38, plain, (r1_tarski(X2,k2_pre_topc(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.50  cnf(c_0_39, plain, (r1_tarski(X1,k3_subset_1(X3,X2))|~r1_xboole_0(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~m1_subset_1(X1,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.50  cnf(c_0_40, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.50  cnf(c_0_41, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.19/0.50  cnf(c_0_42, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.50  fof(c_0_43, plain, ![X35]:(~l1_struct_0(X35)|v1_xboole_0(k1_struct_0(X35))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc3_struct_0])])).
% 0.19/0.50  cnf(c_0_44, plain, (r2_hidden(esk2_2(X1,X2),X2)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.50  fof(c_0_45, negated_conjecture, ~(![X1]:(l1_pre_topc(X1)=>k2_pre_topc(X1,k2_struct_0(X1))=k2_struct_0(X1))), inference(assume_negation,[status(cth)],[t27_tops_1])).
% 0.19/0.50  cnf(c_0_46, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.50  cnf(c_0_47, plain, (r1_tarski(k2_pre_topc(X1,k2_struct_0(X1)),u1_struct_0(X1))|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_36])).
% 0.19/0.50  cnf(c_0_48, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.19/0.50  cnf(c_0_49, plain, (r1_tarski(k2_struct_0(X1),k2_pre_topc(X1,k2_struct_0(X1)))|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_35]), c_0_36])).
% 0.19/0.50  cnf(c_0_50, plain, (r1_tarski(X1,k3_subset_1(X2,X3))|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_xboole_0(X1,X3)|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.19/0.50  fof(c_0_51, plain, ![X36]:(~l1_struct_0(X36)|k2_struct_0(X36)=k3_subset_1(u1_struct_0(X36),k1_struct_0(X36))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t27_pre_topc])])).
% 0.19/0.50  cnf(c_0_52, plain, (r1_tarski(X1,X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.19/0.50  cnf(c_0_53, plain, (v1_xboole_0(k1_struct_0(X1))|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.19/0.50  cnf(c_0_54, plain, (r1_xboole_0(X1,X2)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_41, c_0_44])).
% 0.19/0.50  fof(c_0_55, negated_conjecture, (l1_pre_topc(esk3_0)&k2_pre_topc(esk3_0,k2_struct_0(esk3_0))!=k2_struct_0(esk3_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_45])])])).
% 0.19/0.50  cnf(c_0_56, plain, (k2_pre_topc(X1,k2_struct_0(X1))=u1_struct_0(X1)|~l1_pre_topc(X1)|~r1_tarski(u1_struct_0(X1),k2_pre_topc(X1,k2_struct_0(X1)))), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.19/0.50  cnf(c_0_57, plain, (r1_tarski(X1,k2_pre_topc(X2,k2_struct_0(X2)))|~l1_pre_topc(X2)|~r1_tarski(X1,k2_struct_0(X2))), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.19/0.50  cnf(c_0_58, plain, (r1_tarski(k2_struct_0(X1),u1_struct_0(X1))|~l1_struct_0(X1)), inference(spm,[status(thm)],[c_0_23, c_0_35])).
% 0.19/0.50  cnf(c_0_59, plain, (r1_tarski(X1,k3_subset_1(X1,X2))|~r1_xboole_0(X1,X2)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_50, c_0_30])).
% 0.19/0.50  cnf(c_0_60, plain, (k2_struct_0(X1)=k3_subset_1(u1_struct_0(X1),k1_struct_0(X1))|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.19/0.50  cnf(c_0_61, plain, (r1_tarski(k1_struct_0(X1),X2)|~l1_struct_0(X1)), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.19/0.50  cnf(c_0_62, plain, (r1_xboole_0(X1,k1_struct_0(X2))|~l1_struct_0(X2)), inference(spm,[status(thm)],[c_0_54, c_0_53])).
% 0.19/0.50  cnf(c_0_63, negated_conjecture, (k2_pre_topc(esk3_0,k2_struct_0(esk3_0))!=k2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.19/0.50  cnf(c_0_64, plain, (k2_pre_topc(X1,k2_struct_0(X1))=u1_struct_0(X1)|~l1_pre_topc(X1)|~r1_tarski(u1_struct_0(X1),k2_struct_0(X1))), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.19/0.50  cnf(c_0_65, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.19/0.50  cnf(c_0_66, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_struct_0(X1)|~r1_tarski(u1_struct_0(X1),k2_struct_0(X1))), inference(spm,[status(thm)],[c_0_46, c_0_58])).
% 0.19/0.50  cnf(c_0_67, plain, (r1_tarski(u1_struct_0(X1),k2_struct_0(X1))|~l1_struct_0(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_61]), c_0_62])).
% 0.19/0.50  cnf(c_0_68, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.50  cnf(c_0_69, negated_conjecture, (k2_struct_0(esk3_0)!=u1_struct_0(esk3_0)|~r1_tarski(u1_struct_0(esk3_0),k2_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_65])])).
% 0.19/0.50  cnf(c_0_70, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_struct_0(X1)), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 0.19/0.50  cnf(c_0_71, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_68])).
% 0.19/0.50  cnf(c_0_72, negated_conjecture, (~l1_struct_0(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_71])])).
% 0.19/0.50  cnf(c_0_73, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_36]), c_0_65])]), ['proof']).
% 0.19/0.50  # SZS output end CNFRefutation
% 0.19/0.50  # Proof object total steps             : 74
% 0.19/0.50  # Proof object clause steps            : 41
% 0.19/0.50  # Proof object formula steps           : 33
% 0.19/0.50  # Proof object conjectures             : 8
% 0.19/0.50  # Proof object clause conjectures      : 5
% 0.19/0.50  # Proof object formula conjectures     : 3
% 0.19/0.50  # Proof object initial clauses used    : 19
% 0.19/0.50  # Proof object initial formulas used   : 16
% 0.19/0.50  # Proof object generating inferences   : 20
% 0.19/0.50  # Proof object simplifying inferences  : 12
% 0.19/0.50  # Training examples: 0 positive, 0 negative
% 0.19/0.50  # Parsed axioms                        : 16
% 0.19/0.50  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.50  # Initial clauses                      : 25
% 0.19/0.50  # Removed in clause preprocessing      : 1
% 0.19/0.50  # Initial clauses in saturation        : 24
% 0.19/0.50  # Processed clauses                    : 1790
% 0.19/0.50  # ...of these trivial                  : 0
% 0.19/0.50  # ...subsumed                          : 1266
% 0.19/0.50  # ...remaining for further processing  : 524
% 0.19/0.50  # Other redundant clauses eliminated   : 2
% 0.19/0.50  # Clauses deleted for lack of memory   : 0
% 0.19/0.50  # Backward-subsumed                    : 23
% 0.19/0.50  # Backward-rewritten                   : 0
% 0.19/0.50  # Generated clauses                    : 4672
% 0.19/0.50  # ...of the previous two non-trivial   : 4472
% 0.19/0.50  # Contextual simplify-reflections      : 29
% 0.19/0.50  # Paramodulations                      : 4670
% 0.19/0.50  # Factorizations                       : 0
% 0.19/0.50  # Equation resolutions                 : 2
% 0.19/0.50  # Propositional unsat checks           : 0
% 0.19/0.50  #    Propositional check models        : 0
% 0.19/0.50  #    Propositional check unsatisfiable : 0
% 0.19/0.50  #    Propositional clauses             : 0
% 0.19/0.50  #    Propositional clauses after purity: 0
% 0.19/0.50  #    Propositional unsat core size     : 0
% 0.19/0.50  #    Propositional preprocessing time  : 0.000
% 0.19/0.50  #    Propositional encoding time       : 0.000
% 0.19/0.50  #    Propositional solver time         : 0.000
% 0.19/0.50  #    Success case prop preproc time    : 0.000
% 0.19/0.50  #    Success case prop encoding time   : 0.000
% 0.19/0.50  #    Success case prop solver time     : 0.000
% 0.19/0.50  # Current number of processed clauses  : 476
% 0.19/0.50  #    Positive orientable unit clauses  : 3
% 0.19/0.50  #    Positive unorientable unit clauses: 0
% 0.19/0.50  #    Negative unit clauses             : 3
% 0.19/0.50  #    Non-unit-clauses                  : 470
% 0.19/0.50  # Current number of unprocessed clauses: 2719
% 0.19/0.50  # ...number of literals in the above   : 15329
% 0.19/0.50  # Current number of archived formulas  : 0
% 0.19/0.50  # Current number of archived clauses   : 47
% 0.19/0.50  # Clause-clause subsumption calls (NU) : 66478
% 0.19/0.50  # Rec. Clause-clause subsumption calls : 17100
% 0.19/0.50  # Non-unit clause-clause subsumptions  : 1313
% 0.19/0.50  # Unit Clause-clause subsumption calls : 0
% 0.19/0.50  # Rewrite failures with RHS unbound    : 0
% 0.19/0.50  # BW rewrite match attempts            : 1
% 0.19/0.50  # BW rewrite match successes           : 0
% 0.19/0.50  # Condensation attempts                : 0
% 0.19/0.50  # Condensation successes               : 0
% 0.19/0.50  # Termbank termtop insertions          : 84933
% 0.19/0.50  
% 0.19/0.50  # -------------------------------------------------
% 0.19/0.50  # User time                : 0.155 s
% 0.19/0.50  # System time              : 0.007 s
% 0.19/0.50  # Total time               : 0.162 s
% 0.19/0.50  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
