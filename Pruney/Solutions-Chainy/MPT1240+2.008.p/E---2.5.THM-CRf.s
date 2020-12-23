%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:10:59 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :  155 (2229 expanded)
%              Number of clauses        :   96 ( 891 expanded)
%              Number of leaves         :   29 ( 558 expanded)
%              Depth                    :   17
%              Number of atoms          :  365 (10331 expanded)
%              Number of equality atoms :   79 ( 714 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t85_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_xboole_0(X1,k4_xboole_0(X3,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t72_xboole_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( k2_xboole_0(X1,X2) = k2_xboole_0(X3,X4)
        & r1_xboole_0(X3,X1)
        & r1_xboole_0(X4,X2) )
     => X3 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_xboole_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(t20_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(X1)
    <=> X1 != X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t80_zfmisc_1,axiom,(
    ! [X1] : r1_tarski(k1_tarski(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_zfmisc_1)).

fof(t56_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( ~ r2_hidden(X1,X2)
     => r1_xboole_0(k1_tarski(X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_zfmisc_1)).

fof(t54_tops_1,conjecture,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2,X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
         => ( r2_hidden(X2,k1_tops_1(X1,X3))
          <=> ? [X4] :
                ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                & v3_pre_topc(X4,X1)
                & r1_tarski(X4,X3)
                & r2_hidden(X2,X4) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_tops_1)).

fof(fc9_tops_1,axiom,(
    ! [X1,X2] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => v3_pre_topc(k1_tops_1(X1,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

fof(dt_k1_tops_1,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tops_1)).

fof(t44_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => r1_tarski(k1_tops_1(X1,X2),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(t48_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( r1_tarski(X2,X3)
               => r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tops_1)).

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(fc1_subset_1,axiom,(
    ! [X1] : ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(redefinition_k4_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => k4_subset_1(X1,X2,X3) = k2_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(t53_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( ( v3_pre_topc(X2,X1)
             => k2_pre_topc(X1,k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2)) = k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2) )
            & ( ( v2_pre_topc(X1)
                & k2_pre_topc(X1,k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2)) = k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2) )
             => v3_pre_topc(X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_pre_topc)).

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

fof(redefinition_k7_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k7_subset_1(X1,X2,X3) = k4_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(t33_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => k3_subset_1(X1,k7_subset_1(X1,X2,X3)) = k4_subset_1(X1,k3_subset_1(X1,X2),X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_subset_1)).

fof(t65_xboole_1,axiom,(
    ! [X1] : r1_xboole_0(X1,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(d1_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k1_tops_1(X1,X2) = k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_1)).

fof(c_0_29,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_30,plain,(
    ! [X26,X27,X28] :
      ( ~ r1_tarski(X26,X27)
      | r1_xboole_0(X26,k4_xboole_0(X28,X27)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t85_xboole_1])])).

cnf(c_0_31,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_32,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_33,plain,(
    ! [X14] : k3_xboole_0(X14,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

fof(c_0_34,plain,(
    ! [X16,X17] : k4_xboole_0(X16,k4_xboole_0(X16,X17)) = k3_xboole_0(X16,X17) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_35,plain,(
    ! [X22,X23,X24,X25] :
      ( k2_xboole_0(X22,X23) != k2_xboole_0(X24,X25)
      | ~ r1_xboole_0(X24,X22)
      | ~ r1_xboole_0(X25,X23)
      | X24 = X23 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t72_xboole_1])])).

cnf(c_0_36,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X3,X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_37,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

fof(c_0_38,plain,(
    ! [X15] : k4_xboole_0(X15,k1_xboole_0) = X15 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

fof(c_0_39,plain,(
    ! [X32,X33] :
      ( ( k4_xboole_0(k1_tarski(X32),k1_tarski(X33)) != k1_tarski(X32)
        | X32 != X33 )
      & ( X32 = X33
        | k4_xboole_0(k1_tarski(X32),k1_tarski(X33)) = k1_tarski(X32) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_zfmisc_1])])).

fof(c_0_40,plain,(
    ! [X31] : k2_tarski(X31,X31) = k1_tarski(X31) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

cnf(c_0_41,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_42,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

fof(c_0_43,plain,(
    ! [X39] : r1_tarski(k1_tarski(X39),k1_zfmisc_1(X39)) ),
    inference(variable_rename,[status(thm)],[t80_zfmisc_1])).

cnf(c_0_44,plain,
    ( X3 = X2
    | k2_xboole_0(X1,X2) != k2_xboole_0(X3,X4)
    | ~ r1_xboole_0(X3,X1)
    | ~ r1_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_45,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_46,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

fof(c_0_47,plain,(
    ! [X37,X38] :
      ( r2_hidden(X37,X38)
      | r1_xboole_0(k1_tarski(X37),X38) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t56_zfmisc_1])])])).

cnf(c_0_48,plain,
    ( k4_xboole_0(k1_tarski(X1),k1_tarski(X2)) != k1_tarski(X1)
    | X1 != X2 ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_49,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_50,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_41,c_0_42])).

fof(c_0_51,negated_conjecture,(
    ~ ! [X1] :
        ( ( v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2,X3] :
            ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
           => ( r2_hidden(X2,k1_tops_1(X1,X3))
            <=> ? [X4] :
                  ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                  & v3_pre_topc(X4,X1)
                  & r1_tarski(X4,X3)
                  & r2_hidden(X2,X4) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t54_tops_1])).

cnf(c_0_52,plain,
    ( r1_tarski(k1_tarski(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_53,plain,
    ( X1 = X2
    | ~ r1_xboole_0(X1,X1)
    | ~ r1_xboole_0(X2,X2) ),
    inference(er,[status(thm)],[c_0_44])).

cnf(c_0_54,plain,
    ( r1_xboole_0(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_55,plain,
    ( r2_hidden(X1,X2)
    | r1_xboole_0(k1_tarski(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_56,plain,
    ( X1 != X2
    | k4_xboole_0(k2_tarski(X1,X1),k2_tarski(X2,X2)) != k2_tarski(X1,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_49]),c_0_49]),c_0_49])).

cnf(c_0_57,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_50,c_0_46])).

fof(c_0_58,negated_conjecture,(
    ! [X76] :
      ( v2_pre_topc(esk2_0)
      & l1_pre_topc(esk2_0)
      & m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
      & ( ~ r2_hidden(esk3_0,k1_tops_1(esk2_0,esk4_0))
        | ~ m1_subset_1(X76,k1_zfmisc_1(u1_struct_0(esk2_0)))
        | ~ v3_pre_topc(X76,esk2_0)
        | ~ r1_tarski(X76,esk4_0)
        | ~ r2_hidden(esk3_0,X76) )
      & ( m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
        | r2_hidden(esk3_0,k1_tops_1(esk2_0,esk4_0)) )
      & ( v3_pre_topc(esk5_0,esk2_0)
        | r2_hidden(esk3_0,k1_tops_1(esk2_0,esk4_0)) )
      & ( r1_tarski(esk5_0,esk4_0)
        | r2_hidden(esk3_0,k1_tops_1(esk2_0,esk4_0)) )
      & ( r2_hidden(esk3_0,esk5_0)
        | r2_hidden(esk3_0,k1_tops_1(esk2_0,esk4_0)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_51])])])])])).

fof(c_0_59,plain,(
    ! [X66,X67] :
      ( ~ v2_pre_topc(X66)
      | ~ l1_pre_topc(X66)
      | ~ m1_subset_1(X67,k1_zfmisc_1(u1_struct_0(X66)))
      | v3_pre_topc(k1_tops_1(X66,X67),X66) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc9_tops_1])])).

fof(c_0_60,plain,(
    ! [X64,X65] :
      ( ~ l1_pre_topc(X64)
      | ~ m1_subset_1(X65,k1_zfmisc_1(u1_struct_0(X64)))
      | m1_subset_1(k1_tops_1(X64,X65),k1_zfmisc_1(u1_struct_0(X64))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_tops_1])])).

fof(c_0_61,plain,(
    ! [X68,X69] :
      ( ~ l1_pre_topc(X68)
      | ~ m1_subset_1(X69,k1_zfmisc_1(u1_struct_0(X68)))
      | r1_tarski(k1_tops_1(X68,X69),X69) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_tops_1])])])).

fof(c_0_62,plain,(
    ! [X12,X13] :
      ( ~ r1_tarski(X12,X13)
      | k3_xboole_0(X12,X13) = X12 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

fof(c_0_63,plain,(
    ! [X54] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X54)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

cnf(c_0_64,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_65,plain,
    ( r1_tarski(k2_tarski(X1,X1),k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_52,c_0_49])).

cnf(c_0_66,plain,
    ( k1_xboole_0 = X1
    | ~ r1_xboole_0(X1,X1) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_67,plain,
    ( r2_hidden(X1,X2)
    | r1_xboole_0(k2_tarski(X1,X1),X2) ),
    inference(rw,[status(thm)],[c_0_55,c_0_49])).

cnf(c_0_68,plain,
    ( k2_tarski(X1,X1) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_56]),c_0_57])).

cnf(c_0_69,negated_conjecture,
    ( ~ r2_hidden(esk3_0,k1_tops_1(esk2_0,esk4_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ v3_pre_topc(X1,esk2_0)
    | ~ r1_tarski(X1,esk4_0)
    | ~ r2_hidden(esk3_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_70,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | r2_hidden(esk3_0,k1_tops_1(esk2_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_71,plain,
    ( v3_pre_topc(k1_tops_1(X1,X2),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_72,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_73,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_74,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_75,plain,
    ( m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_76,plain,
    ( r1_tarski(k1_tops_1(X1,X2),X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_77,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_78,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

fof(c_0_79,plain,(
    ! [X70,X71,X72] :
      ( ~ l1_pre_topc(X70)
      | ~ m1_subset_1(X71,k1_zfmisc_1(u1_struct_0(X70)))
      | ~ m1_subset_1(X72,k1_zfmisc_1(u1_struct_0(X70)))
      | ~ r1_tarski(X71,X72)
      | r1_tarski(k1_tops_1(X70,X71),k1_tops_1(X70,X72)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_tops_1])])])).

cnf(c_0_80,negated_conjecture,
    ( r1_tarski(esk5_0,esk4_0)
    | r2_hidden(esk3_0,k1_tops_1(esk2_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_81,negated_conjecture,
    ( v3_pre_topc(esk5_0,esk2_0)
    | r2_hidden(esk3_0,k1_tops_1(esk2_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

fof(c_0_82,plain,(
    ! [X40,X41] :
      ( ( ~ m1_subset_1(X41,X40)
        | r2_hidden(X41,X40)
        | v1_xboole_0(X40) )
      & ( ~ r2_hidden(X41,X40)
        | m1_subset_1(X41,X40)
        | v1_xboole_0(X40) )
      & ( ~ m1_subset_1(X41,X40)
        | v1_xboole_0(X41)
        | ~ v1_xboole_0(X40) )
      & ( ~ v1_xboole_0(X41)
        | m1_subset_1(X41,X40)
        | ~ v1_xboole_0(X40) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

cnf(c_0_83,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X1,k2_tarski(X2,X2)) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_84,plain,
    ( r2_hidden(X1,k2_tarski(X1,X1)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_68])).

fof(c_0_85,plain,(
    ! [X44] : ~ v1_xboole_0(k1_zfmisc_1(X44)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).

fof(c_0_86,plain,(
    ! [X45,X46,X47] :
      ( ~ m1_subset_1(X46,k1_zfmisc_1(X45))
      | ~ m1_subset_1(X47,k1_zfmisc_1(X45))
      | k4_subset_1(X45,X46,X47) = k2_xboole_0(X46,X47) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).

cnf(c_0_87,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ v3_pre_topc(X1,esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ r2_hidden(esk3_0,X1)
    | ~ r1_tarski(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_88,negated_conjecture,
    ( v3_pre_topc(k1_tops_1(esk2_0,esk4_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_73]),c_0_74])])).

cnf(c_0_89,negated_conjecture,
    ( m1_subset_1(k1_tops_1(esk2_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_72]),c_0_74])])).

cnf(c_0_90,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk2_0,esk4_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_72]),c_0_74])])).

cnf(c_0_91,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_77,c_0_42])).

cnf(c_0_92,plain,
    ( r1_tarski(k1_tops_1(X1,k1_xboole_0),k1_xboole_0)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_76,c_0_78])).

fof(c_0_93,plain,(
    ! [X11] : k2_xboole_0(X11,k1_xboole_0) = X11 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

cnf(c_0_94,plain,
    ( r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_79])).

cnf(c_0_95,negated_conjecture,
    ( r1_tarski(esk5_0,esk4_0)
    | ~ v3_pre_topc(X1,esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ r2_hidden(esk3_0,X1)
    | ~ r1_tarski(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_69,c_0_80])).

fof(c_0_96,plain,(
    ! [X42,X43] :
      ( ~ m1_subset_1(X43,k1_zfmisc_1(X42))
      | k3_subset_1(X42,X43) = k4_xboole_0(X42,X43) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

fof(c_0_97,plain,(
    ! [X60,X61] :
      ( ( ~ v3_pre_topc(X61,X60)
        | k2_pre_topc(X60,k7_subset_1(u1_struct_0(X60),k2_struct_0(X60),X61)) = k7_subset_1(u1_struct_0(X60),k2_struct_0(X60),X61)
        | ~ m1_subset_1(X61,k1_zfmisc_1(u1_struct_0(X60)))
        | ~ l1_pre_topc(X60) )
      & ( ~ v2_pre_topc(X60)
        | k2_pre_topc(X60,k7_subset_1(u1_struct_0(X60),k2_struct_0(X60),X61)) != k7_subset_1(u1_struct_0(X60),k2_struct_0(X60),X61)
        | v3_pre_topc(X61,X60)
        | ~ m1_subset_1(X61,k1_zfmisc_1(u1_struct_0(X60)))
        | ~ l1_pre_topc(X60) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t53_pre_topc])])])])).

cnf(c_0_98,negated_conjecture,
    ( v3_pre_topc(esk5_0,esk2_0)
    | ~ v3_pre_topc(X1,esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ r2_hidden(esk3_0,X1)
    | ~ r1_tarski(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_69,c_0_81])).

fof(c_0_99,plain,(
    ! [X58] :
      ( ~ l1_struct_0(X58)
      | k2_struct_0(X58) = u1_struct_0(X58) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

fof(c_0_100,plain,(
    ! [X59] :
      ( ~ l1_pre_topc(X59)
      | l1_struct_0(X59) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

fof(c_0_101,plain,(
    ! [X48,X49,X50] :
      ( ~ m1_subset_1(X49,k1_zfmisc_1(X48))
      | k7_subset_1(X48,X49,X50) = k4_xboole_0(X49,X50) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).

cnf(c_0_102,plain,
    ( m1_subset_1(X1,X2)
    | v1_xboole_0(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_82])).

cnf(c_0_103,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_83,c_0_84])).

cnf(c_0_104,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_85])).

fof(c_0_105,plain,(
    ! [X51,X52,X53] :
      ( ~ m1_subset_1(X52,k1_zfmisc_1(X51))
      | ~ m1_subset_1(X53,k1_zfmisc_1(X51))
      | k3_subset_1(X51,k7_subset_1(X51,X52,X53)) = k4_subset_1(X51,k3_subset_1(X51,X52),X53) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t33_subset_1])])])).

cnf(c_0_106,plain,
    ( k4_subset_1(X2,X1,X3) = k2_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_86])).

cnf(c_0_107,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_88]),c_0_89]),c_0_90])]),c_0_70])).

cnf(c_0_108,plain,
    ( k1_tops_1(X1,k1_xboole_0) = k1_xboole_0
    | ~ l1_pre_topc(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_92]),c_0_46]),c_0_57])).

cnf(c_0_109,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_93])).

fof(c_0_110,plain,(
    ! [X18] : r1_xboole_0(X18,k1_xboole_0) ),
    inference(variable_rename,[status(thm)],[t65_xboole_1])).

cnf(c_0_111,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk2_0,X1),k1_tops_1(esk2_0,esk4_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ r1_tarski(X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_72]),c_0_74])])).

cnf(c_0_112,negated_conjecture,
    ( r1_tarski(esk5_0,esk4_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_88]),c_0_89]),c_0_90])]),c_0_80])).

fof(c_0_113,plain,(
    ! [X62,X63] :
      ( ~ l1_pre_topc(X62)
      | ~ m1_subset_1(X63,k1_zfmisc_1(u1_struct_0(X62)))
      | k1_tops_1(X62,X63) = k3_subset_1(u1_struct_0(X62),k2_pre_topc(X62,k3_subset_1(u1_struct_0(X62),X63))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tops_1])])])).

cnf(c_0_114,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_96])).

cnf(c_0_115,plain,
    ( k2_pre_topc(X2,k7_subset_1(u1_struct_0(X2),k2_struct_0(X2),X1)) = k7_subset_1(u1_struct_0(X2),k2_struct_0(X2),X1)
    | ~ v3_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_97])).

cnf(c_0_116,negated_conjecture,
    ( v3_pre_topc(esk5_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_81]),c_0_88]),c_0_89]),c_0_90])])).

cnf(c_0_117,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_99])).

cnf(c_0_118,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_100])).

cnf(c_0_119,plain,
    ( k7_subset_1(X2,X1,X3) = k4_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_101])).

cnf(c_0_120,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_103]),c_0_104])).

cnf(c_0_121,plain,
    ( k3_subset_1(X2,k7_subset_1(X2,X1,X3)) = k4_subset_1(X2,k3_subset_1(X2,X1),X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_105])).

cnf(c_0_122,negated_conjecture,
    ( k4_subset_1(u1_struct_0(esk2_0),X1,esk5_0) = k2_xboole_0(X1,esk5_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_106,c_0_107])).

cnf(c_0_123,plain,
    ( m1_subset_1(k1_tops_1(X1,k1_xboole_0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_75,c_0_78])).

cnf(c_0_124,negated_conjecture,
    ( k1_tops_1(esk2_0,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_108,c_0_74])).

cnf(c_0_125,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_xboole_0(k2_xboole_0(X1,X2),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_109])]),c_0_54])])).

cnf(c_0_126,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_110])).

cnf(c_0_127,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk2_0,X1),k1_tops_1(esk2_0,k1_tops_1(esk2_0,esk4_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ r1_tarski(X1,k1_tops_1(esk2_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_89]),c_0_74])])).

cnf(c_0_128,negated_conjecture,
    ( m1_subset_1(k1_tops_1(esk2_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_107]),c_0_74])])).

cnf(c_0_129,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk2_0,esk5_0),k1_tops_1(esk2_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111,c_0_112]),c_0_107])])).

cnf(c_0_130,plain,
    ( k1_tops_1(X1,X2) = k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_113])).

cnf(c_0_131,negated_conjecture,
    ( k3_subset_1(u1_struct_0(esk2_0),esk5_0) = k4_xboole_0(u1_struct_0(esk2_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_114,c_0_107])).

cnf(c_0_132,negated_conjecture,
    ( k2_pre_topc(esk2_0,k7_subset_1(u1_struct_0(esk2_0),k2_struct_0(esk2_0),esk5_0)) = k7_subset_1(u1_struct_0(esk2_0),k2_struct_0(esk2_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115,c_0_107]),c_0_116]),c_0_74])])).

cnf(c_0_133,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_117,c_0_118])).

cnf(c_0_134,plain,
    ( k7_subset_1(X1,X1,X2) = k4_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_119,c_0_120])).

cnf(c_0_135,negated_conjecture,
    ( k4_subset_1(u1_struct_0(esk2_0),k3_subset_1(u1_struct_0(esk2_0),X1),esk5_0) = k3_subset_1(u1_struct_0(esk2_0),k7_subset_1(u1_struct_0(esk2_0),X1,esk5_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_121,c_0_107])).

cnf(c_0_136,plain,
    ( k3_subset_1(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114,c_0_120]),c_0_57])).

cnf(c_0_137,negated_conjecture,
    ( k4_subset_1(u1_struct_0(esk2_0),k1_xboole_0,esk5_0) = k2_xboole_0(k1_xboole_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_122,c_0_123]),c_0_124]),c_0_124]),c_0_74])])).

cnf(c_0_138,plain,
    ( k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_125,c_0_126])).

cnf(c_0_139,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk2_0,k1_tops_1(esk2_0,esk5_0)),k1_tops_1(esk2_0,k1_tops_1(esk2_0,esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_127,c_0_128]),c_0_129])])).

cnf(c_0_140,negated_conjecture,
    ( k3_subset_1(u1_struct_0(esk2_0),k2_pre_topc(esk2_0,k4_xboole_0(u1_struct_0(esk2_0),esk5_0))) = k1_tops_1(esk2_0,esk5_0) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_130,c_0_107]),c_0_74])]),c_0_131])).

cnf(c_0_141,negated_conjecture,
    ( k2_pre_topc(esk2_0,k4_xboole_0(u1_struct_0(esk2_0),esk5_0)) = k4_xboole_0(u1_struct_0(esk2_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_132,c_0_133]),c_0_134]),c_0_134]),c_0_74])])).

cnf(c_0_142,negated_conjecture,
    ( k3_subset_1(u1_struct_0(esk2_0),k4_xboole_0(u1_struct_0(esk2_0),esk5_0)) = esk5_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_135,c_0_120]),c_0_136]),c_0_137]),c_0_138]),c_0_134])).

cnf(c_0_143,negated_conjecture,
    ( r2_hidden(esk3_0,esk5_0)
    | r2_hidden(esk3_0,k1_tops_1(esk2_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_144,negated_conjecture,
    ( r2_hidden(X1,k1_tops_1(esk2_0,k1_tops_1(esk2_0,esk4_0)))
    | ~ r2_hidden(X1,k1_tops_1(esk2_0,k1_tops_1(esk2_0,esk5_0))) ),
    inference(spm,[status(thm)],[c_0_64,c_0_139])).

cnf(c_0_145,negated_conjecture,
    ( k1_tops_1(esk2_0,esk5_0) = esk5_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_140,c_0_141]),c_0_142])).

cnf(c_0_146,negated_conjecture,
    ( r2_hidden(esk3_0,esk5_0)
    | ~ v3_pre_topc(X1,esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ r2_hidden(esk3_0,X1)
    | ~ r1_tarski(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_69,c_0_143])).

cnf(c_0_147,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk2_0,k1_tops_1(esk2_0,esk4_0)),k1_tops_1(esk2_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_89]),c_0_74])])).

cnf(c_0_148,negated_conjecture,
    ( r2_hidden(X1,k1_tops_1(esk2_0,k1_tops_1(esk2_0,esk4_0)))
    | ~ r2_hidden(X1,esk5_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_144,c_0_145]),c_0_145])).

cnf(c_0_149,negated_conjecture,
    ( r2_hidden(esk3_0,esk5_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_146,c_0_88]),c_0_89]),c_0_90])]),c_0_143])).

cnf(c_0_150,negated_conjecture,
    ( r2_hidden(X1,k1_tops_1(esk2_0,esk4_0))
    | ~ r2_hidden(X1,k1_tops_1(esk2_0,k1_tops_1(esk2_0,esk4_0))) ),
    inference(spm,[status(thm)],[c_0_64,c_0_147])).

cnf(c_0_151,negated_conjecture,
    ( r2_hidden(esk3_0,k1_tops_1(esk2_0,k1_tops_1(esk2_0,esk4_0))) ),
    inference(spm,[status(thm)],[c_0_148,c_0_149])).

cnf(c_0_152,negated_conjecture,
    ( r2_hidden(esk3_0,k1_tops_1(esk2_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_150,c_0_151])).

cnf(c_0_153,negated_conjecture,
    ( ~ v3_pre_topc(X1,esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ r2_hidden(esk3_0,X1)
    | ~ r1_tarski(X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_69,c_0_152])])).

cnf(c_0_154,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_153,c_0_116]),c_0_107]),c_0_149]),c_0_112])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.36  % Computer   : n023.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % WCLimit    : 600
% 0.14/0.36  % DateTime   : Tue Dec  1 14:42:50 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  # Version: 2.5pre002
% 0.14/0.36  # No SInE strategy applied
% 0.14/0.36  # Trying AutoSched0 for 299 seconds
% 0.14/0.41  # AutoSched0-Mode selected heuristic G_E___110_C45_F1_PI_SE_CS_SP_PS_S4S
% 0.14/0.41  # and selection function SelectNewComplexAHPNS.
% 0.14/0.41  #
% 0.14/0.41  # Preprocessing time       : 0.019 s
% 0.14/0.41  # Presaturation interreduction done
% 0.14/0.41  
% 0.14/0.41  # Proof found!
% 0.14/0.41  # SZS status Theorem
% 0.14/0.41  # SZS output start CNFRefutation
% 0.14/0.41  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.14/0.41  fof(t85_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_xboole_0(X1,k4_xboole_0(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t85_xboole_1)).
% 0.14/0.41  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 0.14/0.41  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.14/0.41  fof(t72_xboole_1, axiom, ![X1, X2, X3, X4]:(((k2_xboole_0(X1,X2)=k2_xboole_0(X3,X4)&r1_xboole_0(X3,X1))&r1_xboole_0(X4,X2))=>X3=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_xboole_1)).
% 0.14/0.41  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 0.14/0.41  fof(t20_zfmisc_1, axiom, ![X1, X2]:(k4_xboole_0(k1_tarski(X1),k1_tarski(X2))=k1_tarski(X1)<=>X1!=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 0.14/0.41  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.14/0.41  fof(t80_zfmisc_1, axiom, ![X1]:r1_tarski(k1_tarski(X1),k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_zfmisc_1)).
% 0.14/0.41  fof(t56_zfmisc_1, axiom, ![X1, X2]:(~(r2_hidden(X1,X2))=>r1_xboole_0(k1_tarski(X1),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_zfmisc_1)).
% 0.14/0.41  fof(t54_tops_1, conjecture, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(r2_hidden(X2,k1_tops_1(X1,X3))<=>?[X4]:(((m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))&v3_pre_topc(X4,X1))&r1_tarski(X4,X3))&r2_hidden(X2,X4))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t54_tops_1)).
% 0.14/0.41  fof(fc9_tops_1, axiom, ![X1, X2]:(((v2_pre_topc(X1)&l1_pre_topc(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>v3_pre_topc(k1_tops_1(X1,X2),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_tops_1)).
% 0.14/0.41  fof(dt_k1_tops_1, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tops_1)).
% 0.14/0.41  fof(t44_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>r1_tarski(k1_tops_1(X1,X2),X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_1)).
% 0.14/0.41  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.14/0.41  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 0.14/0.41  fof(t48_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(r1_tarski(X2,X3)=>r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_tops_1)).
% 0.14/0.41  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 0.14/0.41  fof(fc1_subset_1, axiom, ![X1]:~(v1_xboole_0(k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 0.14/0.41  fof(redefinition_k4_subset_1, axiom, ![X1, X2, X3]:((m1_subset_1(X2,k1_zfmisc_1(X1))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>k4_subset_1(X1,X2,X3)=k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 0.14/0.41  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 0.14/0.41  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 0.14/0.41  fof(t53_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>((v3_pre_topc(X2,X1)=>k2_pre_topc(X1,k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2))=k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2))&((v2_pre_topc(X1)&k2_pre_topc(X1,k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2))=k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2))=>v3_pre_topc(X2,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t53_pre_topc)).
% 0.14/0.41  fof(d3_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>k2_struct_0(X1)=u1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 0.14/0.41  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.14/0.41  fof(redefinition_k7_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k7_subset_1(X1,X2,X3)=k4_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 0.14/0.41  fof(t33_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k3_subset_1(X1,k7_subset_1(X1,X2,X3))=k4_subset_1(X1,k3_subset_1(X1,X2),X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_subset_1)).
% 0.14/0.41  fof(t65_xboole_1, axiom, ![X1]:r1_xboole_0(X1,k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 0.14/0.41  fof(d1_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k1_tops_1(X1,X2)=k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tops_1)).
% 0.14/0.41  fof(c_0_29, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.14/0.41  fof(c_0_30, plain, ![X26, X27, X28]:(~r1_tarski(X26,X27)|r1_xboole_0(X26,k4_xboole_0(X28,X27))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t85_xboole_1])])).
% 0.14/0.41  cnf(c_0_31, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.14/0.41  cnf(c_0_32, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.14/0.41  fof(c_0_33, plain, ![X14]:k3_xboole_0(X14,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 0.14/0.41  fof(c_0_34, plain, ![X16, X17]:k4_xboole_0(X16,k4_xboole_0(X16,X17))=k3_xboole_0(X16,X17), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.14/0.41  fof(c_0_35, plain, ![X22, X23, X24, X25]:(k2_xboole_0(X22,X23)!=k2_xboole_0(X24,X25)|~r1_xboole_0(X24,X22)|~r1_xboole_0(X25,X23)|X24=X23), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t72_xboole_1])])).
% 0.14/0.41  cnf(c_0_36, plain, (r1_xboole_0(X1,k4_xboole_0(X3,X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.14/0.41  cnf(c_0_37, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.14/0.41  fof(c_0_38, plain, ![X15]:k4_xboole_0(X15,k1_xboole_0)=X15, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.14/0.41  fof(c_0_39, plain, ![X32, X33]:((k4_xboole_0(k1_tarski(X32),k1_tarski(X33))!=k1_tarski(X32)|X32!=X33)&(X32=X33|k4_xboole_0(k1_tarski(X32),k1_tarski(X33))=k1_tarski(X32))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_zfmisc_1])])).
% 0.14/0.41  fof(c_0_40, plain, ![X31]:k2_tarski(X31,X31)=k1_tarski(X31), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.14/0.41  cnf(c_0_41, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.14/0.41  cnf(c_0_42, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.14/0.41  fof(c_0_43, plain, ![X39]:r1_tarski(k1_tarski(X39),k1_zfmisc_1(X39)), inference(variable_rename,[status(thm)],[t80_zfmisc_1])).
% 0.14/0.41  cnf(c_0_44, plain, (X3=X2|k2_xboole_0(X1,X2)!=k2_xboole_0(X3,X4)|~r1_xboole_0(X3,X1)|~r1_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.14/0.41  cnf(c_0_45, plain, (r1_xboole_0(X1,k4_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.14/0.41  cnf(c_0_46, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.14/0.41  fof(c_0_47, plain, ![X37, X38]:(r2_hidden(X37,X38)|r1_xboole_0(k1_tarski(X37),X38)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t56_zfmisc_1])])])).
% 0.14/0.41  cnf(c_0_48, plain, (k4_xboole_0(k1_tarski(X1),k1_tarski(X2))!=k1_tarski(X1)|X1!=X2), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.14/0.41  cnf(c_0_49, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.14/0.41  cnf(c_0_50, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))=k1_xboole_0), inference(rw,[status(thm)],[c_0_41, c_0_42])).
% 0.14/0.41  fof(c_0_51, negated_conjecture, ~(![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(r2_hidden(X2,k1_tops_1(X1,X3))<=>?[X4]:(((m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))&v3_pre_topc(X4,X1))&r1_tarski(X4,X3))&r2_hidden(X2,X4)))))), inference(assume_negation,[status(cth)],[t54_tops_1])).
% 0.14/0.41  cnf(c_0_52, plain, (r1_tarski(k1_tarski(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.14/0.41  cnf(c_0_53, plain, (X1=X2|~r1_xboole_0(X1,X1)|~r1_xboole_0(X2,X2)), inference(er,[status(thm)],[c_0_44])).
% 0.14/0.41  cnf(c_0_54, plain, (r1_xboole_0(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.14/0.41  cnf(c_0_55, plain, (r2_hidden(X1,X2)|r1_xboole_0(k1_tarski(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.14/0.41  cnf(c_0_56, plain, (X1!=X2|k4_xboole_0(k2_tarski(X1,X1),k2_tarski(X2,X2))!=k2_tarski(X1,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48, c_0_49]), c_0_49]), c_0_49])).
% 0.14/0.41  cnf(c_0_57, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[c_0_50, c_0_46])).
% 0.14/0.41  fof(c_0_58, negated_conjecture, ![X76]:((v2_pre_topc(esk2_0)&l1_pre_topc(esk2_0))&(m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0)))&((~r2_hidden(esk3_0,k1_tops_1(esk2_0,esk4_0))|(~m1_subset_1(X76,k1_zfmisc_1(u1_struct_0(esk2_0)))|~v3_pre_topc(X76,esk2_0)|~r1_tarski(X76,esk4_0)|~r2_hidden(esk3_0,X76)))&((((m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk2_0)))|r2_hidden(esk3_0,k1_tops_1(esk2_0,esk4_0)))&(v3_pre_topc(esk5_0,esk2_0)|r2_hidden(esk3_0,k1_tops_1(esk2_0,esk4_0))))&(r1_tarski(esk5_0,esk4_0)|r2_hidden(esk3_0,k1_tops_1(esk2_0,esk4_0))))&(r2_hidden(esk3_0,esk5_0)|r2_hidden(esk3_0,k1_tops_1(esk2_0,esk4_0))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_51])])])])])).
% 0.14/0.41  fof(c_0_59, plain, ![X66, X67]:(~v2_pre_topc(X66)|~l1_pre_topc(X66)|~m1_subset_1(X67,k1_zfmisc_1(u1_struct_0(X66)))|v3_pre_topc(k1_tops_1(X66,X67),X66)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc9_tops_1])])).
% 0.14/0.41  fof(c_0_60, plain, ![X64, X65]:(~l1_pre_topc(X64)|~m1_subset_1(X65,k1_zfmisc_1(u1_struct_0(X64)))|m1_subset_1(k1_tops_1(X64,X65),k1_zfmisc_1(u1_struct_0(X64)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_tops_1])])).
% 0.14/0.41  fof(c_0_61, plain, ![X68, X69]:(~l1_pre_topc(X68)|(~m1_subset_1(X69,k1_zfmisc_1(u1_struct_0(X68)))|r1_tarski(k1_tops_1(X68,X69),X69))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_tops_1])])])).
% 0.14/0.41  fof(c_0_62, plain, ![X12, X13]:(~r1_tarski(X12,X13)|k3_xboole_0(X12,X13)=X12), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.14/0.41  fof(c_0_63, plain, ![X54]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X54)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.14/0.41  cnf(c_0_64, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.14/0.41  cnf(c_0_65, plain, (r1_tarski(k2_tarski(X1,X1),k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_52, c_0_49])).
% 0.14/0.41  cnf(c_0_66, plain, (k1_xboole_0=X1|~r1_xboole_0(X1,X1)), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.14/0.41  cnf(c_0_67, plain, (r2_hidden(X1,X2)|r1_xboole_0(k2_tarski(X1,X1),X2)), inference(rw,[status(thm)],[c_0_55, c_0_49])).
% 0.14/0.41  cnf(c_0_68, plain, (k2_tarski(X1,X1)!=k1_xboole_0), inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_56]), c_0_57])).
% 0.14/0.41  cnf(c_0_69, negated_conjecture, (~r2_hidden(esk3_0,k1_tops_1(esk2_0,esk4_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))|~v3_pre_topc(X1,esk2_0)|~r1_tarski(X1,esk4_0)|~r2_hidden(esk3_0,X1)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.14/0.41  cnf(c_0_70, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk2_0)))|r2_hidden(esk3_0,k1_tops_1(esk2_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.14/0.41  cnf(c_0_71, plain, (v3_pre_topc(k1_tops_1(X1,X2),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.14/0.41  cnf(c_0_72, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.14/0.41  cnf(c_0_73, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.14/0.41  cnf(c_0_74, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.14/0.41  cnf(c_0_75, plain, (m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.14/0.41  cnf(c_0_76, plain, (r1_tarski(k1_tops_1(X1,X2),X2)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.14/0.41  cnf(c_0_77, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.14/0.41  cnf(c_0_78, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.14/0.41  fof(c_0_79, plain, ![X70, X71, X72]:(~l1_pre_topc(X70)|(~m1_subset_1(X71,k1_zfmisc_1(u1_struct_0(X70)))|(~m1_subset_1(X72,k1_zfmisc_1(u1_struct_0(X70)))|(~r1_tarski(X71,X72)|r1_tarski(k1_tops_1(X70,X71),k1_tops_1(X70,X72)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_tops_1])])])).
% 0.14/0.41  cnf(c_0_80, negated_conjecture, (r1_tarski(esk5_0,esk4_0)|r2_hidden(esk3_0,k1_tops_1(esk2_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.14/0.41  cnf(c_0_81, negated_conjecture, (v3_pre_topc(esk5_0,esk2_0)|r2_hidden(esk3_0,k1_tops_1(esk2_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.14/0.41  fof(c_0_82, plain, ![X40, X41]:(((~m1_subset_1(X41,X40)|r2_hidden(X41,X40)|v1_xboole_0(X40))&(~r2_hidden(X41,X40)|m1_subset_1(X41,X40)|v1_xboole_0(X40)))&((~m1_subset_1(X41,X40)|v1_xboole_0(X41)|~v1_xboole_0(X40))&(~v1_xboole_0(X41)|m1_subset_1(X41,X40)|~v1_xboole_0(X40)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 0.14/0.41  cnf(c_0_83, plain, (r2_hidden(X1,k1_zfmisc_1(X2))|~r2_hidden(X1,k2_tarski(X2,X2))), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 0.14/0.41  cnf(c_0_84, plain, (r2_hidden(X1,k2_tarski(X1,X1))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_68])).
% 0.14/0.41  fof(c_0_85, plain, ![X44]:~v1_xboole_0(k1_zfmisc_1(X44)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).
% 0.14/0.41  fof(c_0_86, plain, ![X45, X46, X47]:(~m1_subset_1(X46,k1_zfmisc_1(X45))|~m1_subset_1(X47,k1_zfmisc_1(X45))|k4_subset_1(X45,X46,X47)=k2_xboole_0(X46,X47)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).
% 0.14/0.41  cnf(c_0_87, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk2_0)))|~v3_pre_topc(X1,esk2_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))|~r2_hidden(esk3_0,X1)|~r1_tarski(X1,esk4_0)), inference(spm,[status(thm)],[c_0_69, c_0_70])).
% 0.14/0.41  cnf(c_0_88, negated_conjecture, (v3_pre_topc(k1_tops_1(esk2_0,esk4_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_73]), c_0_74])])).
% 0.14/0.41  cnf(c_0_89, negated_conjecture, (m1_subset_1(k1_tops_1(esk2_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_72]), c_0_74])])).
% 0.14/0.41  cnf(c_0_90, negated_conjecture, (r1_tarski(k1_tops_1(esk2_0,esk4_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_72]), c_0_74])])).
% 0.14/0.41  cnf(c_0_91, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=X1|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_77, c_0_42])).
% 0.14/0.41  cnf(c_0_92, plain, (r1_tarski(k1_tops_1(X1,k1_xboole_0),k1_xboole_0)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_76, c_0_78])).
% 0.14/0.41  fof(c_0_93, plain, ![X11]:k2_xboole_0(X11,k1_xboole_0)=X11, inference(variable_rename,[status(thm)],[t1_boole])).
% 0.14/0.41  cnf(c_0_94, plain, (r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_79])).
% 0.14/0.41  cnf(c_0_95, negated_conjecture, (r1_tarski(esk5_0,esk4_0)|~v3_pre_topc(X1,esk2_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))|~r2_hidden(esk3_0,X1)|~r1_tarski(X1,esk4_0)), inference(spm,[status(thm)],[c_0_69, c_0_80])).
% 0.14/0.41  fof(c_0_96, plain, ![X42, X43]:(~m1_subset_1(X43,k1_zfmisc_1(X42))|k3_subset_1(X42,X43)=k4_xboole_0(X42,X43)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 0.14/0.41  fof(c_0_97, plain, ![X60, X61]:((~v3_pre_topc(X61,X60)|k2_pre_topc(X60,k7_subset_1(u1_struct_0(X60),k2_struct_0(X60),X61))=k7_subset_1(u1_struct_0(X60),k2_struct_0(X60),X61)|~m1_subset_1(X61,k1_zfmisc_1(u1_struct_0(X60)))|~l1_pre_topc(X60))&(~v2_pre_topc(X60)|k2_pre_topc(X60,k7_subset_1(u1_struct_0(X60),k2_struct_0(X60),X61))!=k7_subset_1(u1_struct_0(X60),k2_struct_0(X60),X61)|v3_pre_topc(X61,X60)|~m1_subset_1(X61,k1_zfmisc_1(u1_struct_0(X60)))|~l1_pre_topc(X60))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t53_pre_topc])])])])).
% 0.14/0.41  cnf(c_0_98, negated_conjecture, (v3_pre_topc(esk5_0,esk2_0)|~v3_pre_topc(X1,esk2_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))|~r2_hidden(esk3_0,X1)|~r1_tarski(X1,esk4_0)), inference(spm,[status(thm)],[c_0_69, c_0_81])).
% 0.14/0.41  fof(c_0_99, plain, ![X58]:(~l1_struct_0(X58)|k2_struct_0(X58)=u1_struct_0(X58)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).
% 0.14/0.41  fof(c_0_100, plain, ![X59]:(~l1_pre_topc(X59)|l1_struct_0(X59)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.14/0.41  fof(c_0_101, plain, ![X48, X49, X50]:(~m1_subset_1(X49,k1_zfmisc_1(X48))|k7_subset_1(X48,X49,X50)=k4_xboole_0(X49,X50)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).
% 0.14/0.41  cnf(c_0_102, plain, (m1_subset_1(X1,X2)|v1_xboole_0(X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_82])).
% 0.14/0.41  cnf(c_0_103, plain, (r2_hidden(X1,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_83, c_0_84])).
% 0.14/0.41  cnf(c_0_104, plain, (~v1_xboole_0(k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_85])).
% 0.14/0.41  fof(c_0_105, plain, ![X51, X52, X53]:(~m1_subset_1(X52,k1_zfmisc_1(X51))|(~m1_subset_1(X53,k1_zfmisc_1(X51))|k3_subset_1(X51,k7_subset_1(X51,X52,X53))=k4_subset_1(X51,k3_subset_1(X51,X52),X53))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t33_subset_1])])])).
% 0.14/0.41  cnf(c_0_106, plain, (k4_subset_1(X2,X1,X3)=k2_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_86])).
% 0.14/0.41  cnf(c_0_107, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_88]), c_0_89]), c_0_90])]), c_0_70])).
% 0.14/0.41  cnf(c_0_108, plain, (k1_tops_1(X1,k1_xboole_0)=k1_xboole_0|~l1_pre_topc(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_92]), c_0_46]), c_0_57])).
% 0.14/0.41  cnf(c_0_109, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_93])).
% 0.14/0.41  fof(c_0_110, plain, ![X18]:r1_xboole_0(X18,k1_xboole_0), inference(variable_rename,[status(thm)],[t65_xboole_1])).
% 0.14/0.41  cnf(c_0_111, negated_conjecture, (r1_tarski(k1_tops_1(esk2_0,X1),k1_tops_1(esk2_0,esk4_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))|~r1_tarski(X1,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_72]), c_0_74])])).
% 0.14/0.41  cnf(c_0_112, negated_conjecture, (r1_tarski(esk5_0,esk4_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_88]), c_0_89]), c_0_90])]), c_0_80])).
% 0.14/0.41  fof(c_0_113, plain, ![X62, X63]:(~l1_pre_topc(X62)|(~m1_subset_1(X63,k1_zfmisc_1(u1_struct_0(X62)))|k1_tops_1(X62,X63)=k3_subset_1(u1_struct_0(X62),k2_pre_topc(X62,k3_subset_1(u1_struct_0(X62),X63))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tops_1])])])).
% 0.14/0.41  cnf(c_0_114, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_96])).
% 0.14/0.41  cnf(c_0_115, plain, (k2_pre_topc(X2,k7_subset_1(u1_struct_0(X2),k2_struct_0(X2),X1))=k7_subset_1(u1_struct_0(X2),k2_struct_0(X2),X1)|~v3_pre_topc(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_97])).
% 0.14/0.41  cnf(c_0_116, negated_conjecture, (v3_pre_topc(esk5_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_81]), c_0_88]), c_0_89]), c_0_90])])).
% 0.14/0.41  cnf(c_0_117, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_99])).
% 0.14/0.41  cnf(c_0_118, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_100])).
% 0.14/0.41  cnf(c_0_119, plain, (k7_subset_1(X2,X1,X3)=k4_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_101])).
% 0.14/0.41  cnf(c_0_120, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_102, c_0_103]), c_0_104])).
% 0.14/0.41  cnf(c_0_121, plain, (k3_subset_1(X2,k7_subset_1(X2,X1,X3))=k4_subset_1(X2,k3_subset_1(X2,X1),X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_105])).
% 0.14/0.41  cnf(c_0_122, negated_conjecture, (k4_subset_1(u1_struct_0(esk2_0),X1,esk5_0)=k2_xboole_0(X1,esk5_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(spm,[status(thm)],[c_0_106, c_0_107])).
% 0.14/0.41  cnf(c_0_123, plain, (m1_subset_1(k1_tops_1(X1,k1_xboole_0),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_75, c_0_78])).
% 0.14/0.41  cnf(c_0_124, negated_conjecture, (k1_tops_1(esk2_0,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_108, c_0_74])).
% 0.14/0.41  cnf(c_0_125, plain, (k2_xboole_0(X1,X2)=X2|~r1_xboole_0(k2_xboole_0(X1,X2),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_109])]), c_0_54])])).
% 0.14/0.41  cnf(c_0_126, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_110])).
% 0.14/0.41  cnf(c_0_127, negated_conjecture, (r1_tarski(k1_tops_1(esk2_0,X1),k1_tops_1(esk2_0,k1_tops_1(esk2_0,esk4_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))|~r1_tarski(X1,k1_tops_1(esk2_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_89]), c_0_74])])).
% 0.14/0.41  cnf(c_0_128, negated_conjecture, (m1_subset_1(k1_tops_1(esk2_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_107]), c_0_74])])).
% 0.14/0.41  cnf(c_0_129, negated_conjecture, (r1_tarski(k1_tops_1(esk2_0,esk5_0),k1_tops_1(esk2_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111, c_0_112]), c_0_107])])).
% 0.14/0.41  cnf(c_0_130, plain, (k1_tops_1(X1,X2)=k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_113])).
% 0.14/0.41  cnf(c_0_131, negated_conjecture, (k3_subset_1(u1_struct_0(esk2_0),esk5_0)=k4_xboole_0(u1_struct_0(esk2_0),esk5_0)), inference(spm,[status(thm)],[c_0_114, c_0_107])).
% 0.14/0.41  cnf(c_0_132, negated_conjecture, (k2_pre_topc(esk2_0,k7_subset_1(u1_struct_0(esk2_0),k2_struct_0(esk2_0),esk5_0))=k7_subset_1(u1_struct_0(esk2_0),k2_struct_0(esk2_0),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115, c_0_107]), c_0_116]), c_0_74])])).
% 0.14/0.41  cnf(c_0_133, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_117, c_0_118])).
% 0.14/0.41  cnf(c_0_134, plain, (k7_subset_1(X1,X1,X2)=k4_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_119, c_0_120])).
% 0.14/0.41  cnf(c_0_135, negated_conjecture, (k4_subset_1(u1_struct_0(esk2_0),k3_subset_1(u1_struct_0(esk2_0),X1),esk5_0)=k3_subset_1(u1_struct_0(esk2_0),k7_subset_1(u1_struct_0(esk2_0),X1,esk5_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(spm,[status(thm)],[c_0_121, c_0_107])).
% 0.14/0.41  cnf(c_0_136, plain, (k3_subset_1(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114, c_0_120]), c_0_57])).
% 0.14/0.41  cnf(c_0_137, negated_conjecture, (k4_subset_1(u1_struct_0(esk2_0),k1_xboole_0,esk5_0)=k2_xboole_0(k1_xboole_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_122, c_0_123]), c_0_124]), c_0_124]), c_0_74])])).
% 0.14/0.41  cnf(c_0_138, plain, (k2_xboole_0(k1_xboole_0,X1)=X1), inference(spm,[status(thm)],[c_0_125, c_0_126])).
% 0.14/0.41  cnf(c_0_139, negated_conjecture, (r1_tarski(k1_tops_1(esk2_0,k1_tops_1(esk2_0,esk5_0)),k1_tops_1(esk2_0,k1_tops_1(esk2_0,esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_127, c_0_128]), c_0_129])])).
% 0.14/0.41  cnf(c_0_140, negated_conjecture, (k3_subset_1(u1_struct_0(esk2_0),k2_pre_topc(esk2_0,k4_xboole_0(u1_struct_0(esk2_0),esk5_0)))=k1_tops_1(esk2_0,esk5_0)), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_130, c_0_107]), c_0_74])]), c_0_131])).
% 0.14/0.41  cnf(c_0_141, negated_conjecture, (k2_pre_topc(esk2_0,k4_xboole_0(u1_struct_0(esk2_0),esk5_0))=k4_xboole_0(u1_struct_0(esk2_0),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_132, c_0_133]), c_0_134]), c_0_134]), c_0_74])])).
% 0.14/0.41  cnf(c_0_142, negated_conjecture, (k3_subset_1(u1_struct_0(esk2_0),k4_xboole_0(u1_struct_0(esk2_0),esk5_0))=esk5_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_135, c_0_120]), c_0_136]), c_0_137]), c_0_138]), c_0_134])).
% 0.14/0.41  cnf(c_0_143, negated_conjecture, (r2_hidden(esk3_0,esk5_0)|r2_hidden(esk3_0,k1_tops_1(esk2_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.14/0.41  cnf(c_0_144, negated_conjecture, (r2_hidden(X1,k1_tops_1(esk2_0,k1_tops_1(esk2_0,esk4_0)))|~r2_hidden(X1,k1_tops_1(esk2_0,k1_tops_1(esk2_0,esk5_0)))), inference(spm,[status(thm)],[c_0_64, c_0_139])).
% 0.14/0.41  cnf(c_0_145, negated_conjecture, (k1_tops_1(esk2_0,esk5_0)=esk5_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_140, c_0_141]), c_0_142])).
% 0.14/0.41  cnf(c_0_146, negated_conjecture, (r2_hidden(esk3_0,esk5_0)|~v3_pre_topc(X1,esk2_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))|~r2_hidden(esk3_0,X1)|~r1_tarski(X1,esk4_0)), inference(spm,[status(thm)],[c_0_69, c_0_143])).
% 0.14/0.41  cnf(c_0_147, negated_conjecture, (r1_tarski(k1_tops_1(esk2_0,k1_tops_1(esk2_0,esk4_0)),k1_tops_1(esk2_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_89]), c_0_74])])).
% 0.14/0.41  cnf(c_0_148, negated_conjecture, (r2_hidden(X1,k1_tops_1(esk2_0,k1_tops_1(esk2_0,esk4_0)))|~r2_hidden(X1,esk5_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_144, c_0_145]), c_0_145])).
% 0.14/0.41  cnf(c_0_149, negated_conjecture, (r2_hidden(esk3_0,esk5_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_146, c_0_88]), c_0_89]), c_0_90])]), c_0_143])).
% 0.14/0.41  cnf(c_0_150, negated_conjecture, (r2_hidden(X1,k1_tops_1(esk2_0,esk4_0))|~r2_hidden(X1,k1_tops_1(esk2_0,k1_tops_1(esk2_0,esk4_0)))), inference(spm,[status(thm)],[c_0_64, c_0_147])).
% 0.14/0.41  cnf(c_0_151, negated_conjecture, (r2_hidden(esk3_0,k1_tops_1(esk2_0,k1_tops_1(esk2_0,esk4_0)))), inference(spm,[status(thm)],[c_0_148, c_0_149])).
% 0.14/0.41  cnf(c_0_152, negated_conjecture, (r2_hidden(esk3_0,k1_tops_1(esk2_0,esk4_0))), inference(spm,[status(thm)],[c_0_150, c_0_151])).
% 0.14/0.41  cnf(c_0_153, negated_conjecture, (~v3_pre_topc(X1,esk2_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))|~r2_hidden(esk3_0,X1)|~r1_tarski(X1,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_69, c_0_152])])).
% 0.14/0.41  cnf(c_0_154, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_153, c_0_116]), c_0_107]), c_0_149]), c_0_112])]), ['proof']).
% 0.14/0.41  # SZS output end CNFRefutation
% 0.14/0.41  # Proof object total steps             : 155
% 0.14/0.41  # Proof object clause steps            : 96
% 0.14/0.41  # Proof object formula steps           : 59
% 0.14/0.41  # Proof object conjectures             : 45
% 0.14/0.41  # Proof object clause conjectures      : 42
% 0.14/0.41  # Proof object formula conjectures     : 3
% 0.14/0.41  # Proof object initial clauses used    : 38
% 0.14/0.41  # Proof object initial formulas used   : 29
% 0.14/0.41  # Proof object generating inferences   : 48
% 0.14/0.41  # Proof object simplifying inferences  : 81
% 0.14/0.41  # Training examples: 0 positive, 0 negative
% 0.14/0.41  # Parsed axioms                        : 33
% 0.14/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.41  # Initial clauses                      : 51
% 0.14/0.41  # Removed in clause preprocessing      : 2
% 0.14/0.41  # Initial clauses in saturation        : 49
% 0.14/0.41  # Processed clauses                    : 613
% 0.14/0.41  # ...of these trivial                  : 6
% 0.14/0.41  # ...subsumed                          : 145
% 0.14/0.41  # ...remaining for further processing  : 462
% 0.14/0.41  # Other redundant clauses eliminated   : 11
% 0.14/0.41  # Clauses deleted for lack of memory   : 0
% 0.14/0.41  # Backward-subsumed                    : 13
% 0.14/0.41  # Backward-rewritten                   : 81
% 0.14/0.41  # Generated clauses                    : 1433
% 0.14/0.41  # ...of the previous two non-trivial   : 1161
% 0.14/0.41  # Contextual simplify-reflections      : 3
% 0.14/0.41  # Paramodulations                      : 1411
% 0.14/0.41  # Factorizations                       : 10
% 0.14/0.41  # Equation resolutions                 : 12
% 0.14/0.41  # Propositional unsat checks           : 0
% 0.14/0.41  #    Propositional check models        : 0
% 0.14/0.41  #    Propositional check unsatisfiable : 0
% 0.14/0.41  #    Propositional clauses             : 0
% 0.14/0.41  #    Propositional clauses after purity: 0
% 0.14/0.41  #    Propositional unsat core size     : 0
% 0.14/0.41  #    Propositional preprocessing time  : 0.000
% 0.14/0.41  #    Propositional encoding time       : 0.000
% 0.14/0.41  #    Propositional solver time         : 0.000
% 0.14/0.41  #    Success case prop preproc time    : 0.000
% 0.14/0.41  #    Success case prop encoding time   : 0.000
% 0.14/0.41  #    Success case prop solver time     : 0.000
% 0.14/0.41  # Current number of processed clauses  : 314
% 0.14/0.41  #    Positive orientable unit clauses  : 121
% 0.14/0.41  #    Positive unorientable unit clauses: 0
% 0.14/0.41  #    Negative unit clauses             : 6
% 0.14/0.41  #    Non-unit-clauses                  : 187
% 0.14/0.41  # Current number of unprocessed clauses: 619
% 0.14/0.41  # ...number of literals in the above   : 1472
% 0.14/0.41  # Current number of archived formulas  : 0
% 0.14/0.41  # Current number of archived clauses   : 145
% 0.14/0.41  # Clause-clause subsumption calls (NU) : 4997
% 0.14/0.41  # Rec. Clause-clause subsumption calls : 3573
% 0.14/0.41  # Non-unit clause-clause subsumptions  : 132
% 0.14/0.41  # Unit Clause-clause subsumption calls : 575
% 0.14/0.41  # Rewrite failures with RHS unbound    : 0
% 0.14/0.41  # BW rewrite match attempts            : 194
% 0.14/0.41  # BW rewrite match successes           : 17
% 0.14/0.41  # Condensation attempts                : 0
% 0.14/0.41  # Condensation successes               : 0
% 0.14/0.41  # Termbank termtop insertions          : 26192
% 0.14/0.41  
% 0.14/0.41  # -------------------------------------------------
% 0.14/0.41  # User time                : 0.051 s
% 0.14/0.41  # System time              : 0.001 s
% 0.14/0.41  # Total time               : 0.052 s
% 0.14/0.41  # Maximum resident set size: 1612 pages
%------------------------------------------------------------------------------
