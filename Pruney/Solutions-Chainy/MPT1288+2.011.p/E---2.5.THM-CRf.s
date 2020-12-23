%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:12:44 EST 2020

% Result     : Theorem 0.38s
% Output     : CNFRefutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 147 expanded)
%              Number of clauses        :   39 (  56 expanded)
%              Number of leaves         :   17 (  37 expanded)
%              Depth                    :   16
%              Number of atoms          :  233 ( 522 expanded)
%              Number of equality atoms :   34 (  85 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal clause size      :   13 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t106_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k4_xboole_0(X2,X3))
     => ( r1_tarski(X1,X2)
        & r1_xboole_0(X1,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(redefinition_k7_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k7_subset_1(X1,X2,X3) = k4_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(t74_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k1_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).

fof(t67_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X1,X3)
        & r1_xboole_0(X2,X3) )
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_xboole_1)).

fof(t110_tops_1,conjecture,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v4_tops_1(X2,X1)
           => k1_tops_1(X1,k2_tops_1(X1,X2)) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t110_tops_1)).

fof(t44_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => r1_tarski(k1_tops_1(X1,X2),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

fof(dt_k2_tops_1,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k2_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

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

fof(projectivity_k1_tops_1,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => k1_tops_1(X1,k1_tops_1(X1,X2)) = k1_tops_1(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',projectivity_k1_tops_1)).

fof(dt_k1_tops_1,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tops_1)).

fof(t10_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_tarski(X1,k2_xboole_0(X3,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

fof(redefinition_k4_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => k4_subset_1(X1,X2,X3) = k2_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(t65_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k2_pre_topc(X1,X2) = k4_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(dt_k2_pre_topc,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(d6_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v4_tops_1(X2,X1)
          <=> ( r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X2)),X2)
              & r1_tarski(X2,k2_pre_topc(X1,k1_tops_1(X1,X2))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_tops_1)).

fof(c_0_17,plain,(
    ! [X8,X9,X10] :
      ( ( r1_tarski(X8,X9)
        | ~ r1_tarski(X8,k4_xboole_0(X9,X10)) )
      & ( r1_xboole_0(X8,X10)
        | ~ r1_tarski(X8,k4_xboole_0(X9,X10)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t106_xboole_1])])])).

fof(c_0_18,plain,(
    ! [X6,X7] : k4_xboole_0(X6,X7) = k5_xboole_0(X6,k3_xboole_0(X6,X7)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_19,plain,(
    ! [X23,X24,X25] :
      ( ~ m1_subset_1(X24,k1_zfmisc_1(X23))
      | k7_subset_1(X23,X24,X25) = k4_xboole_0(X24,X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).

cnf(c_0_20,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_tarski(X1,k4_xboole_0(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_21,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_22,plain,
    ( k7_subset_1(X2,X1,X3) = k4_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_23,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_tarski(X1,k5_xboole_0(X3,k3_xboole_0(X3,X2))) ),
    inference(rw,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_24,plain,
    ( k7_subset_1(X2,X1,X3) = k5_xboole_0(X1,k3_xboole_0(X1,X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_22,c_0_21])).

fof(c_0_25,plain,(
    ! [X50,X51] :
      ( ~ l1_pre_topc(X50)
      | ~ m1_subset_1(X51,k1_zfmisc_1(u1_struct_0(X50)))
      | k1_tops_1(X50,X51) = k7_subset_1(u1_struct_0(X50),X51,k2_tops_1(X50,X51)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t74_tops_1])])])).

fof(c_0_26,plain,(
    ! [X17,X18,X19] :
      ( ~ r1_tarski(X17,X18)
      | ~ r1_tarski(X17,X19)
      | ~ r1_xboole_0(X18,X19)
      | X17 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t67_xboole_1])])).

cnf(c_0_27,plain,
    ( r1_xboole_0(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X4))
    | ~ r1_tarski(X1,k7_subset_1(X4,X3,X2)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_28,plain,
    ( k1_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_29,negated_conjecture,(
    ~ ! [X1] :
        ( ( v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( v4_tops_1(X2,X1)
             => k1_tops_1(X1,k2_tops_1(X1,X2)) = k1_xboole_0 ) ) ) ),
    inference(assume_negation,[status(cth)],[t110_tops_1])).

cnf(c_0_30,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_31,plain,
    ( r1_xboole_0(X1,k2_tops_1(X2,X3))
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r1_tarski(X1,k1_tops_1(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

fof(c_0_32,negated_conjecture,
    ( v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & v4_tops_1(esk2_0,esk1_0)
    & k1_tops_1(esk1_0,k2_tops_1(esk1_0,esk2_0)) != k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_29])])])).

fof(c_0_33,plain,(
    ! [X40,X41] :
      ( ~ l1_pre_topc(X40)
      | ~ m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(X40)))
      | r1_tarski(k1_tops_1(X40,X41),X41) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_tops_1])])])).

fof(c_0_34,plain,(
    ! [X34,X35] :
      ( ~ l1_pre_topc(X34)
      | ~ m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X34)))
      | m1_subset_1(k2_tops_1(X34,X35),k1_zfmisc_1(u1_struct_0(X34))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_tops_1])])).

cnf(c_0_35,plain,
    ( X1 = k1_xboole_0
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r1_tarski(X1,k2_tops_1(X2,X3))
    | ~ r1_tarski(X4,k1_tops_1(X2,X3))
    | ~ r1_tarski(X1,X4) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_36,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_37,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_38,plain,
    ( r1_tarski(k1_tops_1(X1,X2),X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_39,plain,
    ( m1_subset_1(k2_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_40,negated_conjecture,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k2_tops_1(esk1_0,esk2_0))
    | ~ r1_tarski(X2,k1_tops_1(esk1_0,esk2_0))
    | ~ r1_tarski(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37])])).

cnf(c_0_41,plain,
    ( r1_tarski(k1_tops_1(X1,k2_tops_1(X1,X2)),k2_tops_1(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_42,negated_conjecture,
    ( k1_tops_1(esk1_0,k2_tops_1(esk1_0,esk2_0)) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_43,plain,(
    ! [X42,X43,X44] :
      ( ~ l1_pre_topc(X42)
      | ~ m1_subset_1(X43,k1_zfmisc_1(u1_struct_0(X42)))
      | ~ m1_subset_1(X44,k1_zfmisc_1(u1_struct_0(X42)))
      | ~ r1_tarski(X43,X44)
      | r1_tarski(k1_tops_1(X42,X43),k1_tops_1(X42,X44)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_tops_1])])])).

cnf(c_0_44,negated_conjecture,
    ( ~ r1_tarski(k1_tops_1(esk1_0,k2_tops_1(esk1_0,esk2_0)),X1)
    | ~ r1_tarski(X1,k1_tops_1(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_37]),c_0_36])]),c_0_42])).

cnf(c_0_45,plain,
    ( r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

fof(c_0_46,plain,(
    ! [X38,X39] :
      ( ~ l1_pre_topc(X38)
      | ~ m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(X38)))
      | k1_tops_1(X38,k1_tops_1(X38,X39)) = k1_tops_1(X38,X39) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[projectivity_k1_tops_1])])).

fof(c_0_47,plain,(
    ! [X32,X33] :
      ( ~ l1_pre_topc(X32)
      | ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))
      | m1_subset_1(k1_tops_1(X32,X33),k1_zfmisc_1(u1_struct_0(X32))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_tops_1])])).

cnf(c_0_48,negated_conjecture,
    ( ~ m1_subset_1(k2_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_tarski(k1_tops_1(esk1_0,X1),k1_tops_1(esk1_0,esk2_0))
    | ~ r1_tarski(k2_tops_1(esk1_0,esk2_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_37])])).

cnf(c_0_49,plain,
    ( k1_tops_1(X1,k1_tops_1(X1,X2)) = k1_tops_1(X1,X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_50,plain,
    ( m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_51,negated_conjecture,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_tarski(k1_tops_1(esk1_0,X1),k1_tops_1(esk1_0,esk2_0))
    | ~ r1_tarski(k2_tops_1(esk1_0,esk2_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_39]),c_0_37]),c_0_36])])).

cnf(c_0_52,plain,
    ( r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(k1_tops_1(X1,X2),X3) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_49]),c_0_50])).

fof(c_0_53,plain,(
    ! [X11,X12,X13] :
      ( ~ r1_tarski(X11,X12)
      | r1_tarski(X11,k2_xboole_0(X13,X12)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_xboole_1])])).

fof(c_0_54,plain,(
    ! [X20,X21,X22] :
      ( ~ m1_subset_1(X21,k1_zfmisc_1(X20))
      | ~ m1_subset_1(X22,k1_zfmisc_1(X20))
      | k4_subset_1(X20,X21,X22) = k2_xboole_0(X21,X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).

fof(c_0_55,plain,(
    ! [X48,X49] :
      ( ~ l1_pre_topc(X48)
      | ~ m1_subset_1(X49,k1_zfmisc_1(u1_struct_0(X48)))
      | k2_pre_topc(X48,X49) = k4_subset_1(u1_struct_0(X48),X49,k2_tops_1(X48,X49)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_tops_1])])])).

cnf(c_0_56,negated_conjecture,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_tarski(k2_tops_1(esk1_0,esk2_0),X1)
    | ~ r1_tarski(k1_tops_1(esk1_0,X1),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_37]),c_0_36])])).

cnf(c_0_57,plain,
    ( r1_tarski(X1,k2_xboole_0(X3,X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_58,plain,
    ( k4_subset_1(X2,X1,X3) = k2_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_59,plain,
    ( k2_pre_topc(X1,X2) = k4_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

fof(c_0_60,plain,(
    ! [X4,X5] :
      ( ( r1_tarski(X4,X5)
        | X4 != X5 )
      & ( r1_tarski(X5,X4)
        | X4 != X5 )
      & ( ~ r1_tarski(X4,X5)
        | ~ r1_tarski(X5,X4)
        | X4 = X5 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_61,negated_conjecture,
    ( ~ m1_subset_1(k2_xboole_0(X1,X2),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_tarski(k1_tops_1(esk1_0,k2_xboole_0(X1,X2)),esk2_0)
    | ~ r1_tarski(k2_tops_1(esk1_0,esk2_0),X2) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_62,plain,
    ( k2_xboole_0(X1,k2_tops_1(X2,X1)) = k2_pre_topc(X2,X1)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_39])).

cnf(c_0_63,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_64,negated_conjecture,
    ( ~ l1_pre_topc(X1)
    | ~ m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(k1_tops_1(esk1_0,k2_pre_topc(X1,X2)),esk2_0)
    | ~ r1_tarski(k2_tops_1(esk1_0,esk2_0),k2_tops_1(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_65,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_63])).

fof(c_0_66,plain,(
    ! [X26,X27] :
      ( ~ l1_pre_topc(X26)
      | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))
      | m1_subset_1(k2_pre_topc(X26,X27),k1_zfmisc_1(u1_struct_0(X26))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).

cnf(c_0_67,negated_conjecture,
    ( ~ m1_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_tarski(k1_tops_1(esk1_0,k2_pre_topc(esk1_0,esk2_0)),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_37]),c_0_36])])).

cnf(c_0_68,plain,
    ( m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

fof(c_0_69,plain,(
    ! [X30,X31] :
      ( ( r1_tarski(k1_tops_1(X30,k2_pre_topc(X30,X31)),X31)
        | ~ v4_tops_1(X31,X30)
        | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))
        | ~ l1_pre_topc(X30) )
      & ( r1_tarski(X31,k2_pre_topc(X30,k1_tops_1(X30,X31)))
        | ~ v4_tops_1(X31,X30)
        | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))
        | ~ l1_pre_topc(X30) )
      & ( ~ r1_tarski(k1_tops_1(X30,k2_pre_topc(X30,X31)),X31)
        | ~ r1_tarski(X31,k2_pre_topc(X30,k1_tops_1(X30,X31)))
        | v4_tops_1(X31,X30)
        | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))
        | ~ l1_pre_topc(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_tops_1])])])])).

cnf(c_0_70,negated_conjecture,
    ( ~ r1_tarski(k1_tops_1(esk1_0,k2_pre_topc(esk1_0,esk2_0)),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_37]),c_0_36])])).

cnf(c_0_71,plain,
    ( r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X2)),X2)
    | ~ v4_tops_1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_72,negated_conjecture,
    ( v4_tops_1(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_73,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_72]),c_0_37]),c_0_36])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:00:34 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.38/0.54  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.38/0.54  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.38/0.54  #
% 0.38/0.54  # Preprocessing time       : 0.028 s
% 0.38/0.54  # Presaturation interreduction done
% 0.38/0.54  
% 0.38/0.54  # Proof found!
% 0.38/0.54  # SZS status Theorem
% 0.38/0.54  # SZS output start CNFRefutation
% 0.38/0.54  fof(t106_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k4_xboole_0(X2,X3))=>(r1_tarski(X1,X2)&r1_xboole_0(X1,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 0.38/0.54  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.38/0.54  fof(redefinition_k7_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k7_subset_1(X1,X2,X3)=k4_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 0.38/0.54  fof(t74_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k1_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_tops_1)).
% 0.38/0.54  fof(t67_xboole_1, axiom, ![X1, X2, X3]:(((r1_tarski(X1,X2)&r1_tarski(X1,X3))&r1_xboole_0(X2,X3))=>X1=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_xboole_1)).
% 0.38/0.54  fof(t110_tops_1, conjecture, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v4_tops_1(X2,X1)=>k1_tops_1(X1,k2_tops_1(X1,X2))=k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t110_tops_1)).
% 0.38/0.54  fof(t44_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>r1_tarski(k1_tops_1(X1,X2),X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_1)).
% 0.38/0.54  fof(dt_k2_tops_1, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>m1_subset_1(k2_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 0.38/0.54  fof(t48_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(r1_tarski(X2,X3)=>r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_tops_1)).
% 0.38/0.54  fof(projectivity_k1_tops_1, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>k1_tops_1(X1,k1_tops_1(X1,X2))=k1_tops_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', projectivity_k1_tops_1)).
% 0.38/0.54  fof(dt_k1_tops_1, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tops_1)).
% 0.38/0.54  fof(t10_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_tarski(X1,k2_xboole_0(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_xboole_1)).
% 0.38/0.54  fof(redefinition_k4_subset_1, axiom, ![X1, X2, X3]:((m1_subset_1(X2,k1_zfmisc_1(X1))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>k4_subset_1(X1,X2,X3)=k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 0.38/0.54  fof(t65_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k2_pre_topc(X1,X2)=k4_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tops_1)).
% 0.38/0.54  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.38/0.54  fof(dt_k2_pre_topc, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 0.38/0.54  fof(d6_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v4_tops_1(X2,X1)<=>(r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X2)),X2)&r1_tarski(X2,k2_pre_topc(X1,k1_tops_1(X1,X2))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_tops_1)).
% 0.38/0.54  fof(c_0_17, plain, ![X8, X9, X10]:((r1_tarski(X8,X9)|~r1_tarski(X8,k4_xboole_0(X9,X10)))&(r1_xboole_0(X8,X10)|~r1_tarski(X8,k4_xboole_0(X9,X10)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t106_xboole_1])])])).
% 0.38/0.54  fof(c_0_18, plain, ![X6, X7]:k4_xboole_0(X6,X7)=k5_xboole_0(X6,k3_xboole_0(X6,X7)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.38/0.54  fof(c_0_19, plain, ![X23, X24, X25]:(~m1_subset_1(X24,k1_zfmisc_1(X23))|k7_subset_1(X23,X24,X25)=k4_xboole_0(X24,X25)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).
% 0.38/0.54  cnf(c_0_20, plain, (r1_xboole_0(X1,X2)|~r1_tarski(X1,k4_xboole_0(X3,X2))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.38/0.54  cnf(c_0_21, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.38/0.54  cnf(c_0_22, plain, (k7_subset_1(X2,X1,X3)=k4_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.38/0.54  cnf(c_0_23, plain, (r1_xboole_0(X1,X2)|~r1_tarski(X1,k5_xboole_0(X3,k3_xboole_0(X3,X2)))), inference(rw,[status(thm)],[c_0_20, c_0_21])).
% 0.38/0.54  cnf(c_0_24, plain, (k7_subset_1(X2,X1,X3)=k5_xboole_0(X1,k3_xboole_0(X1,X3))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_22, c_0_21])).
% 0.38/0.54  fof(c_0_25, plain, ![X50, X51]:(~l1_pre_topc(X50)|(~m1_subset_1(X51,k1_zfmisc_1(u1_struct_0(X50)))|k1_tops_1(X50,X51)=k7_subset_1(u1_struct_0(X50),X51,k2_tops_1(X50,X51)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t74_tops_1])])])).
% 0.38/0.54  fof(c_0_26, plain, ![X17, X18, X19]:(~r1_tarski(X17,X18)|~r1_tarski(X17,X19)|~r1_xboole_0(X18,X19)|X17=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t67_xboole_1])])).
% 0.38/0.54  cnf(c_0_27, plain, (r1_xboole_0(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(X4))|~r1_tarski(X1,k7_subset_1(X4,X3,X2))), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.38/0.54  cnf(c_0_28, plain, (k1_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.38/0.54  fof(c_0_29, negated_conjecture, ~(![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v4_tops_1(X2,X1)=>k1_tops_1(X1,k2_tops_1(X1,X2))=k1_xboole_0)))), inference(assume_negation,[status(cth)],[t110_tops_1])).
% 0.38/0.54  cnf(c_0_30, plain, (X1=k1_xboole_0|~r1_tarski(X1,X2)|~r1_tarski(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.38/0.54  cnf(c_0_31, plain, (r1_xboole_0(X1,k2_tops_1(X2,X3))|~l1_pre_topc(X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~r1_tarski(X1,k1_tops_1(X2,X3))), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.38/0.54  fof(c_0_32, negated_conjecture, ((v2_pre_topc(esk1_0)&l1_pre_topc(esk1_0))&(m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&(v4_tops_1(esk2_0,esk1_0)&k1_tops_1(esk1_0,k2_tops_1(esk1_0,esk2_0))!=k1_xboole_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_29])])])).
% 0.38/0.54  fof(c_0_33, plain, ![X40, X41]:(~l1_pre_topc(X40)|(~m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(X40)))|r1_tarski(k1_tops_1(X40,X41),X41))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_tops_1])])])).
% 0.38/0.54  fof(c_0_34, plain, ![X34, X35]:(~l1_pre_topc(X34)|~m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X34)))|m1_subset_1(k2_tops_1(X34,X35),k1_zfmisc_1(u1_struct_0(X34)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_tops_1])])).
% 0.38/0.54  cnf(c_0_35, plain, (X1=k1_xboole_0|~l1_pre_topc(X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~r1_tarski(X1,k2_tops_1(X2,X3))|~r1_tarski(X4,k1_tops_1(X2,X3))|~r1_tarski(X1,X4)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.38/0.54  cnf(c_0_36, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.38/0.54  cnf(c_0_37, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.38/0.54  cnf(c_0_38, plain, (r1_tarski(k1_tops_1(X1,X2),X2)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.38/0.54  cnf(c_0_39, plain, (m1_subset_1(k2_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.38/0.54  cnf(c_0_40, negated_conjecture, (X1=k1_xboole_0|~r1_tarski(X1,k2_tops_1(esk1_0,esk2_0))|~r1_tarski(X2,k1_tops_1(esk1_0,esk2_0))|~r1_tarski(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_37])])).
% 0.38/0.54  cnf(c_0_41, plain, (r1_tarski(k1_tops_1(X1,k2_tops_1(X1,X2)),k2_tops_1(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.38/0.54  cnf(c_0_42, negated_conjecture, (k1_tops_1(esk1_0,k2_tops_1(esk1_0,esk2_0))!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.38/0.54  fof(c_0_43, plain, ![X42, X43, X44]:(~l1_pre_topc(X42)|(~m1_subset_1(X43,k1_zfmisc_1(u1_struct_0(X42)))|(~m1_subset_1(X44,k1_zfmisc_1(u1_struct_0(X42)))|(~r1_tarski(X43,X44)|r1_tarski(k1_tops_1(X42,X43),k1_tops_1(X42,X44)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_tops_1])])])).
% 0.38/0.54  cnf(c_0_44, negated_conjecture, (~r1_tarski(k1_tops_1(esk1_0,k2_tops_1(esk1_0,esk2_0)),X1)|~r1_tarski(X1,k1_tops_1(esk1_0,esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_37]), c_0_36])]), c_0_42])).
% 0.38/0.54  cnf(c_0_45, plain, (r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.38/0.54  fof(c_0_46, plain, ![X38, X39]:(~l1_pre_topc(X38)|~m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(X38)))|k1_tops_1(X38,k1_tops_1(X38,X39))=k1_tops_1(X38,X39)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[projectivity_k1_tops_1])])).
% 0.38/0.54  fof(c_0_47, plain, ![X32, X33]:(~l1_pre_topc(X32)|~m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))|m1_subset_1(k1_tops_1(X32,X33),k1_zfmisc_1(u1_struct_0(X32)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_tops_1])])).
% 0.38/0.54  cnf(c_0_48, negated_conjecture, (~m1_subset_1(k2_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))|~r1_tarski(k1_tops_1(esk1_0,X1),k1_tops_1(esk1_0,esk2_0))|~r1_tarski(k2_tops_1(esk1_0,esk2_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_37])])).
% 0.38/0.54  cnf(c_0_49, plain, (k1_tops_1(X1,k1_tops_1(X1,X2))=k1_tops_1(X1,X2)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.38/0.54  cnf(c_0_50, plain, (m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.38/0.54  cnf(c_0_51, negated_conjecture, (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))|~r1_tarski(k1_tops_1(esk1_0,X1),k1_tops_1(esk1_0,esk2_0))|~r1_tarski(k2_tops_1(esk1_0,esk2_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_39]), c_0_37]), c_0_36])])).
% 0.38/0.54  cnf(c_0_52, plain, (r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3))|~l1_pre_topc(X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(k1_tops_1(X1,X2),X3)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_49]), c_0_50])).
% 0.38/0.54  fof(c_0_53, plain, ![X11, X12, X13]:(~r1_tarski(X11,X12)|r1_tarski(X11,k2_xboole_0(X13,X12))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_xboole_1])])).
% 0.38/0.54  fof(c_0_54, plain, ![X20, X21, X22]:(~m1_subset_1(X21,k1_zfmisc_1(X20))|~m1_subset_1(X22,k1_zfmisc_1(X20))|k4_subset_1(X20,X21,X22)=k2_xboole_0(X21,X22)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).
% 0.38/0.54  fof(c_0_55, plain, ![X48, X49]:(~l1_pre_topc(X48)|(~m1_subset_1(X49,k1_zfmisc_1(u1_struct_0(X48)))|k2_pre_topc(X48,X49)=k4_subset_1(u1_struct_0(X48),X49,k2_tops_1(X48,X49)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_tops_1])])])).
% 0.38/0.54  cnf(c_0_56, negated_conjecture, (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))|~r1_tarski(k2_tops_1(esk1_0,esk2_0),X1)|~r1_tarski(k1_tops_1(esk1_0,X1),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_37]), c_0_36])])).
% 0.38/0.54  cnf(c_0_57, plain, (r1_tarski(X1,k2_xboole_0(X3,X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.38/0.54  cnf(c_0_58, plain, (k4_subset_1(X2,X1,X3)=k2_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.38/0.54  cnf(c_0_59, plain, (k2_pre_topc(X1,X2)=k4_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.38/0.54  fof(c_0_60, plain, ![X4, X5]:(((r1_tarski(X4,X5)|X4!=X5)&(r1_tarski(X5,X4)|X4!=X5))&(~r1_tarski(X4,X5)|~r1_tarski(X5,X4)|X4=X5)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.38/0.54  cnf(c_0_61, negated_conjecture, (~m1_subset_1(k2_xboole_0(X1,X2),k1_zfmisc_1(u1_struct_0(esk1_0)))|~r1_tarski(k1_tops_1(esk1_0,k2_xboole_0(X1,X2)),esk2_0)|~r1_tarski(k2_tops_1(esk1_0,esk2_0),X2)), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.38/0.54  cnf(c_0_62, plain, (k2_xboole_0(X1,k2_tops_1(X2,X1))=k2_pre_topc(X2,X1)|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_39])).
% 0.38/0.54  cnf(c_0_63, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.38/0.54  cnf(c_0_64, negated_conjecture, (~l1_pre_topc(X1)|~m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(k1_tops_1(esk1_0,k2_pre_topc(X1,X2)),esk2_0)|~r1_tarski(k2_tops_1(esk1_0,esk2_0),k2_tops_1(X1,X2))), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 0.38/0.54  cnf(c_0_65, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_63])).
% 0.38/0.54  fof(c_0_66, plain, ![X26, X27]:(~l1_pre_topc(X26)|~m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))|m1_subset_1(k2_pre_topc(X26,X27),k1_zfmisc_1(u1_struct_0(X26)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).
% 0.38/0.54  cnf(c_0_67, negated_conjecture, (~m1_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))|~r1_tarski(k1_tops_1(esk1_0,k2_pre_topc(esk1_0,esk2_0)),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_37]), c_0_36])])).
% 0.38/0.54  cnf(c_0_68, plain, (m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_66])).
% 0.38/0.54  fof(c_0_69, plain, ![X30, X31]:(((r1_tarski(k1_tops_1(X30,k2_pre_topc(X30,X31)),X31)|~v4_tops_1(X31,X30)|~m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))|~l1_pre_topc(X30))&(r1_tarski(X31,k2_pre_topc(X30,k1_tops_1(X30,X31)))|~v4_tops_1(X31,X30)|~m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))|~l1_pre_topc(X30)))&(~r1_tarski(k1_tops_1(X30,k2_pre_topc(X30,X31)),X31)|~r1_tarski(X31,k2_pre_topc(X30,k1_tops_1(X30,X31)))|v4_tops_1(X31,X30)|~m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))|~l1_pre_topc(X30))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_tops_1])])])])).
% 0.38/0.54  cnf(c_0_70, negated_conjecture, (~r1_tarski(k1_tops_1(esk1_0,k2_pre_topc(esk1_0,esk2_0)),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_37]), c_0_36])])).
% 0.38/0.54  cnf(c_0_71, plain, (r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X2)),X2)|~v4_tops_1(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_69])).
% 0.38/0.54  cnf(c_0_72, negated_conjecture, (v4_tops_1(esk2_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.38/0.54  cnf(c_0_73, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_71]), c_0_72]), c_0_37]), c_0_36])]), ['proof']).
% 0.38/0.54  # SZS output end CNFRefutation
% 0.38/0.54  # Proof object total steps             : 74
% 0.38/0.54  # Proof object clause steps            : 39
% 0.38/0.54  # Proof object formula steps           : 35
% 0.38/0.54  # Proof object conjectures             : 17
% 0.38/0.54  # Proof object clause conjectures      : 14
% 0.38/0.54  # Proof object formula conjectures     : 3
% 0.38/0.54  # Proof object initial clauses used    : 20
% 0.38/0.54  # Proof object initial formulas used   : 17
% 0.38/0.54  # Proof object generating inferences   : 16
% 0.38/0.54  # Proof object simplifying inferences  : 29
% 0.38/0.54  # Training examples: 0 positive, 0 negative
% 0.38/0.54  # Parsed axioms                        : 21
% 0.38/0.54  # Removed by relevancy pruning/SinE    : 0
% 0.38/0.54  # Initial clauses                      : 30
% 0.38/0.54  # Removed in clause preprocessing      : 1
% 0.38/0.54  # Initial clauses in saturation        : 29
% 0.38/0.54  # Processed clauses                    : 1629
% 0.38/0.54  # ...of these trivial                  : 2
% 0.38/0.54  # ...subsumed                          : 1037
% 0.38/0.54  # ...remaining for further processing  : 590
% 0.38/0.54  # Other redundant clauses eliminated   : 2
% 0.38/0.54  # Clauses deleted for lack of memory   : 0
% 0.38/0.54  # Backward-subsumed                    : 55
% 0.38/0.54  # Backward-rewritten                   : 16
% 0.38/0.54  # Generated clauses                    : 5699
% 0.38/0.54  # ...of the previous two non-trivial   : 5127
% 0.38/0.54  # Contextual simplify-reflections      : 17
% 0.38/0.54  # Paramodulations                      : 5697
% 0.38/0.54  # Factorizations                       : 0
% 0.38/0.54  # Equation resolutions                 : 2
% 0.38/0.54  # Propositional unsat checks           : 0
% 0.38/0.54  #    Propositional check models        : 0
% 0.38/0.54  #    Propositional check unsatisfiable : 0
% 0.38/0.54  #    Propositional clauses             : 0
% 0.38/0.54  #    Propositional clauses after purity: 0
% 0.38/0.54  #    Propositional unsat core size     : 0
% 0.38/0.54  #    Propositional preprocessing time  : 0.000
% 0.38/0.54  #    Propositional encoding time       : 0.000
% 0.38/0.54  #    Propositional solver time         : 0.000
% 0.38/0.54  #    Success case prop preproc time    : 0.000
% 0.38/0.54  #    Success case prop encoding time   : 0.000
% 0.38/0.54  #    Success case prop solver time     : 0.000
% 0.38/0.54  # Current number of processed clauses  : 489
% 0.38/0.54  #    Positive orientable unit clauses  : 28
% 0.38/0.54  #    Positive unorientable unit clauses: 0
% 0.38/0.54  #    Negative unit clauses             : 8
% 0.38/0.54  #    Non-unit-clauses                  : 453
% 0.38/0.54  # Current number of unprocessed clauses: 3465
% 0.38/0.54  # ...number of literals in the above   : 17667
% 0.38/0.54  # Current number of archived formulas  : 0
% 0.38/0.54  # Current number of archived clauses   : 100
% 0.38/0.54  # Clause-clause subsumption calls (NU) : 67308
% 0.38/0.54  # Rec. Clause-clause subsumption calls : 24033
% 0.38/0.54  # Non-unit clause-clause subsumptions  : 940
% 0.38/0.54  # Unit Clause-clause subsumption calls : 984
% 0.38/0.54  # Rewrite failures with RHS unbound    : 0
% 0.38/0.54  # BW rewrite match attempts            : 26
% 0.38/0.54  # BW rewrite match successes           : 16
% 0.38/0.54  # Condensation attempts                : 0
% 0.38/0.54  # Condensation successes               : 0
% 0.38/0.54  # Termbank termtop insertions          : 136106
% 0.38/0.54  
% 0.38/0.54  # -------------------------------------------------
% 0.38/0.54  # User time                : 0.183 s
% 0.38/0.54  # System time              : 0.014 s
% 0.38/0.54  # Total time               : 0.197 s
% 0.38/0.54  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
