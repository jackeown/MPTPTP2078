%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:12:15 EST 2020

% Result     : Theorem 4.96s
% Output     : CNFRefutation 4.96s
% Verified   : 
% Statistics : Number of formulae       :  193 (40619 expanded)
%              Number of clauses        :  148 (19858 expanded)
%              Number of leaves         :   22 (10086 expanded)
%              Depth                    :   33
%              Number of atoms          :  462 (99130 expanded)
%              Number of equality atoms :   71 (10663 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(t91_tops_1,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_tops_1(X2,X1)
           => v1_tops_1(k3_subset_1(u1_struct_0(X1),X2),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_tops_1)).

fof(t36_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => ( r1_tarski(k3_subset_1(X1,X2),X3)
           => r1_tarski(k3_subset_1(X1,X3),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_subset_1)).

fof(t109_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_tarski(k4_xboole_0(X1,X3),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t109_xboole_1)).

fof(involutiveness_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,k3_subset_1(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(t44_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => r1_tarski(k1_tops_1(X1,X2),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

fof(t84_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v2_tops_1(X2,X1)
          <=> k1_tops_1(X1,X2) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).

fof(d4_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v2_tops_1(X2,X1)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(X1),X2),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_1)).

fof(d3_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v1_tops_1(X2,X1)
          <=> k2_pre_topc(X1,X2) = k2_struct_0(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tops_1)).

fof(dt_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

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

fof(t48_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => r1_tarski(X2,k2_pre_topc(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_pre_topc)).

fof(dt_k2_pre_topc,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(t31_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => ( r1_tarski(X2,X3)
          <=> r1_tarski(k3_subset_1(X1,X3),k3_subset_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_subset_1)).

fof(d5_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_tops_1(X2,X1)
          <=> v2_tops_1(k2_pre_topc(X1,X2),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tops_1)).

fof(d1_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k1_tops_1(X1,X2) = k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_1)).

fof(t49_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( r1_tarski(X2,X3)
               => r1_tarski(k2_pre_topc(X1,X2),k2_pre_topc(X1,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_pre_topc)).

fof(c_0_22,plain,(
    ! [X4,X5] :
      ( ( r1_tarski(X4,X5)
        | X4 != X5 )
      & ( r1_tarski(X5,X4)
        | X4 != X5 )
      & ( ~ r1_tarski(X4,X5)
        | ~ r1_tarski(X5,X4)
        | X4 = X5 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_23,plain,(
    ! [X12,X13] : r1_tarski(k4_xboole_0(X12,X13),X12) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

fof(c_0_24,plain,(
    ! [X14,X15] :
      ( ~ m1_subset_1(X15,k1_zfmisc_1(X14))
      | k3_subset_1(X14,X15) = k4_xboole_0(X14,X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

fof(c_0_25,plain,(
    ! [X26,X27] :
      ( ( ~ m1_subset_1(X26,k1_zfmisc_1(X27))
        | r1_tarski(X26,X27) )
      & ( ~ r1_tarski(X26,X27)
        | m1_subset_1(X26,k1_zfmisc_1(X27)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_26,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_27,plain,(
    ! [X9,X10,X11] :
      ( ~ r1_tarski(X9,X10)
      | ~ r1_tarski(X10,X11)
      | r1_tarski(X9,X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

fof(c_0_28,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( v3_tops_1(X2,X1)
             => v1_tops_1(k3_subset_1(u1_struct_0(X1),X2),X1) ) ) ) ),
    inference(assume_negation,[status(cth)],[t91_tops_1])).

fof(c_0_29,plain,(
    ! [X23,X24,X25] :
      ( ~ m1_subset_1(X24,k1_zfmisc_1(X23))
      | ~ m1_subset_1(X25,k1_zfmisc_1(X23))
      | ~ r1_tarski(k3_subset_1(X23,X24),X25)
      | r1_tarski(k3_subset_1(X23,X25),X24) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t36_subset_1])])])).

cnf(c_0_30,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_31,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_32,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_33,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_26])).

cnf(c_0_34,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_35,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_36,negated_conjecture,
    ( l1_pre_topc(esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & v3_tops_1(esk2_0,esk1_0)
    & ~ v1_tops_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_28])])])).

cnf(c_0_37,plain,
    ( r1_tarski(k3_subset_1(X2,X3),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_tarski(k3_subset_1(X2,X1),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_38,plain,
    ( r1_tarski(k3_subset_1(X1,X2),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_39,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_40,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_41,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_42,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k4_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_30])).

cnf(c_0_43,plain,
    ( r1_tarski(k3_subset_1(X1,X1),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39])])).

fof(c_0_44,plain,(
    ! [X6,X7,X8] :
      ( ~ r1_tarski(X6,X7)
      | r1_tarski(k4_xboole_0(X6,X8),X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t109_xboole_1])])).

cnf(c_0_45,negated_conjecture,
    ( r1_tarski(X1,u1_struct_0(esk1_0))
    | ~ r1_tarski(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_46,plain,
    ( r1_tarski(k3_subset_1(X1,X1),X2)
    | ~ m1_subset_1(k4_xboole_0(X2,X3),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_47,plain,
    ( m1_subset_1(k4_xboole_0(X1,X2),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_30])).

cnf(c_0_48,plain,
    ( r1_tarski(k4_xboole_0(X1,X3),X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_49,negated_conjecture,
    ( r1_tarski(X1,u1_struct_0(esk1_0))
    | ~ r1_tarski(X2,esk2_0)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_34,c_0_45])).

cnf(c_0_50,plain,
    ( r1_tarski(k3_subset_1(X1,X1),X1) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_51,plain,
    ( m1_subset_1(k4_xboole_0(X1,X2),k1_zfmisc_1(X3))
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_32,c_0_48])).

cnf(c_0_52,negated_conjecture,
    ( r1_tarski(X1,u1_struct_0(esk1_0))
    | ~ r1_tarski(X1,k4_xboole_0(esk2_0,X2)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_30])).

cnf(c_0_53,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k3_subset_1(X2,X2)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_50])).

cnf(c_0_54,plain,
    ( r1_tarski(k3_subset_1(X1,X1),X2)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_46,c_0_51])).

cnf(c_0_55,negated_conjecture,
    ( r1_tarski(X1,u1_struct_0(esk1_0))
    | ~ r1_tarski(X1,k3_subset_1(esk2_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_56,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk2_0,X1),u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_33])).

cnf(c_0_57,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_58,plain,
    ( r1_tarski(k3_subset_1(X1,X1),X2)
    | ~ r1_tarski(k3_subset_1(X2,X2),X1) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_59,negated_conjecture,
    ( r1_tarski(k3_subset_1(k3_subset_1(esk2_0,esk2_0),k3_subset_1(esk2_0,esk2_0)),u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_55,c_0_50])).

cnf(c_0_60,negated_conjecture,
    ( m1_subset_1(k4_xboole_0(esk2_0,X1),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_32,c_0_56])).

cnf(c_0_61,plain,
    ( X1 = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_57,c_0_35])).

cnf(c_0_62,negated_conjecture,
    ( r1_tarski(k3_subset_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0)),k3_subset_1(esk2_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_63,negated_conjecture,
    ( r1_tarski(k3_subset_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0)),esk2_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_60])).

fof(c_0_64,plain,(
    ! [X18,X19] :
      ( ~ m1_subset_1(X19,k1_zfmisc_1(X18))
      | k3_subset_1(X18,k3_subset_1(X18,X19)) = X19 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).

cnf(c_0_65,negated_conjecture,
    ( k3_subset_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0)) = k3_subset_1(esk2_0,esk2_0)
    | ~ m1_subset_1(k3_subset_1(esk2_0,esk2_0),k1_zfmisc_1(k3_subset_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0)))) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_66,plain,
    ( m1_subset_1(k3_subset_1(X1,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_43])).

cnf(c_0_67,negated_conjecture,
    ( m1_subset_1(k3_subset_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0)),k1_zfmisc_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_63])).

fof(c_0_68,plain,(
    ! [X45,X46] :
      ( ~ l1_pre_topc(X45)
      | ~ m1_subset_1(X46,k1_zfmisc_1(u1_struct_0(X45)))
      | r1_tarski(k1_tops_1(X45,X46),X46) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_tops_1])])])).

fof(c_0_69,plain,(
    ! [X47,X48] :
      ( ( ~ v2_tops_1(X48,X47)
        | k1_tops_1(X47,X48) = k1_xboole_0
        | ~ m1_subset_1(X48,k1_zfmisc_1(u1_struct_0(X47)))
        | ~ l1_pre_topc(X47) )
      & ( k1_tops_1(X47,X48) != k1_xboole_0
        | v2_tops_1(X48,X47)
        | ~ m1_subset_1(X48,k1_zfmisc_1(u1_struct_0(X47)))
        | ~ l1_pre_topc(X47) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t84_tops_1])])])])).

fof(c_0_70,plain,(
    ! [X41,X42] :
      ( ( ~ v2_tops_1(X42,X41)
        | v1_tops_1(k3_subset_1(u1_struct_0(X41),X42),X41)
        | ~ m1_subset_1(X42,k1_zfmisc_1(u1_struct_0(X41)))
        | ~ l1_pre_topc(X41) )
      & ( ~ v1_tops_1(k3_subset_1(u1_struct_0(X41),X42),X41)
        | v2_tops_1(X42,X41)
        | ~ m1_subset_1(X42,k1_zfmisc_1(u1_struct_0(X41)))
        | ~ l1_pre_topc(X41) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tops_1])])])])).

cnf(c_0_71,plain,
    ( k3_subset_1(X2,k3_subset_1(X2,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_72,negated_conjecture,
    ( k3_subset_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0)) = k3_subset_1(esk2_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_67])])).

cnf(c_0_73,negated_conjecture,
    ( r1_tarski(k3_subset_1(esk2_0,esk2_0),u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_55,c_0_33])).

fof(c_0_74,plain,(
    ! [X39,X40] :
      ( ( ~ v1_tops_1(X40,X39)
        | k2_pre_topc(X39,X40) = k2_struct_0(X39)
        | ~ m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X39)))
        | ~ l1_pre_topc(X39) )
      & ( k2_pre_topc(X39,X40) != k2_struct_0(X39)
        | v1_tops_1(X40,X39)
        | ~ m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X39)))
        | ~ l1_pre_topc(X39) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tops_1])])])])).

fof(c_0_75,plain,(
    ! [X16,X17] :
      ( ~ m1_subset_1(X17,k1_zfmisc_1(X16))
      | m1_subset_1(k3_subset_1(X16,X17),k1_zfmisc_1(X16)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).

cnf(c_0_76,plain,
    ( r1_tarski(k1_tops_1(X1,X2),X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_77,plain,
    ( k1_tops_1(X2,X1) = k1_xboole_0
    | ~ v2_tops_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_78,plain,
    ( v2_tops_1(X2,X1)
    | ~ v1_tops_1(k3_subset_1(u1_struct_0(X1),X2),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_79,negated_conjecture,
    ( k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(esk2_0,esk2_0)) = u1_struct_0(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_39])])).

cnf(c_0_80,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_81,negated_conjecture,
    ( m1_subset_1(k3_subset_1(esk2_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_32,c_0_73])).

cnf(c_0_82,plain,
    ( v1_tops_1(X2,X1)
    | k2_pre_topc(X1,X2) != k2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

cnf(c_0_83,plain,
    ( m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_84,plain,
    ( r1_tarski(k1_xboole_0,X1)
    | ~ v2_tops_1(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(spm,[status(thm)],[c_0_76,c_0_77])).

cnf(c_0_85,negated_conjecture,
    ( v2_tops_1(k3_subset_1(esk2_0,esk2_0),esk1_0)
    | ~ v1_tops_1(u1_struct_0(esk1_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_80]),c_0_81])])).

cnf(c_0_86,plain,
    ( v1_tops_1(k3_subset_1(u1_struct_0(X1),X2),X1)
    | k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2)) != k2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_82,c_0_83])).

fof(c_0_87,plain,(
    ! [X28] :
      ( ~ l1_struct_0(X28)
      | k2_struct_0(X28) = u1_struct_0(X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

fof(c_0_88,plain,(
    ! [X31] :
      ( ~ l1_pre_topc(X31)
      | l1_struct_0(X31) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

fof(c_0_89,plain,(
    ! [X32,X33] :
      ( ~ l1_pre_topc(X32)
      | ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))
      | r1_tarski(X33,k2_pre_topc(X32,X33)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_pre_topc])])])).

cnf(c_0_90,negated_conjecture,
    ( r1_tarski(k1_xboole_0,k3_subset_1(esk2_0,esk2_0))
    | ~ v1_tops_1(u1_struct_0(esk1_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_85]),c_0_80]),c_0_81])])).

cnf(c_0_91,negated_conjecture,
    ( v1_tops_1(u1_struct_0(esk1_0),esk1_0)
    | k2_struct_0(esk1_0) != k2_pre_topc(esk1_0,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_79]),c_0_80]),c_0_81])])).

cnf(c_0_92,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_87])).

cnf(c_0_93,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_88])).

cnf(c_0_94,plain,
    ( r1_tarski(X2,k2_pre_topc(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_89])).

fof(c_0_95,plain,(
    ! [X29,X30] :
      ( ~ l1_pre_topc(X29)
      | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))
      | m1_subset_1(k2_pre_topc(X29,X30),k1_zfmisc_1(u1_struct_0(X29))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).

cnf(c_0_96,negated_conjecture,
    ( r1_tarski(k1_xboole_0,k3_subset_1(esk2_0,esk2_0))
    | k2_struct_0(esk1_0) != k2_pre_topc(esk1_0,u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_90,c_0_91])).

cnf(c_0_97,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_92,c_0_93])).

cnf(c_0_98,plain,
    ( k2_pre_topc(X1,X2) = X2
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_61,c_0_94])).

cnf(c_0_99,plain,
    ( m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_95])).

cnf(c_0_100,negated_conjecture,
    ( r1_tarski(k1_xboole_0,k3_subset_1(esk2_0,esk2_0))
    | k2_pre_topc(esk1_0,u1_struct_0(esk1_0)) != u1_struct_0(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_97]),c_0_80])])).

cnf(c_0_101,plain,
    ( k2_pre_topc(X1,u1_struct_0(X1)) = u1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_99]),c_0_39])])).

cnf(c_0_102,negated_conjecture,
    ( r1_tarski(k3_subset_1(u1_struct_0(esk1_0),esk2_0),u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_63]),c_0_41]),c_0_39])])).

cnf(c_0_103,plain,
    ( X1 = k3_subset_1(X2,X2)
    | ~ r1_tarski(X1,k3_subset_1(X2,X2)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_54]),c_0_53])).

cnf(c_0_104,negated_conjecture,
    ( r1_tarski(k1_xboole_0,k3_subset_1(esk2_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_101]),c_0_80])])).

cnf(c_0_105,negated_conjecture,
    ( r1_tarski(X1,u1_struct_0(esk1_0))
    | ~ r1_tarski(X1,k3_subset_1(u1_struct_0(esk1_0),esk2_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_102])).

cnf(c_0_106,negated_conjecture,
    ( m1_subset_1(k3_subset_1(esk2_0,esk2_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_66,c_0_72])).

cnf(c_0_107,negated_conjecture,
    ( k3_subset_1(esk2_0,esk2_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_103,c_0_104])).

cnf(c_0_108,negated_conjecture,
    ( r1_tarski(k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)),u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_105,c_0_50])).

fof(c_0_109,plain,(
    ! [X20,X21,X22] :
      ( ( ~ r1_tarski(X21,X22)
        | r1_tarski(k3_subset_1(X20,X22),k3_subset_1(X20,X21))
        | ~ m1_subset_1(X22,k1_zfmisc_1(X20))
        | ~ m1_subset_1(X21,k1_zfmisc_1(X20)) )
      & ( ~ r1_tarski(k3_subset_1(X20,X22),k3_subset_1(X20,X21))
        | r1_tarski(X21,X22)
        | ~ m1_subset_1(X22,k1_zfmisc_1(X20))
        | ~ m1_subset_1(X21,k1_zfmisc_1(X20)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_subset_1])])])])).

cnf(c_0_110,negated_conjecture,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(rw,[status(thm)],[c_0_106,c_0_107])).

cnf(c_0_111,negated_conjecture,
    ( m1_subset_1(k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_32,c_0_108])).

cnf(c_0_112,plain,
    ( r1_tarski(X3,X2)
    | ~ r1_tarski(k3_subset_1(X1,X2),k3_subset_1(X1,X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_109])).

cnf(c_0_113,plain,
    ( X1 = k3_subset_1(X2,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k3_subset_1(X2,X2))) ),
    inference(spm,[status(thm)],[c_0_103,c_0_35])).

cnf(c_0_114,negated_conjecture,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)))) ),
    inference(spm,[status(thm)],[c_0_110,c_0_111])).

cnf(c_0_115,plain,
    ( r1_tarski(X1,k3_subset_1(X2,X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_tarski(X3,k3_subset_1(X2,X1)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_112,c_0_71]),c_0_83])).

cnf(c_0_116,negated_conjecture,
    ( k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_113,c_0_114])).

cnf(c_0_117,negated_conjecture,
    ( m1_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_32,c_0_102])).

cnf(c_0_118,plain,
    ( r1_tarski(X1,k3_subset_1(X2,k3_subset_1(k3_subset_1(X2,X1),X3)))
    | ~ m1_subset_1(k3_subset_1(k3_subset_1(X2,X1),X3),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k3_subset_1(X2,X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_115,c_0_38])).

cnf(c_0_119,negated_conjecture,
    ( k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k1_xboole_0) = k3_subset_1(u1_struct_0(esk1_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_116]),c_0_39])])).

cnf(c_0_120,negated_conjecture,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0))) ),
    inference(spm,[status(thm)],[c_0_110,c_0_117])).

cnf(c_0_121,negated_conjecture,
    ( v2_tops_1(k1_xboole_0,esk1_0)
    | ~ v1_tops_1(u1_struct_0(esk1_0),esk1_0) ),
    inference(rw,[status(thm)],[c_0_85,c_0_107])).

cnf(c_0_122,plain,
    ( v1_tops_1(u1_struct_0(X1),X1)
    | k2_pre_topc(X1,u1_struct_0(X1)) != k2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_82,c_0_39])).

fof(c_0_123,plain,(
    ! [X43,X44] :
      ( ( ~ v3_tops_1(X44,X43)
        | v2_tops_1(k2_pre_topc(X43,X44),X43)
        | ~ m1_subset_1(X44,k1_zfmisc_1(u1_struct_0(X43)))
        | ~ l1_pre_topc(X43) )
      & ( ~ v2_tops_1(k2_pre_topc(X43,X44),X43)
        | v3_tops_1(X44,X43)
        | ~ m1_subset_1(X44,k1_zfmisc_1(u1_struct_0(X43)))
        | ~ l1_pre_topc(X43) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_tops_1])])])])).

fof(c_0_124,plain,(
    ! [X37,X38] :
      ( ~ l1_pre_topc(X37)
      | ~ m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(X37)))
      | k1_tops_1(X37,X38) = k3_subset_1(u1_struct_0(X37),k2_pre_topc(X37,k3_subset_1(u1_struct_0(X37),X38))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tops_1])])])).

cnf(c_0_125,negated_conjecture,
    ( r1_tarski(esk2_0,k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_118,c_0_119]),c_0_117]),c_0_120]),c_0_41])])).

cnf(c_0_126,plain,
    ( v1_tops_1(k3_subset_1(u1_struct_0(X2),X1),X2)
    | ~ v2_tops_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_127,negated_conjecture,
    ( v2_tops_1(k1_xboole_0,esk1_0)
    | k2_struct_0(esk1_0) != k2_pre_topc(esk1_0,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_121,c_0_122]),c_0_80])])).

cnf(c_0_128,plain,
    ( v2_tops_1(k2_pre_topc(X2,X1),X2)
    | ~ v3_tops_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_123])).

cnf(c_0_129,plain,
    ( k1_tops_1(X1,X2) = k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_124])).

cnf(c_0_130,negated_conjecture,
    ( k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)) = esk2_0
    | ~ r1_tarski(k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)),esk2_0) ),
    inference(spm,[status(thm)],[c_0_57,c_0_125])).

cnf(c_0_131,plain,
    ( r1_tarski(k3_subset_1(X1,X2),X3)
    | ~ m1_subset_1(k3_subset_1(X1,X3),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_35])).

cnf(c_0_132,plain,
    ( k2_pre_topc(X2,X1) = k2_struct_0(X2)
    | ~ v1_tops_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

cnf(c_0_133,negated_conjecture,
    ( v1_tops_1(u1_struct_0(esk1_0),esk1_0)
    | ~ v2_tops_1(k3_subset_1(esk2_0,esk2_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_126,c_0_79]),c_0_80]),c_0_81])])).

cnf(c_0_134,negated_conjecture,
    ( v2_tops_1(k1_xboole_0,esk1_0)
    | k2_pre_topc(esk1_0,u1_struct_0(esk1_0)) != u1_struct_0(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_127,c_0_97]),c_0_80])])).

cnf(c_0_135,plain,
    ( k3_subset_1(X1,X1) = k3_subset_1(X2,X2)
    | ~ m1_subset_1(k3_subset_1(X2,X2),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_103,c_0_43])).

cnf(c_0_136,plain,
    ( m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_51,c_0_31])).

cnf(c_0_137,plain,
    ( r1_tarski(k1_xboole_0,k2_pre_topc(X1,X2))
    | ~ v3_tops_1(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_128]),c_0_99])).

cnf(c_0_138,negated_conjecture,
    ( v3_tops_1(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_139,negated_conjecture,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_103,c_0_107])).

cnf(c_0_140,plain,
    ( k1_tops_1(X1,k3_subset_1(u1_struct_0(X1),X2)) = k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_129,c_0_71]),c_0_83])).

cnf(c_0_141,negated_conjecture,
    ( k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_130,c_0_131]),c_0_39]),c_0_117]),c_0_41])])).

cnf(c_0_142,plain,
    ( k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2)) = k2_struct_0(X1)
    | ~ v1_tops_1(k3_subset_1(u1_struct_0(X1),X2),X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_132,c_0_83])).

cnf(c_0_143,negated_conjecture,
    ( k3_subset_1(u1_struct_0(esk1_0),k1_xboole_0) = u1_struct_0(esk1_0) ),
    inference(rw,[status(thm)],[c_0_79,c_0_107])).

cnf(c_0_144,negated_conjecture,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(rw,[status(thm)],[c_0_81,c_0_107])).

cnf(c_0_145,negated_conjecture,
    ( v1_tops_1(u1_struct_0(esk1_0),esk1_0)
    | ~ v2_tops_1(k1_xboole_0,esk1_0) ),
    inference(rw,[status(thm)],[c_0_133,c_0_107])).

cnf(c_0_146,negated_conjecture,
    ( v2_tops_1(k1_xboole_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_134,c_0_101]),c_0_80])])).

cnf(c_0_147,negated_conjecture,
    ( r1_tarski(k4_xboole_0(k3_subset_1(u1_struct_0(esk1_0),esk2_0),X1),u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_105,c_0_30])).

cnf(c_0_148,plain,
    ( k3_subset_1(X1,X1) = k3_subset_1(X2,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_135,c_0_136]),c_0_39])])).

cnf(c_0_149,negated_conjecture,
    ( r1_tarski(k1_xboole_0,k2_pre_topc(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_137,c_0_138]),c_0_80]),c_0_41])])).

cnf(c_0_150,negated_conjecture,
    ( k3_subset_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_139,c_0_50])).

cnf(c_0_151,negated_conjecture,
    ( k3_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0))) = k1_tops_1(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_140,c_0_141]),c_0_80]),c_0_117])])).

cnf(c_0_152,negated_conjecture,
    ( ~ v1_tops_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_153,negated_conjecture,
    ( k2_struct_0(esk1_0) = k2_pre_topc(esk1_0,u1_struct_0(esk1_0))
    | ~ v1_tops_1(u1_struct_0(esk1_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_142,c_0_143]),c_0_80]),c_0_144])])).

cnf(c_0_154,negated_conjecture,
    ( v1_tops_1(u1_struct_0(esk1_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_145,c_0_146])])).

cnf(c_0_155,negated_conjecture,
    ( m1_subset_1(k4_xboole_0(k3_subset_1(u1_struct_0(esk1_0),esk2_0),X1),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_32,c_0_147])).

cnf(c_0_156,plain,
    ( r1_tarski(X1,u1_struct_0(X2))
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r1_tarski(X1,k2_pre_topc(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_99])).

cnf(c_0_157,negated_conjecture,
    ( k3_subset_1(k2_pre_topc(esk1_0,esk2_0),k2_pre_topc(esk1_0,esk2_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_148,c_0_149]),c_0_150])).

cnf(c_0_158,plain,
    ( r1_tarski(k3_subset_1(X1,X2),X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_48,c_0_31])).

cnf(c_0_159,negated_conjecture,
    ( k3_subset_1(u1_struct_0(esk1_0),k1_tops_1(esk1_0,esk2_0)) = k2_pre_topc(esk1_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0))
    | ~ m1_subset_1(k2_pre_topc(esk1_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0)),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_71,c_0_151])).

cnf(c_0_160,negated_conjecture,
    ( m1_subset_1(k1_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(k2_pre_topc(esk1_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0)),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_83,c_0_151])).

cnf(c_0_161,negated_conjecture,
    ( k2_pre_topc(esk1_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0)) != k2_struct_0(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_117]),c_0_80])]),c_0_152])).

cnf(c_0_162,negated_conjecture,
    ( k2_struct_0(esk1_0) = k2_pre_topc(esk1_0,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_153,c_0_154])])).

cnf(c_0_163,negated_conjecture,
    ( m1_subset_1(k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),X1),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0))) ),
    inference(spm,[status(thm)],[c_0_155,c_0_31])).

cnf(c_0_164,plain,
    ( m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_32,c_0_76])).

cnf(c_0_165,negated_conjecture,
    ( k1_tops_1(esk1_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0)) = k3_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_129,c_0_141]),c_0_80]),c_0_117])])).

cnf(c_0_166,plain,
    ( r1_tarski(k3_subset_1(k2_pre_topc(X1,X2),X3),u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_pre_topc(X1,X2)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_156,c_0_38])).

cnf(c_0_167,negated_conjecture,
    ( k3_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_xboole_0) = k2_pre_topc(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_157]),c_0_39])])).

cnf(c_0_168,negated_conjecture,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_pre_topc(esk1_0,esk2_0))) ),
    inference(spm,[status(thm)],[c_0_32,c_0_149])).

cnf(c_0_169,plain,
    ( k3_subset_1(X1,X2) = X3
    | ~ m1_subset_1(X3,k1_zfmisc_1(k3_subset_1(X1,X2)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_61,c_0_158])).

cnf(c_0_170,negated_conjecture,
    ( k3_subset_1(u1_struct_0(esk1_0),k1_tops_1(esk1_0,esk2_0)) = k2_pre_topc(esk1_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_159,c_0_99]),c_0_80]),c_0_117])])).

cnf(c_0_171,negated_conjecture,
    ( m1_subset_1(k1_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_160,c_0_99]),c_0_80]),c_0_117])])).

cnf(c_0_172,negated_conjecture,
    ( k2_pre_topc(esk1_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0)) != k2_pre_topc(esk1_0,u1_struct_0(esk1_0)) ),
    inference(rw,[status(thm)],[c_0_161,c_0_162])).

cnf(c_0_173,negated_conjecture,
    ( k2_pre_topc(esk1_0,u1_struct_0(esk1_0)) = u1_struct_0(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_162]),c_0_80])])).

cnf(c_0_174,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_163,c_0_71]),c_0_83])).

cnf(c_0_175,negated_conjecture,
    ( m1_subset_1(k3_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0)),k1_zfmisc_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_164,c_0_165]),c_0_80]),c_0_117])])).

cnf(c_0_176,plain,
    ( v1_tops_1(k1_tops_1(X1,X2),X1)
    | ~ v2_tops_1(k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2)),X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2)),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_126,c_0_129])).

cnf(c_0_177,negated_conjecture,
    ( r1_tarski(k2_pre_topc(esk1_0,esk2_0),u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_166,c_0_167]),c_0_80]),c_0_168]),c_0_41])])).

cnf(c_0_178,plain,
    ( X1 = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3))
    | ~ r1_tarski(X3,X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_169,c_0_71]),c_0_83])).

cnf(c_0_179,negated_conjecture,
    ( m1_subset_1(k2_pre_topc(esk1_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0)),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_170]),c_0_171])])).

cnf(c_0_180,negated_conjecture,
    ( k2_pre_topc(esk1_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0)) != u1_struct_0(esk1_0) ),
    inference(rw,[status(thm)],[c_0_172,c_0_173])).

fof(c_0_181,plain,(
    ! [X34,X35,X36] :
      ( ~ l1_pre_topc(X34)
      | ~ m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X34)))
      | ~ m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X34)))
      | ~ r1_tarski(X35,X36)
      | r1_tarski(k2_pre_topc(X34,X35),k2_pre_topc(X34,X36)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t49_pre_topc])])])).

cnf(c_0_182,negated_conjecture,
    ( m1_subset_1(k3_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0)),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_174,c_0_175])).

cnf(c_0_183,plain,
    ( v1_tops_1(k1_tops_1(X1,X2),X1)
    | ~ v3_tops_1(k3_subset_1(u1_struct_0(X1),X2),X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2)),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_176,c_0_128]),c_0_83])).

cnf(c_0_184,negated_conjecture,
    ( m1_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_32,c_0_177])).

cnf(c_0_185,negated_conjecture,
    ( ~ m1_subset_1(u1_struct_0(esk1_0),k1_zfmisc_1(X1))
    | ~ r1_tarski(X1,k2_pre_topc(esk1_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_178,c_0_179]),c_0_180])).

cnf(c_0_186,plain,
    ( r1_tarski(k2_pre_topc(X1,X2),k2_pre_topc(X1,X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_181])).

cnf(c_0_187,negated_conjecture,
    ( k2_pre_topc(esk1_0,k3_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0))) = u1_struct_0(esk1_0)
    | ~ v1_tops_1(k3_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0)),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_132,c_0_182]),c_0_162]),c_0_173]),c_0_80])])).

cnf(c_0_188,negated_conjecture,
    ( v1_tops_1(k3_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0)),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_183,c_0_141]),c_0_165]),c_0_138]),c_0_80]),c_0_184]),c_0_117])])).

cnf(c_0_189,negated_conjecture,
    ( ~ m1_subset_1(u1_struct_0(esk1_0),k1_zfmisc_1(k2_pre_topc(esk1_0,X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_tarski(X1,k3_subset_1(u1_struct_0(esk1_0),esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_185,c_0_186]),c_0_80]),c_0_117])])).

cnf(c_0_190,negated_conjecture,
    ( k2_pre_topc(esk1_0,k3_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0))) = u1_struct_0(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_187,c_0_188])])).

cnf(c_0_191,negated_conjecture,
    ( r1_tarski(k3_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0)),k3_subset_1(u1_struct_0(esk1_0),esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_165]),c_0_80]),c_0_117])])).

cnf(c_0_192,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_189,c_0_190]),c_0_39]),c_0_182]),c_0_191])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:02:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 4.96/5.20  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 4.96/5.20  # and selection function SelectComplexExceptUniqMaxHorn.
% 4.96/5.20  #
% 4.96/5.20  # Preprocessing time       : 0.029 s
% 4.96/5.20  # Presaturation interreduction done
% 4.96/5.20  
% 4.96/5.20  # Proof found!
% 4.96/5.20  # SZS status Theorem
% 4.96/5.20  # SZS output start CNFRefutation
% 4.96/5.20  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.96/5.20  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 4.96/5.20  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 4.96/5.20  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 4.96/5.20  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 4.96/5.20  fof(t91_tops_1, conjecture, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_tops_1(X2,X1)=>v1_tops_1(k3_subset_1(u1_struct_0(X1),X2),X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_tops_1)).
% 4.96/5.20  fof(t36_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(r1_tarski(k3_subset_1(X1,X2),X3)=>r1_tarski(k3_subset_1(X1,X3),X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_subset_1)).
% 4.96/5.20  fof(t109_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_tarski(k4_xboole_0(X1,X3),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t109_xboole_1)).
% 4.96/5.20  fof(involutiveness_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,k3_subset_1(X1,X2))=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 4.96/5.20  fof(t44_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>r1_tarski(k1_tops_1(X1,X2),X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_1)).
% 4.96/5.20  fof(t84_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v2_tops_1(X2,X1)<=>k1_tops_1(X1,X2)=k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_tops_1)).
% 4.96/5.20  fof(d4_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v2_tops_1(X2,X1)<=>v1_tops_1(k3_subset_1(u1_struct_0(X1),X2),X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tops_1)).
% 4.96/5.20  fof(d3_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v1_tops_1(X2,X1)<=>k2_pre_topc(X1,X2)=k2_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tops_1)).
% 4.96/5.20  fof(dt_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 4.96/5.20  fof(d3_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>k2_struct_0(X1)=u1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 4.96/5.20  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 4.96/5.20  fof(t48_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>r1_tarski(X2,k2_pre_topc(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_pre_topc)).
% 4.96/5.20  fof(dt_k2_pre_topc, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 4.96/5.20  fof(t31_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(r1_tarski(X2,X3)<=>r1_tarski(k3_subset_1(X1,X3),k3_subset_1(X1,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_subset_1)).
% 4.96/5.20  fof(d5_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_tops_1(X2,X1)<=>v2_tops_1(k2_pre_topc(X1,X2),X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tops_1)).
% 4.96/5.20  fof(d1_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k1_tops_1(X1,X2)=k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tops_1)).
% 4.96/5.20  fof(t49_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(r1_tarski(X2,X3)=>r1_tarski(k2_pre_topc(X1,X2),k2_pre_topc(X1,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_pre_topc)).
% 4.96/5.20  fof(c_0_22, plain, ![X4, X5]:(((r1_tarski(X4,X5)|X4!=X5)&(r1_tarski(X5,X4)|X4!=X5))&(~r1_tarski(X4,X5)|~r1_tarski(X5,X4)|X4=X5)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 4.96/5.20  fof(c_0_23, plain, ![X12, X13]:r1_tarski(k4_xboole_0(X12,X13),X12), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 4.96/5.20  fof(c_0_24, plain, ![X14, X15]:(~m1_subset_1(X15,k1_zfmisc_1(X14))|k3_subset_1(X14,X15)=k4_xboole_0(X14,X15)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 4.96/5.20  fof(c_0_25, plain, ![X26, X27]:((~m1_subset_1(X26,k1_zfmisc_1(X27))|r1_tarski(X26,X27))&(~r1_tarski(X26,X27)|m1_subset_1(X26,k1_zfmisc_1(X27)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 4.96/5.20  cnf(c_0_26, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_22])).
% 4.96/5.20  fof(c_0_27, plain, ![X9, X10, X11]:(~r1_tarski(X9,X10)|~r1_tarski(X10,X11)|r1_tarski(X9,X11)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 4.96/5.20  fof(c_0_28, negated_conjecture, ~(![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_tops_1(X2,X1)=>v1_tops_1(k3_subset_1(u1_struct_0(X1),X2),X1))))), inference(assume_negation,[status(cth)],[t91_tops_1])).
% 4.96/5.20  fof(c_0_29, plain, ![X23, X24, X25]:(~m1_subset_1(X24,k1_zfmisc_1(X23))|(~m1_subset_1(X25,k1_zfmisc_1(X23))|(~r1_tarski(k3_subset_1(X23,X24),X25)|r1_tarski(k3_subset_1(X23,X25),X24)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t36_subset_1])])])).
% 4.96/5.20  cnf(c_0_30, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 4.96/5.20  cnf(c_0_31, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 4.96/5.20  cnf(c_0_32, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 4.96/5.20  cnf(c_0_33, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_26])).
% 4.96/5.20  cnf(c_0_34, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 4.96/5.20  cnf(c_0_35, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 4.96/5.20  fof(c_0_36, negated_conjecture, (l1_pre_topc(esk1_0)&(m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&(v3_tops_1(esk2_0,esk1_0)&~v1_tops_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),esk1_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_28])])])).
% 4.96/5.20  cnf(c_0_37, plain, (r1_tarski(k3_subset_1(X2,X3),X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_tarski(k3_subset_1(X2,X1),X3)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 4.96/5.20  cnf(c_0_38, plain, (r1_tarski(k3_subset_1(X1,X2),X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 4.96/5.20  cnf(c_0_39, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 4.96/5.20  cnf(c_0_40, plain, (r1_tarski(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 4.96/5.20  cnf(c_0_41, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 4.96/5.20  cnf(c_0_42, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k4_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_34, c_0_30])).
% 4.96/5.20  cnf(c_0_43, plain, (r1_tarski(k3_subset_1(X1,X1),X2)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_39])])).
% 4.96/5.20  fof(c_0_44, plain, ![X6, X7, X8]:(~r1_tarski(X6,X7)|r1_tarski(k4_xboole_0(X6,X8),X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t109_xboole_1])])).
% 4.96/5.20  cnf(c_0_45, negated_conjecture, (r1_tarski(X1,u1_struct_0(esk1_0))|~r1_tarski(X1,esk2_0)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 4.96/5.20  cnf(c_0_46, plain, (r1_tarski(k3_subset_1(X1,X1),X2)|~m1_subset_1(k4_xboole_0(X2,X3),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 4.96/5.20  cnf(c_0_47, plain, (m1_subset_1(k4_xboole_0(X1,X2),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_32, c_0_30])).
% 4.96/5.20  cnf(c_0_48, plain, (r1_tarski(k4_xboole_0(X1,X3),X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 4.96/5.20  cnf(c_0_49, negated_conjecture, (r1_tarski(X1,u1_struct_0(esk1_0))|~r1_tarski(X2,esk2_0)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_34, c_0_45])).
% 4.96/5.20  cnf(c_0_50, plain, (r1_tarski(k3_subset_1(X1,X1),X1)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 4.96/5.20  cnf(c_0_51, plain, (m1_subset_1(k4_xboole_0(X1,X2),k1_zfmisc_1(X3))|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_32, c_0_48])).
% 4.96/5.20  cnf(c_0_52, negated_conjecture, (r1_tarski(X1,u1_struct_0(esk1_0))|~r1_tarski(X1,k4_xboole_0(esk2_0,X2))), inference(spm,[status(thm)],[c_0_49, c_0_30])).
% 4.96/5.20  cnf(c_0_53, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k3_subset_1(X2,X2))), inference(spm,[status(thm)],[c_0_34, c_0_50])).
% 4.96/5.20  cnf(c_0_54, plain, (r1_tarski(k3_subset_1(X1,X1),X2)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_46, c_0_51])).
% 4.96/5.20  cnf(c_0_55, negated_conjecture, (r1_tarski(X1,u1_struct_0(esk1_0))|~r1_tarski(X1,k3_subset_1(esk2_0,esk2_0))), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 4.96/5.20  cnf(c_0_56, negated_conjecture, (r1_tarski(k4_xboole_0(esk2_0,X1),u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_52, c_0_33])).
% 4.96/5.20  cnf(c_0_57, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 4.96/5.20  cnf(c_0_58, plain, (r1_tarski(k3_subset_1(X1,X1),X2)|~r1_tarski(k3_subset_1(X2,X2),X1)), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 4.96/5.20  cnf(c_0_59, negated_conjecture, (r1_tarski(k3_subset_1(k3_subset_1(esk2_0,esk2_0),k3_subset_1(esk2_0,esk2_0)),u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_55, c_0_50])).
% 4.96/5.20  cnf(c_0_60, negated_conjecture, (m1_subset_1(k4_xboole_0(esk2_0,X1),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_32, c_0_56])).
% 4.96/5.20  cnf(c_0_61, plain, (X1=X2|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_57, c_0_35])).
% 4.96/5.20  cnf(c_0_62, negated_conjecture, (r1_tarski(k3_subset_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0)),k3_subset_1(esk2_0,esk2_0))), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 4.96/5.20  cnf(c_0_63, negated_conjecture, (r1_tarski(k3_subset_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0)),esk2_0)), inference(spm,[status(thm)],[c_0_46, c_0_60])).
% 4.96/5.20  fof(c_0_64, plain, ![X18, X19]:(~m1_subset_1(X19,k1_zfmisc_1(X18))|k3_subset_1(X18,k3_subset_1(X18,X19))=X19), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).
% 4.96/5.20  cnf(c_0_65, negated_conjecture, (k3_subset_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0))=k3_subset_1(esk2_0,esk2_0)|~m1_subset_1(k3_subset_1(esk2_0,esk2_0),k1_zfmisc_1(k3_subset_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0))))), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 4.96/5.20  cnf(c_0_66, plain, (m1_subset_1(k3_subset_1(X1,X1),k1_zfmisc_1(X2))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_32, c_0_43])).
% 4.96/5.20  cnf(c_0_67, negated_conjecture, (m1_subset_1(k3_subset_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0)),k1_zfmisc_1(esk2_0))), inference(spm,[status(thm)],[c_0_32, c_0_63])).
% 4.96/5.20  fof(c_0_68, plain, ![X45, X46]:(~l1_pre_topc(X45)|(~m1_subset_1(X46,k1_zfmisc_1(u1_struct_0(X45)))|r1_tarski(k1_tops_1(X45,X46),X46))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_tops_1])])])).
% 4.96/5.20  fof(c_0_69, plain, ![X47, X48]:((~v2_tops_1(X48,X47)|k1_tops_1(X47,X48)=k1_xboole_0|~m1_subset_1(X48,k1_zfmisc_1(u1_struct_0(X47)))|~l1_pre_topc(X47))&(k1_tops_1(X47,X48)!=k1_xboole_0|v2_tops_1(X48,X47)|~m1_subset_1(X48,k1_zfmisc_1(u1_struct_0(X47)))|~l1_pre_topc(X47))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t84_tops_1])])])])).
% 4.96/5.20  fof(c_0_70, plain, ![X41, X42]:((~v2_tops_1(X42,X41)|v1_tops_1(k3_subset_1(u1_struct_0(X41),X42),X41)|~m1_subset_1(X42,k1_zfmisc_1(u1_struct_0(X41)))|~l1_pre_topc(X41))&(~v1_tops_1(k3_subset_1(u1_struct_0(X41),X42),X41)|v2_tops_1(X42,X41)|~m1_subset_1(X42,k1_zfmisc_1(u1_struct_0(X41)))|~l1_pre_topc(X41))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tops_1])])])])).
% 4.96/5.20  cnf(c_0_71, plain, (k3_subset_1(X2,k3_subset_1(X2,X1))=X1|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_64])).
% 4.96/5.20  cnf(c_0_72, negated_conjecture, (k3_subset_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0))=k3_subset_1(esk2_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_67])])).
% 4.96/5.20  cnf(c_0_73, negated_conjecture, (r1_tarski(k3_subset_1(esk2_0,esk2_0),u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_55, c_0_33])).
% 4.96/5.20  fof(c_0_74, plain, ![X39, X40]:((~v1_tops_1(X40,X39)|k2_pre_topc(X39,X40)=k2_struct_0(X39)|~m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X39)))|~l1_pre_topc(X39))&(k2_pre_topc(X39,X40)!=k2_struct_0(X39)|v1_tops_1(X40,X39)|~m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X39)))|~l1_pre_topc(X39))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tops_1])])])])).
% 4.96/5.20  fof(c_0_75, plain, ![X16, X17]:(~m1_subset_1(X17,k1_zfmisc_1(X16))|m1_subset_1(k3_subset_1(X16,X17),k1_zfmisc_1(X16))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).
% 4.96/5.20  cnf(c_0_76, plain, (r1_tarski(k1_tops_1(X1,X2),X2)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_68])).
% 4.96/5.20  cnf(c_0_77, plain, (k1_tops_1(X2,X1)=k1_xboole_0|~v2_tops_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_69])).
% 4.96/5.20  cnf(c_0_78, plain, (v2_tops_1(X2,X1)|~v1_tops_1(k3_subset_1(u1_struct_0(X1),X2),X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_70])).
% 4.96/5.20  cnf(c_0_79, negated_conjecture, (k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(esk2_0,esk2_0))=u1_struct_0(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_39])])).
% 4.96/5.20  cnf(c_0_80, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 4.96/5.20  cnf(c_0_81, negated_conjecture, (m1_subset_1(k3_subset_1(esk2_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_32, c_0_73])).
% 4.96/5.20  cnf(c_0_82, plain, (v1_tops_1(X2,X1)|k2_pre_topc(X1,X2)!=k2_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_74])).
% 4.96/5.20  cnf(c_0_83, plain, (m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_75])).
% 4.96/5.20  cnf(c_0_84, plain, (r1_tarski(k1_xboole_0,X1)|~v2_tops_1(X1,X2)|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))), inference(spm,[status(thm)],[c_0_76, c_0_77])).
% 4.96/5.20  cnf(c_0_85, negated_conjecture, (v2_tops_1(k3_subset_1(esk2_0,esk2_0),esk1_0)|~v1_tops_1(u1_struct_0(esk1_0),esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_79]), c_0_80]), c_0_81])])).
% 4.96/5.20  cnf(c_0_86, plain, (v1_tops_1(k3_subset_1(u1_struct_0(X1),X2),X1)|k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2))!=k2_struct_0(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_82, c_0_83])).
% 4.96/5.20  fof(c_0_87, plain, ![X28]:(~l1_struct_0(X28)|k2_struct_0(X28)=u1_struct_0(X28)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).
% 4.96/5.20  fof(c_0_88, plain, ![X31]:(~l1_pre_topc(X31)|l1_struct_0(X31)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 4.96/5.20  fof(c_0_89, plain, ![X32, X33]:(~l1_pre_topc(X32)|(~m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))|r1_tarski(X33,k2_pre_topc(X32,X33)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_pre_topc])])])).
% 4.96/5.20  cnf(c_0_90, negated_conjecture, (r1_tarski(k1_xboole_0,k3_subset_1(esk2_0,esk2_0))|~v1_tops_1(u1_struct_0(esk1_0),esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_85]), c_0_80]), c_0_81])])).
% 4.96/5.20  cnf(c_0_91, negated_conjecture, (v1_tops_1(u1_struct_0(esk1_0),esk1_0)|k2_struct_0(esk1_0)!=k2_pre_topc(esk1_0,u1_struct_0(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_79]), c_0_80]), c_0_81])])).
% 4.96/5.20  cnf(c_0_92, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_87])).
% 4.96/5.20  cnf(c_0_93, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_88])).
% 4.96/5.20  cnf(c_0_94, plain, (r1_tarski(X2,k2_pre_topc(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_89])).
% 4.96/5.20  fof(c_0_95, plain, ![X29, X30]:(~l1_pre_topc(X29)|~m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))|m1_subset_1(k2_pre_topc(X29,X30),k1_zfmisc_1(u1_struct_0(X29)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).
% 4.96/5.20  cnf(c_0_96, negated_conjecture, (r1_tarski(k1_xboole_0,k3_subset_1(esk2_0,esk2_0))|k2_struct_0(esk1_0)!=k2_pre_topc(esk1_0,u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_90, c_0_91])).
% 4.96/5.20  cnf(c_0_97, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_92, c_0_93])).
% 4.96/5.20  cnf(c_0_98, plain, (k2_pre_topc(X1,X2)=X2|~l1_pre_topc(X1)|~m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(X2))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_61, c_0_94])).
% 4.96/5.20  cnf(c_0_99, plain, (m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_95])).
% 4.96/5.20  cnf(c_0_100, negated_conjecture, (r1_tarski(k1_xboole_0,k3_subset_1(esk2_0,esk2_0))|k2_pre_topc(esk1_0,u1_struct_0(esk1_0))!=u1_struct_0(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_97]), c_0_80])])).
% 4.96/5.20  cnf(c_0_101, plain, (k2_pre_topc(X1,u1_struct_0(X1))=u1_struct_0(X1)|~l1_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_99]), c_0_39])])).
% 4.96/5.20  cnf(c_0_102, negated_conjecture, (r1_tarski(k3_subset_1(u1_struct_0(esk1_0),esk2_0),u1_struct_0(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_63]), c_0_41]), c_0_39])])).
% 4.96/5.20  cnf(c_0_103, plain, (X1=k3_subset_1(X2,X2)|~r1_tarski(X1,k3_subset_1(X2,X2))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_54]), c_0_53])).
% 4.96/5.20  cnf(c_0_104, negated_conjecture, (r1_tarski(k1_xboole_0,k3_subset_1(esk2_0,esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_101]), c_0_80])])).
% 4.96/5.20  cnf(c_0_105, negated_conjecture, (r1_tarski(X1,u1_struct_0(esk1_0))|~r1_tarski(X1,k3_subset_1(u1_struct_0(esk1_0),esk2_0))), inference(spm,[status(thm)],[c_0_34, c_0_102])).
% 4.96/5.20  cnf(c_0_106, negated_conjecture, (m1_subset_1(k3_subset_1(esk2_0,esk2_0),k1_zfmisc_1(X1))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_66, c_0_72])).
% 4.96/5.20  cnf(c_0_107, negated_conjecture, (k3_subset_1(esk2_0,esk2_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_103, c_0_104])).
% 4.96/5.20  cnf(c_0_108, negated_conjecture, (r1_tarski(k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)),u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_105, c_0_50])).
% 4.96/5.20  fof(c_0_109, plain, ![X20, X21, X22]:((~r1_tarski(X21,X22)|r1_tarski(k3_subset_1(X20,X22),k3_subset_1(X20,X21))|~m1_subset_1(X22,k1_zfmisc_1(X20))|~m1_subset_1(X21,k1_zfmisc_1(X20)))&(~r1_tarski(k3_subset_1(X20,X22),k3_subset_1(X20,X21))|r1_tarski(X21,X22)|~m1_subset_1(X22,k1_zfmisc_1(X20))|~m1_subset_1(X21,k1_zfmisc_1(X20)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_subset_1])])])])).
% 4.96/5.20  cnf(c_0_110, negated_conjecture, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(rw,[status(thm)],[c_0_106, c_0_107])).
% 4.96/5.20  cnf(c_0_111, negated_conjecture, (m1_subset_1(k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_32, c_0_108])).
% 4.96/5.20  cnf(c_0_112, plain, (r1_tarski(X3,X2)|~r1_tarski(k3_subset_1(X1,X2),k3_subset_1(X1,X3))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~m1_subset_1(X3,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_109])).
% 4.96/5.20  cnf(c_0_113, plain, (X1=k3_subset_1(X2,X2)|~m1_subset_1(X1,k1_zfmisc_1(k3_subset_1(X2,X2)))), inference(spm,[status(thm)],[c_0_103, c_0_35])).
% 4.96/5.20  cnf(c_0_114, negated_conjecture, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0))))), inference(spm,[status(thm)],[c_0_110, c_0_111])).
% 4.96/5.20  cnf(c_0_115, plain, (r1_tarski(X1,k3_subset_1(X2,X3))|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_tarski(X3,k3_subset_1(X2,X1))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_112, c_0_71]), c_0_83])).
% 4.96/5.20  cnf(c_0_116, negated_conjecture, (k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_113, c_0_114])).
% 4.96/5.20  cnf(c_0_117, negated_conjecture, (m1_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_32, c_0_102])).
% 4.96/5.20  cnf(c_0_118, plain, (r1_tarski(X1,k3_subset_1(X2,k3_subset_1(k3_subset_1(X2,X1),X3)))|~m1_subset_1(k3_subset_1(k3_subset_1(X2,X1),X3),k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(k3_subset_1(X2,X1)))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_115, c_0_38])).
% 4.96/5.20  cnf(c_0_119, negated_conjecture, (k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k1_xboole_0)=k3_subset_1(u1_struct_0(esk1_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_116]), c_0_39])])).
% 4.96/5.20  cnf(c_0_120, negated_conjecture, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0)))), inference(spm,[status(thm)],[c_0_110, c_0_117])).
% 4.96/5.20  cnf(c_0_121, negated_conjecture, (v2_tops_1(k1_xboole_0,esk1_0)|~v1_tops_1(u1_struct_0(esk1_0),esk1_0)), inference(rw,[status(thm)],[c_0_85, c_0_107])).
% 4.96/5.20  cnf(c_0_122, plain, (v1_tops_1(u1_struct_0(X1),X1)|k2_pre_topc(X1,u1_struct_0(X1))!=k2_struct_0(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_82, c_0_39])).
% 4.96/5.20  fof(c_0_123, plain, ![X43, X44]:((~v3_tops_1(X44,X43)|v2_tops_1(k2_pre_topc(X43,X44),X43)|~m1_subset_1(X44,k1_zfmisc_1(u1_struct_0(X43)))|~l1_pre_topc(X43))&(~v2_tops_1(k2_pre_topc(X43,X44),X43)|v3_tops_1(X44,X43)|~m1_subset_1(X44,k1_zfmisc_1(u1_struct_0(X43)))|~l1_pre_topc(X43))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_tops_1])])])])).
% 4.96/5.20  fof(c_0_124, plain, ![X37, X38]:(~l1_pre_topc(X37)|(~m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(X37)))|k1_tops_1(X37,X38)=k3_subset_1(u1_struct_0(X37),k2_pre_topc(X37,k3_subset_1(u1_struct_0(X37),X38))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tops_1])])])).
% 4.96/5.20  cnf(c_0_125, negated_conjecture, (r1_tarski(esk2_0,k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_118, c_0_119]), c_0_117]), c_0_120]), c_0_41])])).
% 4.96/5.20  cnf(c_0_126, plain, (v1_tops_1(k3_subset_1(u1_struct_0(X2),X1),X2)|~v2_tops_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_70])).
% 4.96/5.20  cnf(c_0_127, negated_conjecture, (v2_tops_1(k1_xboole_0,esk1_0)|k2_struct_0(esk1_0)!=k2_pre_topc(esk1_0,u1_struct_0(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_121, c_0_122]), c_0_80])])).
% 4.96/5.20  cnf(c_0_128, plain, (v2_tops_1(k2_pre_topc(X2,X1),X2)|~v3_tops_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_123])).
% 4.96/5.20  cnf(c_0_129, plain, (k1_tops_1(X1,X2)=k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_124])).
% 4.96/5.20  cnf(c_0_130, negated_conjecture, (k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0))=esk2_0|~r1_tarski(k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)),esk2_0)), inference(spm,[status(thm)],[c_0_57, c_0_125])).
% 4.96/5.20  cnf(c_0_131, plain, (r1_tarski(k3_subset_1(X1,X2),X3)|~m1_subset_1(k3_subset_1(X1,X3),k1_zfmisc_1(X2))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~m1_subset_1(X3,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_37, c_0_35])).
% 4.96/5.20  cnf(c_0_132, plain, (k2_pre_topc(X2,X1)=k2_struct_0(X2)|~v1_tops_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_74])).
% 4.96/5.20  cnf(c_0_133, negated_conjecture, (v1_tops_1(u1_struct_0(esk1_0),esk1_0)|~v2_tops_1(k3_subset_1(esk2_0,esk2_0),esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_126, c_0_79]), c_0_80]), c_0_81])])).
% 4.96/5.20  cnf(c_0_134, negated_conjecture, (v2_tops_1(k1_xboole_0,esk1_0)|k2_pre_topc(esk1_0,u1_struct_0(esk1_0))!=u1_struct_0(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_127, c_0_97]), c_0_80])])).
% 4.96/5.20  cnf(c_0_135, plain, (k3_subset_1(X1,X1)=k3_subset_1(X2,X2)|~m1_subset_1(k3_subset_1(X2,X2),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_103, c_0_43])).
% 4.96/5.20  cnf(c_0_136, plain, (m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X3))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_51, c_0_31])).
% 4.96/5.20  cnf(c_0_137, plain, (r1_tarski(k1_xboole_0,k2_pre_topc(X1,X2))|~v3_tops_1(X2,X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_128]), c_0_99])).
% 4.96/5.20  cnf(c_0_138, negated_conjecture, (v3_tops_1(esk2_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 4.96/5.20  cnf(c_0_139, negated_conjecture, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_103, c_0_107])).
% 4.96/5.20  cnf(c_0_140, plain, (k1_tops_1(X1,k3_subset_1(u1_struct_0(X1),X2))=k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_129, c_0_71]), c_0_83])).
% 4.96/5.20  cnf(c_0_141, negated_conjecture, (k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0))=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_130, c_0_131]), c_0_39]), c_0_117]), c_0_41])])).
% 4.96/5.20  cnf(c_0_142, plain, (k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2))=k2_struct_0(X1)|~v1_tops_1(k3_subset_1(u1_struct_0(X1),X2),X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_132, c_0_83])).
% 4.96/5.20  cnf(c_0_143, negated_conjecture, (k3_subset_1(u1_struct_0(esk1_0),k1_xboole_0)=u1_struct_0(esk1_0)), inference(rw,[status(thm)],[c_0_79, c_0_107])).
% 4.96/5.20  cnf(c_0_144, negated_conjecture, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(rw,[status(thm)],[c_0_81, c_0_107])).
% 4.96/5.20  cnf(c_0_145, negated_conjecture, (v1_tops_1(u1_struct_0(esk1_0),esk1_0)|~v2_tops_1(k1_xboole_0,esk1_0)), inference(rw,[status(thm)],[c_0_133, c_0_107])).
% 4.96/5.20  cnf(c_0_146, negated_conjecture, (v2_tops_1(k1_xboole_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_134, c_0_101]), c_0_80])])).
% 4.96/5.20  cnf(c_0_147, negated_conjecture, (r1_tarski(k4_xboole_0(k3_subset_1(u1_struct_0(esk1_0),esk2_0),X1),u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_105, c_0_30])).
% 4.96/5.20  cnf(c_0_148, plain, (k3_subset_1(X1,X1)=k3_subset_1(X2,X2)|~r1_tarski(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_135, c_0_136]), c_0_39])])).
% 4.96/5.20  cnf(c_0_149, negated_conjecture, (r1_tarski(k1_xboole_0,k2_pre_topc(esk1_0,esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_137, c_0_138]), c_0_80]), c_0_41])])).
% 4.96/5.20  cnf(c_0_150, negated_conjecture, (k3_subset_1(k1_xboole_0,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_139, c_0_50])).
% 4.96/5.20  cnf(c_0_151, negated_conjecture, (k3_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0)))=k1_tops_1(esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_140, c_0_141]), c_0_80]), c_0_117])])).
% 4.96/5.20  cnf(c_0_152, negated_conjecture, (~v1_tops_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),esk1_0)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 4.96/5.20  cnf(c_0_153, negated_conjecture, (k2_struct_0(esk1_0)=k2_pre_topc(esk1_0,u1_struct_0(esk1_0))|~v1_tops_1(u1_struct_0(esk1_0),esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_142, c_0_143]), c_0_80]), c_0_144])])).
% 4.96/5.20  cnf(c_0_154, negated_conjecture, (v1_tops_1(u1_struct_0(esk1_0),esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_145, c_0_146])])).
% 4.96/5.20  cnf(c_0_155, negated_conjecture, (m1_subset_1(k4_xboole_0(k3_subset_1(u1_struct_0(esk1_0),esk2_0),X1),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_32, c_0_147])).
% 4.96/5.20  cnf(c_0_156, plain, (r1_tarski(X1,u1_struct_0(X2))|~l1_pre_topc(X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~r1_tarski(X1,k2_pre_topc(X2,X3))), inference(spm,[status(thm)],[c_0_40, c_0_99])).
% 4.96/5.20  cnf(c_0_157, negated_conjecture, (k3_subset_1(k2_pre_topc(esk1_0,esk2_0),k2_pre_topc(esk1_0,esk2_0))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_148, c_0_149]), c_0_150])).
% 4.96/5.20  cnf(c_0_158, plain, (r1_tarski(k3_subset_1(X1,X2),X3)|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_48, c_0_31])).
% 4.96/5.20  cnf(c_0_159, negated_conjecture, (k3_subset_1(u1_struct_0(esk1_0),k1_tops_1(esk1_0,esk2_0))=k2_pre_topc(esk1_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0))|~m1_subset_1(k2_pre_topc(esk1_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0)),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_71, c_0_151])).
% 4.96/5.20  cnf(c_0_160, negated_conjecture, (m1_subset_1(k1_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(k2_pre_topc(esk1_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0)),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_83, c_0_151])).
% 4.96/5.20  cnf(c_0_161, negated_conjecture, (k2_pre_topc(esk1_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0))!=k2_struct_0(esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_117]), c_0_80])]), c_0_152])).
% 4.96/5.20  cnf(c_0_162, negated_conjecture, (k2_struct_0(esk1_0)=k2_pre_topc(esk1_0,u1_struct_0(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_153, c_0_154])])).
% 4.96/5.20  cnf(c_0_163, negated_conjecture, (m1_subset_1(k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),X1),k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(X1,k1_zfmisc_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0)))), inference(spm,[status(thm)],[c_0_155, c_0_31])).
% 4.96/5.20  cnf(c_0_164, plain, (m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_32, c_0_76])).
% 4.96/5.20  cnf(c_0_165, negated_conjecture, (k1_tops_1(esk1_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0))=k3_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_129, c_0_141]), c_0_80]), c_0_117])])).
% 4.96/5.20  cnf(c_0_166, plain, (r1_tarski(k3_subset_1(k2_pre_topc(X1,X2),X3),u1_struct_0(X1))|~l1_pre_topc(X1)|~m1_subset_1(X3,k1_zfmisc_1(k2_pre_topc(X1,X2)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_156, c_0_38])).
% 4.96/5.20  cnf(c_0_167, negated_conjecture, (k3_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_xboole_0)=k2_pre_topc(esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_157]), c_0_39])])).
% 4.96/5.20  cnf(c_0_168, negated_conjecture, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_pre_topc(esk1_0,esk2_0)))), inference(spm,[status(thm)],[c_0_32, c_0_149])).
% 4.96/5.20  cnf(c_0_169, plain, (k3_subset_1(X1,X2)=X3|~m1_subset_1(X3,k1_zfmisc_1(k3_subset_1(X1,X2)))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_61, c_0_158])).
% 4.96/5.20  cnf(c_0_170, negated_conjecture, (k3_subset_1(u1_struct_0(esk1_0),k1_tops_1(esk1_0,esk2_0))=k2_pre_topc(esk1_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_159, c_0_99]), c_0_80]), c_0_117])])).
% 4.96/5.20  cnf(c_0_171, negated_conjecture, (m1_subset_1(k1_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_160, c_0_99]), c_0_80]), c_0_117])])).
% 4.96/5.20  cnf(c_0_172, negated_conjecture, (k2_pre_topc(esk1_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0))!=k2_pre_topc(esk1_0,u1_struct_0(esk1_0))), inference(rw,[status(thm)],[c_0_161, c_0_162])).
% 4.96/5.20  cnf(c_0_173, negated_conjecture, (k2_pre_topc(esk1_0,u1_struct_0(esk1_0))=u1_struct_0(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97, c_0_162]), c_0_80])])).
% 4.96/5.20  cnf(c_0_174, negated_conjecture, (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(X1,k1_zfmisc_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_163, c_0_71]), c_0_83])).
% 4.96/5.20  cnf(c_0_175, negated_conjecture, (m1_subset_1(k3_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0)),k1_zfmisc_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_164, c_0_165]), c_0_80]), c_0_117])])).
% 4.96/5.20  cnf(c_0_176, plain, (v1_tops_1(k1_tops_1(X1,X2),X1)|~v2_tops_1(k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2)),X1)|~l1_pre_topc(X1)|~m1_subset_1(k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2)),k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_126, c_0_129])).
% 4.96/5.20  cnf(c_0_177, negated_conjecture, (r1_tarski(k2_pre_topc(esk1_0,esk2_0),u1_struct_0(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_166, c_0_167]), c_0_80]), c_0_168]), c_0_41])])).
% 4.96/5.20  cnf(c_0_178, plain, (X1=X2|~m1_subset_1(X2,k1_zfmisc_1(X1))|~m1_subset_1(X1,k1_zfmisc_1(X3))|~r1_tarski(X3,X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_169, c_0_71]), c_0_83])).
% 4.96/5.20  cnf(c_0_179, negated_conjecture, (m1_subset_1(k2_pre_topc(esk1_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0)),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_170]), c_0_171])])).
% 4.96/5.20  cnf(c_0_180, negated_conjecture, (k2_pre_topc(esk1_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0))!=u1_struct_0(esk1_0)), inference(rw,[status(thm)],[c_0_172, c_0_173])).
% 4.96/5.20  fof(c_0_181, plain, ![X34, X35, X36]:(~l1_pre_topc(X34)|(~m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X34)))|(~m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X34)))|(~r1_tarski(X35,X36)|r1_tarski(k2_pre_topc(X34,X35),k2_pre_topc(X34,X36)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t49_pre_topc])])])).
% 4.96/5.20  cnf(c_0_182, negated_conjecture, (m1_subset_1(k3_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0)),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_174, c_0_175])).
% 4.96/5.20  cnf(c_0_183, plain, (v1_tops_1(k1_tops_1(X1,X2),X1)|~v3_tops_1(k3_subset_1(u1_struct_0(X1),X2),X1)|~l1_pre_topc(X1)|~m1_subset_1(k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2)),k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_176, c_0_128]), c_0_83])).
% 4.96/5.20  cnf(c_0_184, negated_conjecture, (m1_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_32, c_0_177])).
% 4.96/5.20  cnf(c_0_185, negated_conjecture, (~m1_subset_1(u1_struct_0(esk1_0),k1_zfmisc_1(X1))|~r1_tarski(X1,k2_pre_topc(esk1_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_178, c_0_179]), c_0_180])).
% 4.96/5.20  cnf(c_0_186, plain, (r1_tarski(k2_pre_topc(X1,X2),k2_pre_topc(X1,X3))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_181])).
% 4.96/5.20  cnf(c_0_187, negated_conjecture, (k2_pre_topc(esk1_0,k3_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0)))=u1_struct_0(esk1_0)|~v1_tops_1(k3_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0)),esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_132, c_0_182]), c_0_162]), c_0_173]), c_0_80])])).
% 4.96/5.20  cnf(c_0_188, negated_conjecture, (v1_tops_1(k3_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0)),esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_183, c_0_141]), c_0_165]), c_0_138]), c_0_80]), c_0_184]), c_0_117])])).
% 4.96/5.20  cnf(c_0_189, negated_conjecture, (~m1_subset_1(u1_struct_0(esk1_0),k1_zfmisc_1(k2_pre_topc(esk1_0,X1)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))|~r1_tarski(X1,k3_subset_1(u1_struct_0(esk1_0),esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_185, c_0_186]), c_0_80]), c_0_117])])).
% 4.96/5.20  cnf(c_0_190, negated_conjecture, (k2_pre_topc(esk1_0,k3_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0)))=u1_struct_0(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_187, c_0_188])])).
% 4.96/5.20  cnf(c_0_191, negated_conjecture, (r1_tarski(k3_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0)),k3_subset_1(u1_struct_0(esk1_0),esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_165]), c_0_80]), c_0_117])])).
% 4.96/5.20  cnf(c_0_192, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_189, c_0_190]), c_0_39]), c_0_182]), c_0_191])]), ['proof']).
% 4.96/5.20  # SZS output end CNFRefutation
% 4.96/5.20  # Proof object total steps             : 193
% 4.96/5.20  # Proof object clause steps            : 148
% 4.96/5.20  # Proof object formula steps           : 45
% 4.96/5.20  # Proof object conjectures             : 86
% 4.96/5.20  # Proof object clause conjectures      : 83
% 4.96/5.20  # Proof object formula conjectures     : 3
% 4.96/5.20  # Proof object initial clauses used    : 29
% 4.96/5.20  # Proof object initial formulas used   : 22
% 4.96/5.20  # Proof object generating inferences   : 108
% 4.96/5.20  # Proof object simplifying inferences  : 122
% 4.96/5.20  # Training examples: 0 positive, 0 negative
% 4.96/5.20  # Parsed axioms                        : 22
% 4.96/5.20  # Removed by relevancy pruning/SinE    : 0
% 4.96/5.20  # Initial clauses                      : 33
% 4.96/5.20  # Removed in clause preprocessing      : 0
% 4.96/5.20  # Initial clauses in saturation        : 33
% 4.96/5.20  # Processed clauses                    : 45884
% 4.96/5.20  # ...of these trivial                  : 232
% 4.96/5.20  # ...subsumed                          : 41756
% 4.96/5.20  # ...remaining for further processing  : 3896
% 4.96/5.20  # Other redundant clauses eliminated   : 2
% 4.96/5.20  # Clauses deleted for lack of memory   : 0
% 4.96/5.20  # Backward-subsumed                    : 267
% 4.96/5.20  # Backward-rewritten                   : 109
% 4.96/5.20  # Generated clauses                    : 425866
% 4.96/5.20  # ...of the previous two non-trivial   : 389567
% 4.96/5.20  # Contextual simplify-reflections      : 269
% 4.96/5.20  # Paramodulations                      : 425864
% 4.96/5.20  # Factorizations                       : 0
% 4.96/5.20  # Equation resolutions                 : 2
% 4.96/5.20  # Propositional unsat checks           : 0
% 4.96/5.20  #    Propositional check models        : 0
% 4.96/5.20  #    Propositional check unsatisfiable : 0
% 4.96/5.20  #    Propositional clauses             : 0
% 4.96/5.20  #    Propositional clauses after purity: 0
% 4.96/5.20  #    Propositional unsat core size     : 0
% 4.96/5.20  #    Propositional preprocessing time  : 0.000
% 4.96/5.20  #    Propositional encoding time       : 0.000
% 4.96/5.20  #    Propositional solver time         : 0.000
% 4.96/5.20  #    Success case prop preproc time    : 0.000
% 4.96/5.20  #    Success case prop encoding time   : 0.000
% 4.96/5.20  #    Success case prop solver time     : 0.000
% 4.96/5.20  # Current number of processed clauses  : 3486
% 4.96/5.20  #    Positive orientable unit clauses  : 147
% 4.96/5.20  #    Positive unorientable unit clauses: 0
% 4.96/5.20  #    Negative unit clauses             : 57
% 4.96/5.20  #    Non-unit-clauses                  : 3282
% 4.96/5.20  # Current number of unprocessed clauses: 342454
% 4.96/5.20  # ...number of literals in the above   : 1659077
% 4.96/5.20  # Current number of archived formulas  : 0
% 4.96/5.20  # Current number of archived clauses   : 408
% 4.96/5.20  # Clause-clause subsumption calls (NU) : 2167103
% 4.96/5.20  # Rec. Clause-clause subsumption calls : 782670
% 4.96/5.20  # Non-unit clause-clause subsumptions  : 16914
% 4.96/5.20  # Unit Clause-clause subsumption calls : 17219
% 4.96/5.20  # Rewrite failures with RHS unbound    : 0
% 4.96/5.20  # BW rewrite match attempts            : 289
% 4.96/5.20  # BW rewrite match successes           : 33
% 4.96/5.20  # Condensation attempts                : 0
% 4.96/5.20  # Condensation successes               : 0
% 4.96/5.20  # Termbank termtop insertions          : 9665137
% 5.05/5.22  
% 5.05/5.22  # -------------------------------------------------
% 5.05/5.22  # User time                : 4.727 s
% 5.05/5.22  # System time              : 0.144 s
% 5.05/5.22  # Total time               : 4.871 s
% 5.05/5.22  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
