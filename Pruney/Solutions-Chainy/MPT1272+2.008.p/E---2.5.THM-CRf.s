%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:12:15 EST 2020

% Result     : Theorem 0.38s
% Output     : CNFRefutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :  208 (207625 expanded)
%              Number of clauses        :  161 (101155 expanded)
%              Number of leaves         :   23 (52987 expanded)
%              Depth                    :   50
%              Number of atoms          :  510 (481198 expanded)
%              Number of equality atoms :   70 (65895 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(t109_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_tarski(k4_xboole_0(X1,X3),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t109_xboole_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(t36_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => ( r1_tarski(k3_subset_1(X1,X2),X3)
           => r1_tarski(k3_subset_1(X1,X3),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_subset_1)).

fof(involutiveness_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,k3_subset_1(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(dt_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(t35_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => ( r1_tarski(X2,k3_subset_1(X1,X3))
           => r1_tarski(X3,k3_subset_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_subset_1)).

fof(dt_k1_tops_1,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_1)).

fof(t84_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v2_tops_1(X2,X1)
          <=> k1_tops_1(X1,X2) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).

fof(t91_tops_1,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_tops_1(X2,X1)
           => v1_tops_1(k3_subset_1(u1_struct_0(X1),X2),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_tops_1)).

fof(rc5_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ? [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
          & v2_tops_1(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc5_tops_1)).

fof(t44_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => r1_tarski(k1_tops_1(X1,X2),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

fof(d4_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v2_tops_1(X2,X1)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(X1),X2),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_1)).

fof(d3_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => k2_struct_0(X1) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(d3_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v1_tops_1(X2,X1)
          <=> k2_pre_topc(X1,X2) = k2_struct_0(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_1)).

fof(t27_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => k2_pre_topc(X1,k2_struct_0(X1)) = k2_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_tops_1)).

fof(d1_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k1_tops_1(X1,X2) = k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).

fof(dt_k2_pre_topc,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(t49_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( r1_tarski(X2,X3)
               => r1_tarski(k2_pre_topc(X1,X2),k2_pre_topc(X1,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_pre_topc)).

fof(d5_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_tops_1(X2,X1)
          <=> v2_tops_1(k2_pre_topc(X1,X2),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tops_1)).

fof(c_0_23,plain,(
    ! [X4,X5] :
      ( ( r1_tarski(X4,X5)
        | X4 != X5 )
      & ( r1_tarski(X5,X4)
        | X4 != X5 )
      & ( ~ r1_tarski(X4,X5)
        | ~ r1_tarski(X5,X4)
        | X4 = X5 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_24,plain,(
    ! [X23,X24] :
      ( ( ~ m1_subset_1(X23,k1_zfmisc_1(X24))
        | r1_tarski(X23,X24) )
      & ( ~ r1_tarski(X23,X24)
        | m1_subset_1(X23,k1_zfmisc_1(X24)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_25,plain,(
    ! [X6,X7,X8] :
      ( ~ r1_tarski(X6,X7)
      | r1_tarski(k4_xboole_0(X6,X8),X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t109_xboole_1])])).

fof(c_0_26,plain,(
    ! [X9,X10] : r1_tarski(k4_xboole_0(X9,X10),X9) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

fof(c_0_27,plain,(
    ! [X11,X12] :
      ( ~ m1_subset_1(X12,k1_zfmisc_1(X11))
      | k3_subset_1(X11,X12) = k4_xboole_0(X11,X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

cnf(c_0_28,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_30,plain,
    ( r1_tarski(k4_xboole_0(X1,X3),X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_31,plain,(
    ! [X20,X21,X22] :
      ( ~ m1_subset_1(X21,k1_zfmisc_1(X20))
      | ~ m1_subset_1(X22,k1_zfmisc_1(X20))
      | ~ r1_tarski(k3_subset_1(X20,X21),X22)
      | r1_tarski(k3_subset_1(X20,X22),X21) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t36_subset_1])])])).

cnf(c_0_32,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_33,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_34,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_28])).

cnf(c_0_35,plain,
    ( m1_subset_1(k4_xboole_0(X1,X2),k1_zfmisc_1(X3))
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

fof(c_0_36,plain,(
    ! [X15,X16] :
      ( ~ m1_subset_1(X16,k1_zfmisc_1(X15))
      | k3_subset_1(X15,k3_subset_1(X15,X16)) = X16 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).

fof(c_0_37,plain,(
    ! [X13,X14] :
      ( ~ m1_subset_1(X14,k1_zfmisc_1(X13))
      | m1_subset_1(k3_subset_1(X13,X14),k1_zfmisc_1(X13)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).

cnf(c_0_38,plain,
    ( r1_tarski(k3_subset_1(X2,X3),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_tarski(k3_subset_1(X2,X1),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_39,plain,
    ( r1_tarski(k3_subset_1(X1,X2),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_40,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_34])).

cnf(c_0_41,plain,
    ( m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_35,c_0_33])).

cnf(c_0_42,plain,
    ( k3_subset_1(X2,k3_subset_1(X2,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_43,plain,
    ( m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_44,plain,
    ( r1_tarski(k3_subset_1(X1,X1),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40])])).

cnf(c_0_45,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3))
    | ~ r1_tarski(X3,X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_43])).

cnf(c_0_46,plain,
    ( m1_subset_1(k3_subset_1(X1,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_44])).

cnf(c_0_47,plain,
    ( m1_subset_1(k3_subset_1(X1,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_48,plain,
    ( m1_subset_1(k4_xboole_0(X1,X2),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_32])).

cnf(c_0_49,plain,
    ( m1_subset_1(k4_xboole_0(X1,X2),k1_zfmisc_1(X3))
    | ~ r1_tarski(X4,X3)
    | ~ r1_tarski(X1,X4) ),
    inference(spm,[status(thm)],[c_0_45,c_0_35])).

cnf(c_0_50,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_51,plain,
    ( m1_subset_1(k3_subset_1(X1,X1),k1_zfmisc_1(X2))
    | ~ r1_tarski(k4_xboole_0(X1,X3),X2) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_52,plain,
    ( r1_tarski(k3_subset_1(X1,X2),X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_30,c_0_33])).

fof(c_0_53,plain,(
    ! [X17,X18,X19] :
      ( ~ m1_subset_1(X18,k1_zfmisc_1(X17))
      | ~ m1_subset_1(X19,k1_zfmisc_1(X17))
      | ~ r1_tarski(X18,k3_subset_1(X17,X19))
      | r1_tarski(X19,k3_subset_1(X17,X18)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_subset_1])])])).

cnf(c_0_54,plain,
    ( m1_subset_1(k4_xboole_0(X1,X2),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
    | ~ r1_tarski(X1,X4) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_55,plain,
    ( m1_subset_1(k3_subset_1(X1,X1),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_32])).

cnf(c_0_56,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3))
    | ~ r1_tarski(X3,X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_42]),c_0_43])).

cnf(c_0_57,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_58,plain,
    ( r1_tarski(X3,k3_subset_1(X2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,k3_subset_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_59,plain,
    ( m1_subset_1(k4_xboole_0(X1,X2),k1_zfmisc_1(X3))
    | ~ r1_tarski(X1,k3_subset_1(X3,X3)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_60,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X4,X3)
    | ~ r1_tarski(X1,X4) ),
    inference(spm,[status(thm)],[c_0_56,c_0_35])).

cnf(c_0_61,plain,
    ( k3_subset_1(X1,X2) = X1
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_tarski(X1,k3_subset_1(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_57,c_0_39])).

cnf(c_0_62,plain,
    ( r1_tarski(X1,k3_subset_1(X2,k4_xboole_0(k3_subset_1(X2,X1),X3)))
    | ~ m1_subset_1(k4_xboole_0(k3_subset_1(X2,X1),X3),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_58,c_0_32])).

cnf(c_0_63,plain,
    ( m1_subset_1(k4_xboole_0(k3_subset_1(X1,X1),X2),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_34])).

cnf(c_0_64,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X1,k4_xboole_0(X3,X4)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_32])).

cnf(c_0_65,plain,
    ( k3_subset_1(X1,k4_xboole_0(k3_subset_1(X1,X1),X2)) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_63]),c_0_40])])).

cnf(c_0_66,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k4_xboole_0(X3,X4))) ),
    inference(spm,[status(thm)],[c_0_64,c_0_50])).

cnf(c_0_67,plain,
    ( k4_xboole_0(k3_subset_1(X1,X1),X2) = k3_subset_1(X1,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_65]),c_0_63])])).

cnf(c_0_68,plain,
    ( r1_tarski(k3_subset_1(X1,X1),X2)
    | ~ m1_subset_1(k4_xboole_0(X2,X3),k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_46]),c_0_67])).

cnf(c_0_69,plain,
    ( r1_tarski(k3_subset_1(X1,X1),X2)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_68,c_0_35])).

fof(c_0_70,plain,(
    ! [X40,X41] :
      ( ~ l1_pre_topc(X40)
      | ~ m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(X40)))
      | m1_subset_1(k1_tops_1(X40,X41),k1_zfmisc_1(u1_struct_0(X40))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_tops_1])])).

fof(c_0_71,plain,(
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

fof(c_0_72,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( v3_tops_1(X2,X1)
             => v1_tops_1(k3_subset_1(u1_struct_0(X1),X2),X1) ) ) ) ),
    inference(assume_negation,[status(cth)],[t91_tops_1])).

cnf(c_0_73,plain,
    ( r1_tarski(k3_subset_1(X1,X1),X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_56,c_0_46])).

cnf(c_0_74,plain,
    ( m1_subset_1(k3_subset_1(X1,X1),k1_zfmisc_1(X2))
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_69])).

cnf(c_0_75,plain,
    ( m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_76,plain,
    ( k1_tops_1(X2,X1) = k1_xboole_0
    | ~ v2_tops_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

fof(c_0_77,plain,(
    ! [X42] :
      ( ( m1_subset_1(esk1_1(X42),k1_zfmisc_1(u1_struct_0(X42)))
        | ~ l1_pre_topc(X42) )
      & ( v2_tops_1(esk1_1(X42),X42)
        | ~ l1_pre_topc(X42) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[rc5_tops_1])])])])).

fof(c_0_78,negated_conjecture,
    ( l1_pre_topc(esk2_0)
    & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
    & v3_tops_1(esk3_0,esk2_0)
    & ~ v1_tops_1(k3_subset_1(u1_struct_0(esk2_0),esk3_0),esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_72])])])).

cnf(c_0_79,plain,
    ( m1_subset_1(k3_subset_1(X1,X1),k1_zfmisc_1(k4_xboole_0(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_51,c_0_34])).

cnf(c_0_80,plain,
    ( r1_tarski(k3_subset_1(X1,X1),X2)
    | ~ r1_tarski(k3_subset_1(X3,X3),X2)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_81,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_tops_1(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_82,plain,
    ( v2_tops_1(esk1_1(X1),X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_77])).

cnf(c_0_83,plain,
    ( m1_subset_1(esk1_1(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_77])).

cnf(c_0_84,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_78])).

cnf(c_0_85,plain,
    ( r1_tarski(k3_subset_1(X1,X1),X2)
    | ~ r1_tarski(k4_xboole_0(X1,X3),X2) ),
    inference(spm,[status(thm)],[c_0_56,c_0_79])).

cnf(c_0_86,plain,
    ( r1_tarski(k3_subset_1(X1,X1),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_80,c_0_44])).

cnf(c_0_87,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_82]),c_0_83])).

cnf(c_0_88,negated_conjecture,
    ( r1_tarski(esk3_0,X1)
    | ~ r1_tarski(u1_struct_0(esk2_0),X1) ),
    inference(spm,[status(thm)],[c_0_56,c_0_84])).

cnf(c_0_89,plain,
    ( r1_tarski(k3_subset_1(X1,X1),X1) ),
    inference(spm,[status(thm)],[c_0_85,c_0_32])).

cnf(c_0_90,plain,
    ( r1_tarski(k3_subset_1(X1,X1),k1_xboole_0)
    | ~ l1_pre_topc(X2)
    | ~ r1_tarski(X1,u1_struct_0(X2)) ),
    inference(spm,[status(thm)],[c_0_86,c_0_87])).

cnf(c_0_91,negated_conjecture,
    ( r1_tarski(esk3_0,u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_88,c_0_34])).

cnf(c_0_92,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_78])).

cnf(c_0_93,plain,
    ( m1_subset_1(k3_subset_1(X1,X1),k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_47,c_0_40])).

cnf(c_0_94,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X1,k3_subset_1(X3,X3)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_89])).

cnf(c_0_95,plain,
    ( r1_tarski(k3_subset_1(X1,X1),X2)
    | ~ r1_tarski(X3,X2)
    | ~ r1_tarski(X3,X1) ),
    inference(spm,[status(thm)],[c_0_56,c_0_74])).

cnf(c_0_96,negated_conjecture,
    ( r1_tarski(k3_subset_1(esk3_0,esk3_0),k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_91]),c_0_92])])).

cnf(c_0_97,plain,
    ( r1_tarski(k3_subset_1(X1,X1),X2)
    | ~ r1_tarski(X3,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_56,c_0_93])).

cnf(c_0_98,plain,
    ( r1_tarski(k3_subset_1(X1,X1),X2)
    | ~ r1_tarski(k3_subset_1(X2,X2),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_69]),c_0_67])).

cnf(c_0_99,negated_conjecture,
    ( r1_tarski(k3_subset_1(X1,X1),k1_xboole_0)
    | ~ r1_tarski(k3_subset_1(esk3_0,esk3_0),X1) ),
    inference(spm,[status(thm)],[c_0_95,c_0_96])).

cnf(c_0_100,negated_conjecture,
    ( r1_tarski(k3_subset_1(X1,X1),u1_struct_0(esk2_0))
    | ~ r1_tarski(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_97,c_0_91])).

cnf(c_0_101,plain,
    ( r1_tarski(k3_subset_1(X1,X1),X2)
    | ~ r1_tarski(k3_subset_1(X3,X3),X2)
    | ~ r1_tarski(X3,X1) ),
    inference(spm,[status(thm)],[c_0_73,c_0_93])).

cnf(c_0_102,negated_conjecture,
    ( r1_tarski(k3_subset_1(k1_xboole_0,k1_xboole_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_98,c_0_96])).

cnf(c_0_103,negated_conjecture,
    ( r1_tarski(k3_subset_1(u1_struct_0(esk2_0),u1_struct_0(esk2_0)),k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_100]),c_0_34])])).

cnf(c_0_104,negated_conjecture,
    ( r1_tarski(k3_subset_1(X1,X1),esk3_0)
    | ~ r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_101,c_0_102])).

cnf(c_0_105,plain,
    ( r1_tarski(k1_xboole_0,X1)
    | ~ l1_pre_topc(X2)
    | ~ r1_tarski(u1_struct_0(X2),X1) ),
    inference(spm,[status(thm)],[c_0_56,c_0_87])).

cnf(c_0_106,negated_conjecture,
    ( r1_tarski(k3_subset_1(X1,X1),esk3_0)
    | ~ r1_tarski(k3_subset_1(k1_xboole_0,k1_xboole_0),X1) ),
    inference(spm,[status(thm)],[c_0_95,c_0_102])).

cnf(c_0_107,negated_conjecture,
    ( r1_tarski(k3_subset_1(k1_xboole_0,k1_xboole_0),u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_98,c_0_103])).

cnf(c_0_108,plain,
    ( X1 = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_57,c_0_50])).

cnf(c_0_109,negated_conjecture,
    ( r1_tarski(k3_subset_1(X1,X1),esk3_0)
    | ~ r1_tarski(k1_xboole_0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_80,c_0_104])).

cnf(c_0_110,plain,
    ( r1_tarski(k1_xboole_0,u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_105,c_0_34])).

cnf(c_0_111,negated_conjecture,
    ( r1_tarski(k3_subset_1(u1_struct_0(esk2_0),u1_struct_0(esk2_0)),esk3_0) ),
    inference(spm,[status(thm)],[c_0_106,c_0_107])).

cnf(c_0_112,plain,
    ( X1 = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_108,c_0_50])).

cnf(c_0_113,negated_conjecture,
    ( r1_tarski(k3_subset_1(X1,X1),esk3_0)
    | ~ l1_pre_topc(X2)
    | ~ r1_tarski(X1,u1_struct_0(X2)) ),
    inference(spm,[status(thm)],[c_0_109,c_0_110])).

cnf(c_0_114,negated_conjecture,
    ( r1_tarski(k3_subset_1(esk3_0,esk3_0),u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_98,c_0_111])).

cnf(c_0_115,plain,
    ( k3_subset_1(X1,X2) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(k3_subset_1(X1,X2)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_112,c_0_43])).

cnf(c_0_116,negated_conjecture,
    ( r1_tarski(k3_subset_1(k3_subset_1(esk3_0,esk3_0),k3_subset_1(esk3_0,esk3_0)),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113,c_0_114]),c_0_92])])).

cnf(c_0_117,plain,
    ( k3_subset_1(k3_subset_1(X1,X1),X2) = k3_subset_1(X1,X1)
    | ~ m1_subset_1(k3_subset_1(k3_subset_1(X1,X1),X2),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k3_subset_1(X1,X1))) ),
    inference(spm,[status(thm)],[c_0_115,c_0_46])).

cnf(c_0_118,negated_conjecture,
    ( m1_subset_1(k3_subset_1(k3_subset_1(esk3_0,esk3_0),k3_subset_1(esk3_0,esk3_0)),k1_zfmisc_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_116])).

fof(c_0_119,plain,(
    ! [X45,X46] :
      ( ~ l1_pre_topc(X45)
      | ~ m1_subset_1(X46,k1_zfmisc_1(u1_struct_0(X45)))
      | r1_tarski(k1_tops_1(X45,X46),X46) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_tops_1])])])).

fof(c_0_120,plain,(
    ! [X36,X37] :
      ( ( ~ v2_tops_1(X37,X36)
        | v1_tops_1(k3_subset_1(u1_struct_0(X36),X37),X36)
        | ~ m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X36)))
        | ~ l1_pre_topc(X36) )
      & ( ~ v1_tops_1(k3_subset_1(u1_struct_0(X36),X37),X36)
        | v2_tops_1(X37,X36)
        | ~ m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X36)))
        | ~ l1_pre_topc(X36) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tops_1])])])])).

cnf(c_0_121,plain,
    ( X1 = k3_subset_1(X2,X2)
    | ~ r1_tarski(X1,k3_subset_1(X2,X2))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_57,c_0_69])).

cnf(c_0_122,negated_conjecture,
    ( k3_subset_1(k3_subset_1(esk3_0,esk3_0),k3_subset_1(esk3_0,esk3_0)) = k3_subset_1(esk3_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117,c_0_118]),c_0_40])])).

cnf(c_0_123,negated_conjecture,
    ( m1_subset_1(k4_xboole_0(X1,X2),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ r1_tarski(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_54,c_0_84])).

cnf(c_0_124,plain,
    ( r1_tarski(k1_tops_1(X1,X2),X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_119])).

cnf(c_0_125,plain,
    ( v2_tops_1(X2,X1)
    | ~ v1_tops_1(k3_subset_1(u1_struct_0(X1),X2),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_120])).

cnf(c_0_126,negated_conjecture,
    ( X1 = k3_subset_1(esk3_0,esk3_0)
    | ~ r1_tarski(X1,k3_subset_1(esk3_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_121,c_0_122])).

cnf(c_0_127,negated_conjecture,
    ( r1_tarski(k3_subset_1(u1_struct_0(esk2_0),u1_struct_0(esk2_0)),X1)
    | ~ r1_tarski(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_68,c_0_123])).

cnf(c_0_128,plain,
    ( k1_tops_1(X1,X2) = X2
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_tops_1(X1,X2)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_108,c_0_124])).

cnf(c_0_129,plain,
    ( v2_tops_1(k3_subset_1(u1_struct_0(X1),X2),X1)
    | ~ v1_tops_1(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_125,c_0_42]),c_0_43])).

cnf(c_0_130,negated_conjecture,
    ( k3_subset_1(u1_struct_0(esk2_0),u1_struct_0(esk2_0)) = k3_subset_1(esk3_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_126,c_0_127]),c_0_89])])).

cnf(c_0_131,plain,
    ( m1_subset_1(k3_subset_1(X1,X1),k1_zfmisc_1(X2))
    | ~ r1_tarski(k3_subset_1(X2,X2),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_69]),c_0_67])).

fof(c_0_132,plain,(
    ! [X25] :
      ( ~ l1_struct_0(X25)
      | k2_struct_0(X25) = u1_struct_0(X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

fof(c_0_133,plain,(
    ! [X28] :
      ( ~ l1_pre_topc(X28)
      | l1_struct_0(X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_134,plain,
    ( k1_xboole_0 = X1
    | ~ v2_tops_1(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_128,c_0_76])).

cnf(c_0_135,negated_conjecture,
    ( v2_tops_1(k3_subset_1(esk3_0,esk3_0),esk2_0)
    | ~ v1_tops_1(u1_struct_0(esk2_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_129,c_0_130]),c_0_92]),c_0_40])])).

cnf(c_0_136,negated_conjecture,
    ( m1_subset_1(k3_subset_1(esk3_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_131,c_0_111])).

cnf(c_0_137,negated_conjecture,
    ( m1_subset_1(k3_subset_1(esk3_0,esk3_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_96])).

fof(c_0_138,plain,(
    ! [X34,X35] :
      ( ( ~ v1_tops_1(X35,X34)
        | k2_pre_topc(X34,X35) = k2_struct_0(X34)
        | ~ m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X34)))
        | ~ l1_pre_topc(X34) )
      & ( k2_pre_topc(X34,X35) != k2_struct_0(X34)
        | v1_tops_1(X35,X34)
        | ~ m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X34)))
        | ~ l1_pre_topc(X34) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tops_1])])])])).

fof(c_0_139,plain,(
    ! [X44] :
      ( ~ l1_pre_topc(X44)
      | k2_pre_topc(X44,k2_struct_0(X44)) = k2_struct_0(X44) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t27_tops_1])])).

cnf(c_0_140,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_132])).

cnf(c_0_141,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_133])).

cnf(c_0_142,negated_conjecture,
    ( k3_subset_1(esk3_0,esk3_0) = k1_xboole_0
    | ~ v1_tops_1(u1_struct_0(esk2_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_134,c_0_135]),c_0_92]),c_0_136]),c_0_137])])).

cnf(c_0_143,plain,
    ( v1_tops_1(X2,X1)
    | k2_pre_topc(X1,X2) != k2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_138])).

cnf(c_0_144,plain,
    ( k2_pre_topc(X1,k2_struct_0(X1)) = k2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_139])).

cnf(c_0_145,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_140,c_0_141])).

cnf(c_0_146,negated_conjecture,
    ( k3_subset_1(esk3_0,esk3_0) = k1_xboole_0
    | k2_pre_topc(esk2_0,u1_struct_0(esk2_0)) != k2_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_142,c_0_143]),c_0_92]),c_0_40])])).

cnf(c_0_147,plain,
    ( k2_pre_topc(X1,u1_struct_0(X1)) = u1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_144,c_0_145])).

cnf(c_0_148,plain,
    ( r1_tarski(k3_subset_1(X1,X1),X2)
    | ~ r1_tarski(X1,X3)
    | ~ r1_tarski(X2,X3) ),
    inference(spm,[status(thm)],[c_0_80,c_0_69])).

cnf(c_0_149,negated_conjecture,
    ( k3_subset_1(esk3_0,esk3_0) = k1_xboole_0
    | k2_struct_0(esk2_0) != u1_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_146,c_0_147]),c_0_92])])).

cnf(c_0_150,negated_conjecture,
    ( r1_tarski(k3_subset_1(esk3_0,esk3_0),X1)
    | ~ r1_tarski(X1,u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_148,c_0_91])).

cnf(c_0_151,negated_conjecture,
    ( k3_subset_1(esk3_0,esk3_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_149,c_0_145]),c_0_92])])).

cnf(c_0_152,negated_conjecture,
    ( r1_tarski(k3_subset_1(u1_struct_0(esk2_0),esk3_0),u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_111]),c_0_84]),c_0_40])])).

cnf(c_0_153,negated_conjecture,
    ( r1_tarski(k1_xboole_0,X1)
    | ~ r1_tarski(X1,u1_struct_0(esk2_0)) ),
    inference(rw,[status(thm)],[c_0_150,c_0_151])).

cnf(c_0_154,negated_conjecture,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_74,c_0_151])).

cnf(c_0_155,negated_conjecture,
    ( r1_tarski(k3_subset_1(k3_subset_1(u1_struct_0(esk2_0),esk3_0),k3_subset_1(u1_struct_0(esk2_0),esk3_0)),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113,c_0_152]),c_0_92])])).

cnf(c_0_156,negated_conjecture,
    ( r1_tarski(k1_xboole_0,k3_subset_1(u1_struct_0(esk2_0),esk3_0)) ),
    inference(spm,[status(thm)],[c_0_153,c_0_152])).

cnf(c_0_157,plain,
    ( k3_subset_1(X1,X1) = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(k3_subset_1(X1,X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_108,c_0_44])).

cnf(c_0_158,negated_conjecture,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k3_subset_1(k3_subset_1(u1_struct_0(esk2_0),esk3_0),k3_subset_1(u1_struct_0(esk2_0),esk3_0)))) ),
    inference(spm,[status(thm)],[c_0_154,c_0_155])).

cnf(c_0_159,negated_conjecture,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k3_subset_1(u1_struct_0(esk2_0),esk3_0))) ),
    inference(spm,[status(thm)],[c_0_29,c_0_156])).

cnf(c_0_160,negated_conjecture,
    ( k3_subset_1(k3_subset_1(u1_struct_0(esk2_0),esk3_0),k3_subset_1(u1_struct_0(esk2_0),esk3_0)) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_157,c_0_158]),c_0_159])])).

cnf(c_0_161,plain,
    ( v1_tops_1(k3_subset_1(u1_struct_0(X2),X1),X2)
    | ~ v2_tops_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_120])).

cnf(c_0_162,plain,
    ( r1_tarski(X1,k3_subset_1(X2,k3_subset_1(k3_subset_1(X2,X1),X3)))
    | ~ m1_subset_1(k3_subset_1(k3_subset_1(X2,X1),X3),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k3_subset_1(X2,X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_58,c_0_39])).

cnf(c_0_163,negated_conjecture,
    ( k3_subset_1(k3_subset_1(u1_struct_0(esk2_0),esk3_0),k1_xboole_0) = k3_subset_1(u1_struct_0(esk2_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_160]),c_0_40])])).

cnf(c_0_164,negated_conjecture,
    ( m1_subset_1(k3_subset_1(u1_struct_0(esk2_0),esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_29,c_0_152])).

cnf(c_0_165,plain,
    ( v1_tops_1(X1,X2)
    | ~ v2_tops_1(k3_subset_1(u1_struct_0(X2),X1),X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_161,c_0_42]),c_0_43])).

fof(c_0_166,plain,(
    ! [X32,X33] :
      ( ~ l1_pre_topc(X32)
      | ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))
      | k1_tops_1(X32,X33) = k3_subset_1(u1_struct_0(X32),k2_pre_topc(X32,k3_subset_1(u1_struct_0(X32),X33))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tops_1])])])).

cnf(c_0_167,negated_conjecture,
    ( r1_tarski(esk3_0,k3_subset_1(u1_struct_0(esk2_0),k3_subset_1(u1_struct_0(esk2_0),esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_162,c_0_163]),c_0_164]),c_0_159]),c_0_84])])).

cnf(c_0_168,negated_conjecture,
    ( v1_tops_1(u1_struct_0(esk2_0),esk2_0)
    | ~ v2_tops_1(k3_subset_1(esk3_0,esk3_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_165,c_0_130]),c_0_92]),c_0_40])])).

cnf(c_0_169,negated_conjecture,
    ( v2_tops_1(k1_xboole_0,esk2_0)
    | ~ v1_tops_1(u1_struct_0(esk2_0),esk2_0) ),
    inference(rw,[status(thm)],[c_0_135,c_0_151])).

cnf(c_0_170,plain,
    ( k1_tops_1(X1,X2) = k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_166])).

cnf(c_0_171,negated_conjecture,
    ( k3_subset_1(u1_struct_0(esk2_0),k3_subset_1(u1_struct_0(esk2_0),esk3_0)) = esk3_0
    | ~ r1_tarski(k3_subset_1(u1_struct_0(esk2_0),k3_subset_1(u1_struct_0(esk2_0),esk3_0)),esk3_0) ),
    inference(spm,[status(thm)],[c_0_57,c_0_167])).

cnf(c_0_172,plain,
    ( r1_tarski(k3_subset_1(X1,X2),X3)
    | ~ m1_subset_1(k3_subset_1(X1,X3),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_50])).

cnf(c_0_173,plain,
    ( k2_pre_topc(X2,X1) = k2_struct_0(X2)
    | ~ v1_tops_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_138])).

cnf(c_0_174,negated_conjecture,
    ( v1_tops_1(u1_struct_0(esk2_0),esk2_0)
    | ~ v2_tops_1(k1_xboole_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_168,c_0_151])).

cnf(c_0_175,negated_conjecture,
    ( v2_tops_1(k1_xboole_0,esk2_0)
    | k2_pre_topc(esk2_0,u1_struct_0(esk2_0)) != k2_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_169,c_0_143]),c_0_92]),c_0_40])])).

cnf(c_0_176,plain,
    ( k1_tops_1(X1,k3_subset_1(u1_struct_0(X1),X2)) = k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_170,c_0_42]),c_0_43])).

cnf(c_0_177,negated_conjecture,
    ( k3_subset_1(u1_struct_0(esk2_0),k3_subset_1(u1_struct_0(esk2_0),esk3_0)) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_171,c_0_172]),c_0_40]),c_0_164]),c_0_84])])).

fof(c_0_178,plain,(
    ! [X26,X27] :
      ( ~ l1_pre_topc(X26)
      | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))
      | m1_subset_1(k2_pre_topc(X26,X27),k1_zfmisc_1(u1_struct_0(X26))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).

cnf(c_0_179,negated_conjecture,
    ( ~ v1_tops_1(k3_subset_1(u1_struct_0(esk2_0),esk3_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_78])).

cnf(c_0_180,negated_conjecture,
    ( k2_pre_topc(esk2_0,u1_struct_0(esk2_0)) = k2_struct_0(esk2_0)
    | ~ v2_tops_1(k1_xboole_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_173,c_0_174]),c_0_92]),c_0_40])])).

cnf(c_0_181,negated_conjecture,
    ( v2_tops_1(k1_xboole_0,esk2_0)
    | k2_struct_0(esk2_0) != u1_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_175,c_0_147]),c_0_92])])).

cnf(c_0_182,negated_conjecture,
    ( k3_subset_1(u1_struct_0(esk2_0),k2_pre_topc(esk2_0,k3_subset_1(u1_struct_0(esk2_0),esk3_0))) = k1_tops_1(esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_176,c_0_177]),c_0_92]),c_0_164])])).

cnf(c_0_183,plain,
    ( m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_178])).

cnf(c_0_184,negated_conjecture,
    ( k2_pre_topc(esk2_0,k3_subset_1(u1_struct_0(esk2_0),esk3_0)) != k2_struct_0(esk2_0)
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(esk2_0),esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_179,c_0_143]),c_0_92])])).

cnf(c_0_185,negated_conjecture,
    ( k2_struct_0(esk2_0) = u1_struct_0(esk2_0)
    | ~ v2_tops_1(k1_xboole_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_147,c_0_180]),c_0_92])])).

cnf(c_0_186,negated_conjecture,
    ( v2_tops_1(k1_xboole_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_181,c_0_145]),c_0_92])])).

fof(c_0_187,plain,(
    ! [X29,X30,X31] :
      ( ~ l1_pre_topc(X29)
      | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))
      | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X29)))
      | ~ r1_tarski(X30,X31)
      | r1_tarski(k2_pre_topc(X29,X30),k2_pre_topc(X29,X31)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t49_pre_topc])])])).

cnf(c_0_188,negated_conjecture,
    ( k3_subset_1(u1_struct_0(esk2_0),k1_tops_1(esk2_0,esk3_0)) = k2_pre_topc(esk2_0,k3_subset_1(u1_struct_0(esk2_0),esk3_0))
    | ~ m1_subset_1(k2_pre_topc(esk2_0,k3_subset_1(u1_struct_0(esk2_0),esk3_0)),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_42,c_0_182])).

cnf(c_0_189,plain,
    ( m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(u1_struct_0(X1),X3) ),
    inference(spm,[status(thm)],[c_0_45,c_0_183])).

cnf(c_0_190,negated_conjecture,
    ( m1_subset_1(k1_tops_1(esk2_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ m1_subset_1(k2_pre_topc(esk2_0,k3_subset_1(u1_struct_0(esk2_0),esk3_0)),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_43,c_0_182])).

cnf(c_0_191,negated_conjecture,
    ( k2_pre_topc(esk2_0,k3_subset_1(u1_struct_0(esk2_0),esk3_0)) != k2_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_184,c_0_164])])).

cnf(c_0_192,negated_conjecture,
    ( k2_struct_0(esk2_0) = u1_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_185,c_0_186])])).

cnf(c_0_193,plain,
    ( r1_tarski(k2_pre_topc(X1,X2),k2_pre_topc(X1,X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_187])).

cnf(c_0_194,plain,
    ( k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2)) = k2_struct_0(X1)
    | ~ v2_tops_1(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_173,c_0_161]),c_0_43])).

cnf(c_0_195,negated_conjecture,
    ( k1_tops_1(esk2_0,k3_subset_1(u1_struct_0(esk2_0),esk3_0)) = k3_subset_1(u1_struct_0(esk2_0),k2_pre_topc(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_170,c_0_177]),c_0_92]),c_0_164])])).

cnf(c_0_196,negated_conjecture,
    ( k3_subset_1(u1_struct_0(esk2_0),k1_tops_1(esk2_0,esk3_0)) = k2_pre_topc(esk2_0,k3_subset_1(u1_struct_0(esk2_0),esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_188,c_0_189]),c_0_92]),c_0_164]),c_0_34])])).

cnf(c_0_197,negated_conjecture,
    ( m1_subset_1(k1_tops_1(esk2_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_190,c_0_183]),c_0_92]),c_0_164])])).

cnf(c_0_198,negated_conjecture,
    ( k2_pre_topc(esk2_0,k3_subset_1(u1_struct_0(esk2_0),esk3_0)) != u1_struct_0(esk2_0) ),
    inference(rw,[status(thm)],[c_0_191,c_0_192])).

cnf(c_0_199,plain,
    ( r1_tarski(k2_struct_0(X1),k2_pre_topc(X1,X2))
    | ~ v2_tops_1(X3,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(k3_subset_1(u1_struct_0(X1),X3),X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_193,c_0_194]),c_0_43])).

cnf(c_0_200,negated_conjecture,
    ( r1_tarski(k3_subset_1(u1_struct_0(esk2_0),k2_pre_topc(esk2_0,esk3_0)),k3_subset_1(u1_struct_0(esk2_0),esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_124,c_0_195]),c_0_92]),c_0_164])])).

cnf(c_0_201,negated_conjecture,
    ( ~ r1_tarski(u1_struct_0(esk2_0),k2_pre_topc(esk2_0,k3_subset_1(u1_struct_0(esk2_0),esk3_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_196]),c_0_197])]),c_0_198])).

fof(c_0_202,plain,(
    ! [X38,X39] :
      ( ( ~ v3_tops_1(X39,X38)
        | v2_tops_1(k2_pre_topc(X38,X39),X38)
        | ~ m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(X38)))
        | ~ l1_pre_topc(X38) )
      & ( ~ v2_tops_1(k2_pre_topc(X38,X39),X38)
        | v3_tops_1(X39,X38)
        | ~ m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(X38)))
        | ~ l1_pre_topc(X38) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_tops_1])])])])).

cnf(c_0_203,negated_conjecture,
    ( ~ v2_tops_1(k2_pre_topc(esk2_0,esk3_0),esk2_0)
    | ~ m1_subset_1(k2_pre_topc(esk2_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_199,c_0_200]),c_0_192]),c_0_92]),c_0_164])]),c_0_201])).

cnf(c_0_204,plain,
    ( v2_tops_1(k2_pre_topc(X2,X1),X2)
    | ~ v3_tops_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_202])).

cnf(c_0_205,negated_conjecture,
    ( v3_tops_1(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_78])).

cnf(c_0_206,negated_conjecture,
    ( ~ m1_subset_1(k2_pre_topc(esk2_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_203,c_0_204]),c_0_205]),c_0_92]),c_0_84])])).

cnf(c_0_207,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_206,c_0_189]),c_0_92]),c_0_84]),c_0_34])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n019.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:45:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.38/0.62  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.38/0.62  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.38/0.62  #
% 0.38/0.62  # Preprocessing time       : 0.030 s
% 0.38/0.62  # Presaturation interreduction done
% 0.38/0.62  
% 0.38/0.62  # Proof found!
% 0.38/0.62  # SZS status Theorem
% 0.38/0.62  # SZS output start CNFRefutation
% 0.38/0.62  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.38/0.62  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.38/0.62  fof(t109_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_tarski(k4_xboole_0(X1,X3),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t109_xboole_1)).
% 0.38/0.62  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.38/0.62  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 0.38/0.62  fof(t36_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(r1_tarski(k3_subset_1(X1,X2),X3)=>r1_tarski(k3_subset_1(X1,X3),X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_subset_1)).
% 0.38/0.62  fof(involutiveness_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,k3_subset_1(X1,X2))=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 0.38/0.62  fof(dt_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 0.38/0.62  fof(t35_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(r1_tarski(X2,k3_subset_1(X1,X3))=>r1_tarski(X3,k3_subset_1(X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_subset_1)).
% 0.38/0.62  fof(dt_k1_tops_1, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tops_1)).
% 0.38/0.62  fof(t84_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v2_tops_1(X2,X1)<=>k1_tops_1(X1,X2)=k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_tops_1)).
% 0.38/0.62  fof(t91_tops_1, conjecture, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_tops_1(X2,X1)=>v1_tops_1(k3_subset_1(u1_struct_0(X1),X2),X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_tops_1)).
% 0.38/0.62  fof(rc5_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>?[X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))&v2_tops_1(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc5_tops_1)).
% 0.38/0.62  fof(t44_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>r1_tarski(k1_tops_1(X1,X2),X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_1)).
% 0.38/0.62  fof(d4_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v2_tops_1(X2,X1)<=>v1_tops_1(k3_subset_1(u1_struct_0(X1),X2),X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tops_1)).
% 0.38/0.62  fof(d3_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>k2_struct_0(X1)=u1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 0.38/0.62  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.38/0.62  fof(d3_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v1_tops_1(X2,X1)<=>k2_pre_topc(X1,X2)=k2_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tops_1)).
% 0.38/0.62  fof(t27_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>k2_pre_topc(X1,k2_struct_0(X1))=k2_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_tops_1)).
% 0.38/0.62  fof(d1_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k1_tops_1(X1,X2)=k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tops_1)).
% 0.38/0.62  fof(dt_k2_pre_topc, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 0.38/0.62  fof(t49_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(r1_tarski(X2,X3)=>r1_tarski(k2_pre_topc(X1,X2),k2_pre_topc(X1,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_pre_topc)).
% 0.38/0.62  fof(d5_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_tops_1(X2,X1)<=>v2_tops_1(k2_pre_topc(X1,X2),X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tops_1)).
% 0.38/0.62  fof(c_0_23, plain, ![X4, X5]:(((r1_tarski(X4,X5)|X4!=X5)&(r1_tarski(X5,X4)|X4!=X5))&(~r1_tarski(X4,X5)|~r1_tarski(X5,X4)|X4=X5)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.38/0.62  fof(c_0_24, plain, ![X23, X24]:((~m1_subset_1(X23,k1_zfmisc_1(X24))|r1_tarski(X23,X24))&(~r1_tarski(X23,X24)|m1_subset_1(X23,k1_zfmisc_1(X24)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.38/0.62  fof(c_0_25, plain, ![X6, X7, X8]:(~r1_tarski(X6,X7)|r1_tarski(k4_xboole_0(X6,X8),X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t109_xboole_1])])).
% 0.38/0.62  fof(c_0_26, plain, ![X9, X10]:r1_tarski(k4_xboole_0(X9,X10),X9), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.38/0.62  fof(c_0_27, plain, ![X11, X12]:(~m1_subset_1(X12,k1_zfmisc_1(X11))|k3_subset_1(X11,X12)=k4_xboole_0(X11,X12)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 0.38/0.62  cnf(c_0_28, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.38/0.62  cnf(c_0_29, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.38/0.62  cnf(c_0_30, plain, (r1_tarski(k4_xboole_0(X1,X3),X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.38/0.62  fof(c_0_31, plain, ![X20, X21, X22]:(~m1_subset_1(X21,k1_zfmisc_1(X20))|(~m1_subset_1(X22,k1_zfmisc_1(X20))|(~r1_tarski(k3_subset_1(X20,X21),X22)|r1_tarski(k3_subset_1(X20,X22),X21)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t36_subset_1])])])).
% 0.38/0.62  cnf(c_0_32, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.38/0.62  cnf(c_0_33, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.38/0.62  cnf(c_0_34, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_28])).
% 0.38/0.62  cnf(c_0_35, plain, (m1_subset_1(k4_xboole_0(X1,X2),k1_zfmisc_1(X3))|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.38/0.62  fof(c_0_36, plain, ![X15, X16]:(~m1_subset_1(X16,k1_zfmisc_1(X15))|k3_subset_1(X15,k3_subset_1(X15,X16))=X16), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).
% 0.38/0.62  fof(c_0_37, plain, ![X13, X14]:(~m1_subset_1(X14,k1_zfmisc_1(X13))|m1_subset_1(k3_subset_1(X13,X14),k1_zfmisc_1(X13))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).
% 0.38/0.62  cnf(c_0_38, plain, (r1_tarski(k3_subset_1(X2,X3),X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_tarski(k3_subset_1(X2,X1),X3)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.38/0.62  cnf(c_0_39, plain, (r1_tarski(k3_subset_1(X1,X2),X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.38/0.62  cnf(c_0_40, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_29, c_0_34])).
% 0.38/0.62  cnf(c_0_41, plain, (m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X3))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_35, c_0_33])).
% 0.38/0.62  cnf(c_0_42, plain, (k3_subset_1(X2,k3_subset_1(X2,X1))=X1|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.38/0.62  cnf(c_0_43, plain, (m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.38/0.62  cnf(c_0_44, plain, (r1_tarski(k3_subset_1(X1,X1),X2)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_40])])).
% 0.38/0.62  cnf(c_0_45, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X3))|~r1_tarski(X3,X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_43])).
% 0.38/0.62  cnf(c_0_46, plain, (m1_subset_1(k3_subset_1(X1,X1),k1_zfmisc_1(X2))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_29, c_0_44])).
% 0.38/0.62  cnf(c_0_47, plain, (m1_subset_1(k3_subset_1(X1,X1),k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.38/0.62  cnf(c_0_48, plain, (m1_subset_1(k4_xboole_0(X1,X2),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_29, c_0_32])).
% 0.38/0.62  cnf(c_0_49, plain, (m1_subset_1(k4_xboole_0(X1,X2),k1_zfmisc_1(X3))|~r1_tarski(X4,X3)|~r1_tarski(X1,X4)), inference(spm,[status(thm)],[c_0_45, c_0_35])).
% 0.38/0.62  cnf(c_0_50, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.38/0.62  cnf(c_0_51, plain, (m1_subset_1(k3_subset_1(X1,X1),k1_zfmisc_1(X2))|~r1_tarski(k4_xboole_0(X1,X3),X2)), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.38/0.62  cnf(c_0_52, plain, (r1_tarski(k3_subset_1(X1,X2),X3)|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_30, c_0_33])).
% 0.38/0.62  fof(c_0_53, plain, ![X17, X18, X19]:(~m1_subset_1(X18,k1_zfmisc_1(X17))|(~m1_subset_1(X19,k1_zfmisc_1(X17))|(~r1_tarski(X18,k3_subset_1(X17,X19))|r1_tarski(X19,k3_subset_1(X17,X18))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_subset_1])])])).
% 0.38/0.62  cnf(c_0_54, plain, (m1_subset_1(k4_xboole_0(X1,X2),k1_zfmisc_1(X3))|~m1_subset_1(X4,k1_zfmisc_1(X3))|~r1_tarski(X1,X4)), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.38/0.62  cnf(c_0_55, plain, (m1_subset_1(k3_subset_1(X1,X1),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_51, c_0_32])).
% 0.38/0.62  cnf(c_0_56, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X3))|~r1_tarski(X3,X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_42]), c_0_43])).
% 0.38/0.62  cnf(c_0_57, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.38/0.62  cnf(c_0_58, plain, (r1_tarski(X3,k3_subset_1(X2,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_tarski(X1,k3_subset_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.38/0.62  cnf(c_0_59, plain, (m1_subset_1(k4_xboole_0(X1,X2),k1_zfmisc_1(X3))|~r1_tarski(X1,k3_subset_1(X3,X3))), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.38/0.62  cnf(c_0_60, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|~r1_tarski(X4,X3)|~r1_tarski(X1,X4)), inference(spm,[status(thm)],[c_0_56, c_0_35])).
% 0.38/0.62  cnf(c_0_61, plain, (k3_subset_1(X1,X2)=X1|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_tarski(X1,k3_subset_1(X1,X2))), inference(spm,[status(thm)],[c_0_57, c_0_39])).
% 0.38/0.62  cnf(c_0_62, plain, (r1_tarski(X1,k3_subset_1(X2,k4_xboole_0(k3_subset_1(X2,X1),X3)))|~m1_subset_1(k4_xboole_0(k3_subset_1(X2,X1),X3),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_58, c_0_32])).
% 0.38/0.62  cnf(c_0_63, plain, (m1_subset_1(k4_xboole_0(k3_subset_1(X1,X1),X2),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_59, c_0_34])).
% 0.38/0.62  cnf(c_0_64, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|~r1_tarski(X1,k4_xboole_0(X3,X4))), inference(spm,[status(thm)],[c_0_60, c_0_32])).
% 0.38/0.62  cnf(c_0_65, plain, (k3_subset_1(X1,k4_xboole_0(k3_subset_1(X1,X1),X2))=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_63]), c_0_40])])).
% 0.38/0.62  cnf(c_0_66, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|~m1_subset_1(X1,k1_zfmisc_1(k4_xboole_0(X3,X4)))), inference(spm,[status(thm)],[c_0_64, c_0_50])).
% 0.38/0.62  cnf(c_0_67, plain, (k4_xboole_0(k3_subset_1(X1,X1),X2)=k3_subset_1(X1,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_65]), c_0_63])])).
% 0.38/0.62  cnf(c_0_68, plain, (r1_tarski(k3_subset_1(X1,X1),X2)|~m1_subset_1(k4_xboole_0(X2,X3),k1_zfmisc_1(X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_46]), c_0_67])).
% 0.38/0.62  cnf(c_0_69, plain, (r1_tarski(k3_subset_1(X1,X1),X2)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_68, c_0_35])).
% 0.38/0.62  fof(c_0_70, plain, ![X40, X41]:(~l1_pre_topc(X40)|~m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(X40)))|m1_subset_1(k1_tops_1(X40,X41),k1_zfmisc_1(u1_struct_0(X40)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_tops_1])])).
% 0.38/0.62  fof(c_0_71, plain, ![X47, X48]:((~v2_tops_1(X48,X47)|k1_tops_1(X47,X48)=k1_xboole_0|~m1_subset_1(X48,k1_zfmisc_1(u1_struct_0(X47)))|~l1_pre_topc(X47))&(k1_tops_1(X47,X48)!=k1_xboole_0|v2_tops_1(X48,X47)|~m1_subset_1(X48,k1_zfmisc_1(u1_struct_0(X47)))|~l1_pre_topc(X47))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t84_tops_1])])])])).
% 0.38/0.62  fof(c_0_72, negated_conjecture, ~(![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_tops_1(X2,X1)=>v1_tops_1(k3_subset_1(u1_struct_0(X1),X2),X1))))), inference(assume_negation,[status(cth)],[t91_tops_1])).
% 0.38/0.62  cnf(c_0_73, plain, (r1_tarski(k3_subset_1(X1,X1),X2)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_56, c_0_46])).
% 0.38/0.62  cnf(c_0_74, plain, (m1_subset_1(k3_subset_1(X1,X1),k1_zfmisc_1(X2))|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_29, c_0_69])).
% 0.38/0.62  cnf(c_0_75, plain, (m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_70])).
% 0.38/0.62  cnf(c_0_76, plain, (k1_tops_1(X2,X1)=k1_xboole_0|~v2_tops_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_71])).
% 0.38/0.62  fof(c_0_77, plain, ![X42]:((m1_subset_1(esk1_1(X42),k1_zfmisc_1(u1_struct_0(X42)))|~l1_pre_topc(X42))&(v2_tops_1(esk1_1(X42),X42)|~l1_pre_topc(X42))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[rc5_tops_1])])])])).
% 0.38/0.62  fof(c_0_78, negated_conjecture, (l1_pre_topc(esk2_0)&(m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))&(v3_tops_1(esk3_0,esk2_0)&~v1_tops_1(k3_subset_1(u1_struct_0(esk2_0),esk3_0),esk2_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_72])])])).
% 0.38/0.62  cnf(c_0_79, plain, (m1_subset_1(k3_subset_1(X1,X1),k1_zfmisc_1(k4_xboole_0(X1,X2)))), inference(spm,[status(thm)],[c_0_51, c_0_34])).
% 0.38/0.62  cnf(c_0_80, plain, (r1_tarski(k3_subset_1(X1,X1),X2)|~r1_tarski(k3_subset_1(X3,X3),X2)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_73, c_0_74])).
% 0.38/0.62  cnf(c_0_81, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X1)))|~v2_tops_1(X2,X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_75, c_0_76])).
% 0.38/0.62  cnf(c_0_82, plain, (v2_tops_1(esk1_1(X1),X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_77])).
% 0.38/0.62  cnf(c_0_83, plain, (m1_subset_1(esk1_1(X1),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_77])).
% 0.38/0.62  cnf(c_0_84, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_78])).
% 0.38/0.62  cnf(c_0_85, plain, (r1_tarski(k3_subset_1(X1,X1),X2)|~r1_tarski(k4_xboole_0(X1,X3),X2)), inference(spm,[status(thm)],[c_0_56, c_0_79])).
% 0.38/0.62  cnf(c_0_86, plain, (r1_tarski(k3_subset_1(X1,X1),X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_80, c_0_44])).
% 0.38/0.62  cnf(c_0_87, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_82]), c_0_83])).
% 0.38/0.62  cnf(c_0_88, negated_conjecture, (r1_tarski(esk3_0,X1)|~r1_tarski(u1_struct_0(esk2_0),X1)), inference(spm,[status(thm)],[c_0_56, c_0_84])).
% 0.38/0.62  cnf(c_0_89, plain, (r1_tarski(k3_subset_1(X1,X1),X1)), inference(spm,[status(thm)],[c_0_85, c_0_32])).
% 0.38/0.62  cnf(c_0_90, plain, (r1_tarski(k3_subset_1(X1,X1),k1_xboole_0)|~l1_pre_topc(X2)|~r1_tarski(X1,u1_struct_0(X2))), inference(spm,[status(thm)],[c_0_86, c_0_87])).
% 0.38/0.62  cnf(c_0_91, negated_conjecture, (r1_tarski(esk3_0,u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_88, c_0_34])).
% 0.38/0.62  cnf(c_0_92, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_78])).
% 0.38/0.62  cnf(c_0_93, plain, (m1_subset_1(k3_subset_1(X1,X1),k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_47, c_0_40])).
% 0.38/0.62  cnf(c_0_94, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|~r1_tarski(X1,k3_subset_1(X3,X3))), inference(spm,[status(thm)],[c_0_60, c_0_89])).
% 0.38/0.62  cnf(c_0_95, plain, (r1_tarski(k3_subset_1(X1,X1),X2)|~r1_tarski(X3,X2)|~r1_tarski(X3,X1)), inference(spm,[status(thm)],[c_0_56, c_0_74])).
% 0.38/0.62  cnf(c_0_96, negated_conjecture, (r1_tarski(k3_subset_1(esk3_0,esk3_0),k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_91]), c_0_92])])).
% 0.38/0.62  cnf(c_0_97, plain, (r1_tarski(k3_subset_1(X1,X1),X2)|~r1_tarski(X3,X2)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_56, c_0_93])).
% 0.38/0.62  cnf(c_0_98, plain, (r1_tarski(k3_subset_1(X1,X1),X2)|~r1_tarski(k3_subset_1(X2,X2),X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_69]), c_0_67])).
% 0.38/0.62  cnf(c_0_99, negated_conjecture, (r1_tarski(k3_subset_1(X1,X1),k1_xboole_0)|~r1_tarski(k3_subset_1(esk3_0,esk3_0),X1)), inference(spm,[status(thm)],[c_0_95, c_0_96])).
% 0.38/0.62  cnf(c_0_100, negated_conjecture, (r1_tarski(k3_subset_1(X1,X1),u1_struct_0(esk2_0))|~r1_tarski(X1,esk3_0)), inference(spm,[status(thm)],[c_0_97, c_0_91])).
% 0.38/0.62  cnf(c_0_101, plain, (r1_tarski(k3_subset_1(X1,X1),X2)|~r1_tarski(k3_subset_1(X3,X3),X2)|~r1_tarski(X3,X1)), inference(spm,[status(thm)],[c_0_73, c_0_93])).
% 0.38/0.62  cnf(c_0_102, negated_conjecture, (r1_tarski(k3_subset_1(k1_xboole_0,k1_xboole_0),esk3_0)), inference(spm,[status(thm)],[c_0_98, c_0_96])).
% 0.38/0.62  cnf(c_0_103, negated_conjecture, (r1_tarski(k3_subset_1(u1_struct_0(esk2_0),u1_struct_0(esk2_0)),k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_100]), c_0_34])])).
% 0.38/0.62  cnf(c_0_104, negated_conjecture, (r1_tarski(k3_subset_1(X1,X1),esk3_0)|~r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_101, c_0_102])).
% 0.38/0.62  cnf(c_0_105, plain, (r1_tarski(k1_xboole_0,X1)|~l1_pre_topc(X2)|~r1_tarski(u1_struct_0(X2),X1)), inference(spm,[status(thm)],[c_0_56, c_0_87])).
% 0.38/0.62  cnf(c_0_106, negated_conjecture, (r1_tarski(k3_subset_1(X1,X1),esk3_0)|~r1_tarski(k3_subset_1(k1_xboole_0,k1_xboole_0),X1)), inference(spm,[status(thm)],[c_0_95, c_0_102])).
% 0.38/0.62  cnf(c_0_107, negated_conjecture, (r1_tarski(k3_subset_1(k1_xboole_0,k1_xboole_0),u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_98, c_0_103])).
% 0.38/0.62  cnf(c_0_108, plain, (X1=X2|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_57, c_0_50])).
% 0.38/0.62  cnf(c_0_109, negated_conjecture, (r1_tarski(k3_subset_1(X1,X1),esk3_0)|~r1_tarski(k1_xboole_0,X2)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_80, c_0_104])).
% 0.38/0.62  cnf(c_0_110, plain, (r1_tarski(k1_xboole_0,u1_struct_0(X1))|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_105, c_0_34])).
% 0.38/0.62  cnf(c_0_111, negated_conjecture, (r1_tarski(k3_subset_1(u1_struct_0(esk2_0),u1_struct_0(esk2_0)),esk3_0)), inference(spm,[status(thm)],[c_0_106, c_0_107])).
% 0.38/0.62  cnf(c_0_112, plain, (X1=X2|~m1_subset_1(X2,k1_zfmisc_1(X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_108, c_0_50])).
% 0.38/0.62  cnf(c_0_113, negated_conjecture, (r1_tarski(k3_subset_1(X1,X1),esk3_0)|~l1_pre_topc(X2)|~r1_tarski(X1,u1_struct_0(X2))), inference(spm,[status(thm)],[c_0_109, c_0_110])).
% 0.38/0.62  cnf(c_0_114, negated_conjecture, (r1_tarski(k3_subset_1(esk3_0,esk3_0),u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_98, c_0_111])).
% 0.38/0.62  cnf(c_0_115, plain, (k3_subset_1(X1,X2)=X1|~m1_subset_1(X1,k1_zfmisc_1(k3_subset_1(X1,X2)))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_112, c_0_43])).
% 0.38/0.62  cnf(c_0_116, negated_conjecture, (r1_tarski(k3_subset_1(k3_subset_1(esk3_0,esk3_0),k3_subset_1(esk3_0,esk3_0)),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113, c_0_114]), c_0_92])])).
% 0.38/0.62  cnf(c_0_117, plain, (k3_subset_1(k3_subset_1(X1,X1),X2)=k3_subset_1(X1,X1)|~m1_subset_1(k3_subset_1(k3_subset_1(X1,X1),X2),k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(k3_subset_1(X1,X1)))), inference(spm,[status(thm)],[c_0_115, c_0_46])).
% 0.38/0.62  cnf(c_0_118, negated_conjecture, (m1_subset_1(k3_subset_1(k3_subset_1(esk3_0,esk3_0),k3_subset_1(esk3_0,esk3_0)),k1_zfmisc_1(esk3_0))), inference(spm,[status(thm)],[c_0_29, c_0_116])).
% 0.38/0.62  fof(c_0_119, plain, ![X45, X46]:(~l1_pre_topc(X45)|(~m1_subset_1(X46,k1_zfmisc_1(u1_struct_0(X45)))|r1_tarski(k1_tops_1(X45,X46),X46))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_tops_1])])])).
% 0.38/0.62  fof(c_0_120, plain, ![X36, X37]:((~v2_tops_1(X37,X36)|v1_tops_1(k3_subset_1(u1_struct_0(X36),X37),X36)|~m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X36)))|~l1_pre_topc(X36))&(~v1_tops_1(k3_subset_1(u1_struct_0(X36),X37),X36)|v2_tops_1(X37,X36)|~m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X36)))|~l1_pre_topc(X36))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tops_1])])])])).
% 0.38/0.62  cnf(c_0_121, plain, (X1=k3_subset_1(X2,X2)|~r1_tarski(X1,k3_subset_1(X2,X2))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_57, c_0_69])).
% 0.38/0.62  cnf(c_0_122, negated_conjecture, (k3_subset_1(k3_subset_1(esk3_0,esk3_0),k3_subset_1(esk3_0,esk3_0))=k3_subset_1(esk3_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117, c_0_118]), c_0_40])])).
% 0.38/0.62  cnf(c_0_123, negated_conjecture, (m1_subset_1(k4_xboole_0(X1,X2),k1_zfmisc_1(u1_struct_0(esk2_0)))|~r1_tarski(X1,esk3_0)), inference(spm,[status(thm)],[c_0_54, c_0_84])).
% 0.38/0.62  cnf(c_0_124, plain, (r1_tarski(k1_tops_1(X1,X2),X2)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_119])).
% 0.38/0.62  cnf(c_0_125, plain, (v2_tops_1(X2,X1)|~v1_tops_1(k3_subset_1(u1_struct_0(X1),X2),X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_120])).
% 0.38/0.62  cnf(c_0_126, negated_conjecture, (X1=k3_subset_1(esk3_0,esk3_0)|~r1_tarski(X1,k3_subset_1(esk3_0,esk3_0))), inference(spm,[status(thm)],[c_0_121, c_0_122])).
% 0.38/0.62  cnf(c_0_127, negated_conjecture, (r1_tarski(k3_subset_1(u1_struct_0(esk2_0),u1_struct_0(esk2_0)),X1)|~r1_tarski(X1,esk3_0)), inference(spm,[status(thm)],[c_0_68, c_0_123])).
% 0.38/0.62  cnf(c_0_128, plain, (k1_tops_1(X1,X2)=X2|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(k1_tops_1(X1,X2)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_108, c_0_124])).
% 0.38/0.62  cnf(c_0_129, plain, (v2_tops_1(k3_subset_1(u1_struct_0(X1),X2),X1)|~v1_tops_1(X2,X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_125, c_0_42]), c_0_43])).
% 0.38/0.62  cnf(c_0_130, negated_conjecture, (k3_subset_1(u1_struct_0(esk2_0),u1_struct_0(esk2_0))=k3_subset_1(esk3_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_126, c_0_127]), c_0_89])])).
% 0.38/0.62  cnf(c_0_131, plain, (m1_subset_1(k3_subset_1(X1,X1),k1_zfmisc_1(X2))|~r1_tarski(k3_subset_1(X2,X2),X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_69]), c_0_67])).
% 0.38/0.62  fof(c_0_132, plain, ![X25]:(~l1_struct_0(X25)|k2_struct_0(X25)=u1_struct_0(X25)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).
% 0.38/0.62  fof(c_0_133, plain, ![X28]:(~l1_pre_topc(X28)|l1_struct_0(X28)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.38/0.62  cnf(c_0_134, plain, (k1_xboole_0=X1|~v2_tops_1(X1,X2)|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_128, c_0_76])).
% 0.38/0.62  cnf(c_0_135, negated_conjecture, (v2_tops_1(k3_subset_1(esk3_0,esk3_0),esk2_0)|~v1_tops_1(u1_struct_0(esk2_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_129, c_0_130]), c_0_92]), c_0_40])])).
% 0.38/0.62  cnf(c_0_136, negated_conjecture, (m1_subset_1(k3_subset_1(esk3_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(spm,[status(thm)],[c_0_131, c_0_111])).
% 0.38/0.62  cnf(c_0_137, negated_conjecture, (m1_subset_1(k3_subset_1(esk3_0,esk3_0),k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_29, c_0_96])).
% 0.38/0.62  fof(c_0_138, plain, ![X34, X35]:((~v1_tops_1(X35,X34)|k2_pre_topc(X34,X35)=k2_struct_0(X34)|~m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X34)))|~l1_pre_topc(X34))&(k2_pre_topc(X34,X35)!=k2_struct_0(X34)|v1_tops_1(X35,X34)|~m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X34)))|~l1_pre_topc(X34))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tops_1])])])])).
% 0.38/0.62  fof(c_0_139, plain, ![X44]:(~l1_pre_topc(X44)|k2_pre_topc(X44,k2_struct_0(X44))=k2_struct_0(X44)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t27_tops_1])])).
% 0.38/0.62  cnf(c_0_140, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_132])).
% 0.38/0.62  cnf(c_0_141, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_133])).
% 0.38/0.62  cnf(c_0_142, negated_conjecture, (k3_subset_1(esk3_0,esk3_0)=k1_xboole_0|~v1_tops_1(u1_struct_0(esk2_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_134, c_0_135]), c_0_92]), c_0_136]), c_0_137])])).
% 0.38/0.62  cnf(c_0_143, plain, (v1_tops_1(X2,X1)|k2_pre_topc(X1,X2)!=k2_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_138])).
% 0.38/0.62  cnf(c_0_144, plain, (k2_pre_topc(X1,k2_struct_0(X1))=k2_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_139])).
% 0.38/0.62  cnf(c_0_145, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_140, c_0_141])).
% 0.38/0.62  cnf(c_0_146, negated_conjecture, (k3_subset_1(esk3_0,esk3_0)=k1_xboole_0|k2_pre_topc(esk2_0,u1_struct_0(esk2_0))!=k2_struct_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_142, c_0_143]), c_0_92]), c_0_40])])).
% 0.38/0.62  cnf(c_0_147, plain, (k2_pre_topc(X1,u1_struct_0(X1))=u1_struct_0(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_144, c_0_145])).
% 0.38/0.62  cnf(c_0_148, plain, (r1_tarski(k3_subset_1(X1,X1),X2)|~r1_tarski(X1,X3)|~r1_tarski(X2,X3)), inference(spm,[status(thm)],[c_0_80, c_0_69])).
% 0.38/0.62  cnf(c_0_149, negated_conjecture, (k3_subset_1(esk3_0,esk3_0)=k1_xboole_0|k2_struct_0(esk2_0)!=u1_struct_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_146, c_0_147]), c_0_92])])).
% 0.38/0.62  cnf(c_0_150, negated_conjecture, (r1_tarski(k3_subset_1(esk3_0,esk3_0),X1)|~r1_tarski(X1,u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_148, c_0_91])).
% 0.38/0.62  cnf(c_0_151, negated_conjecture, (k3_subset_1(esk3_0,esk3_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_149, c_0_145]), c_0_92])])).
% 0.38/0.62  cnf(c_0_152, negated_conjecture, (r1_tarski(k3_subset_1(u1_struct_0(esk2_0),esk3_0),u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_111]), c_0_84]), c_0_40])])).
% 0.38/0.62  cnf(c_0_153, negated_conjecture, (r1_tarski(k1_xboole_0,X1)|~r1_tarski(X1,u1_struct_0(esk2_0))), inference(rw,[status(thm)],[c_0_150, c_0_151])).
% 0.38/0.62  cnf(c_0_154, negated_conjecture, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~r1_tarski(X1,esk3_0)), inference(spm,[status(thm)],[c_0_74, c_0_151])).
% 0.38/0.62  cnf(c_0_155, negated_conjecture, (r1_tarski(k3_subset_1(k3_subset_1(u1_struct_0(esk2_0),esk3_0),k3_subset_1(u1_struct_0(esk2_0),esk3_0)),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113, c_0_152]), c_0_92])])).
% 0.38/0.62  cnf(c_0_156, negated_conjecture, (r1_tarski(k1_xboole_0,k3_subset_1(u1_struct_0(esk2_0),esk3_0))), inference(spm,[status(thm)],[c_0_153, c_0_152])).
% 0.38/0.62  cnf(c_0_157, plain, (k3_subset_1(X1,X1)=X2|~m1_subset_1(X2,k1_zfmisc_1(k3_subset_1(X1,X1)))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_108, c_0_44])).
% 0.38/0.62  cnf(c_0_158, negated_conjecture, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(k3_subset_1(k3_subset_1(u1_struct_0(esk2_0),esk3_0),k3_subset_1(u1_struct_0(esk2_0),esk3_0))))), inference(spm,[status(thm)],[c_0_154, c_0_155])).
% 0.38/0.62  cnf(c_0_159, negated_conjecture, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(k3_subset_1(u1_struct_0(esk2_0),esk3_0)))), inference(spm,[status(thm)],[c_0_29, c_0_156])).
% 0.38/0.62  cnf(c_0_160, negated_conjecture, (k3_subset_1(k3_subset_1(u1_struct_0(esk2_0),esk3_0),k3_subset_1(u1_struct_0(esk2_0),esk3_0))=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_157, c_0_158]), c_0_159])])).
% 0.38/0.62  cnf(c_0_161, plain, (v1_tops_1(k3_subset_1(u1_struct_0(X2),X1),X2)|~v2_tops_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_120])).
% 0.38/0.62  cnf(c_0_162, plain, (r1_tarski(X1,k3_subset_1(X2,k3_subset_1(k3_subset_1(X2,X1),X3)))|~m1_subset_1(k3_subset_1(k3_subset_1(X2,X1),X3),k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(k3_subset_1(X2,X1)))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_58, c_0_39])).
% 0.38/0.62  cnf(c_0_163, negated_conjecture, (k3_subset_1(k3_subset_1(u1_struct_0(esk2_0),esk3_0),k1_xboole_0)=k3_subset_1(u1_struct_0(esk2_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_160]), c_0_40])])).
% 0.38/0.62  cnf(c_0_164, negated_conjecture, (m1_subset_1(k3_subset_1(u1_struct_0(esk2_0),esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(spm,[status(thm)],[c_0_29, c_0_152])).
% 0.38/0.62  cnf(c_0_165, plain, (v1_tops_1(X1,X2)|~v2_tops_1(k3_subset_1(u1_struct_0(X2),X1),X2)|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_161, c_0_42]), c_0_43])).
% 0.38/0.62  fof(c_0_166, plain, ![X32, X33]:(~l1_pre_topc(X32)|(~m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))|k1_tops_1(X32,X33)=k3_subset_1(u1_struct_0(X32),k2_pre_topc(X32,k3_subset_1(u1_struct_0(X32),X33))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tops_1])])])).
% 0.38/0.62  cnf(c_0_167, negated_conjecture, (r1_tarski(esk3_0,k3_subset_1(u1_struct_0(esk2_0),k3_subset_1(u1_struct_0(esk2_0),esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_162, c_0_163]), c_0_164]), c_0_159]), c_0_84])])).
% 0.38/0.62  cnf(c_0_168, negated_conjecture, (v1_tops_1(u1_struct_0(esk2_0),esk2_0)|~v2_tops_1(k3_subset_1(esk3_0,esk3_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_165, c_0_130]), c_0_92]), c_0_40])])).
% 0.38/0.62  cnf(c_0_169, negated_conjecture, (v2_tops_1(k1_xboole_0,esk2_0)|~v1_tops_1(u1_struct_0(esk2_0),esk2_0)), inference(rw,[status(thm)],[c_0_135, c_0_151])).
% 0.38/0.62  cnf(c_0_170, plain, (k1_tops_1(X1,X2)=k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_166])).
% 0.38/0.62  cnf(c_0_171, negated_conjecture, (k3_subset_1(u1_struct_0(esk2_0),k3_subset_1(u1_struct_0(esk2_0),esk3_0))=esk3_0|~r1_tarski(k3_subset_1(u1_struct_0(esk2_0),k3_subset_1(u1_struct_0(esk2_0),esk3_0)),esk3_0)), inference(spm,[status(thm)],[c_0_57, c_0_167])).
% 0.38/0.62  cnf(c_0_172, plain, (r1_tarski(k3_subset_1(X1,X2),X3)|~m1_subset_1(k3_subset_1(X1,X3),k1_zfmisc_1(X2))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~m1_subset_1(X3,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_38, c_0_50])).
% 0.38/0.62  cnf(c_0_173, plain, (k2_pre_topc(X2,X1)=k2_struct_0(X2)|~v1_tops_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_138])).
% 0.38/0.62  cnf(c_0_174, negated_conjecture, (v1_tops_1(u1_struct_0(esk2_0),esk2_0)|~v2_tops_1(k1_xboole_0,esk2_0)), inference(rw,[status(thm)],[c_0_168, c_0_151])).
% 0.38/0.62  cnf(c_0_175, negated_conjecture, (v2_tops_1(k1_xboole_0,esk2_0)|k2_pre_topc(esk2_0,u1_struct_0(esk2_0))!=k2_struct_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_169, c_0_143]), c_0_92]), c_0_40])])).
% 0.38/0.62  cnf(c_0_176, plain, (k1_tops_1(X1,k3_subset_1(u1_struct_0(X1),X2))=k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_170, c_0_42]), c_0_43])).
% 0.38/0.62  cnf(c_0_177, negated_conjecture, (k3_subset_1(u1_struct_0(esk2_0),k3_subset_1(u1_struct_0(esk2_0),esk3_0))=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_171, c_0_172]), c_0_40]), c_0_164]), c_0_84])])).
% 0.38/0.62  fof(c_0_178, plain, ![X26, X27]:(~l1_pre_topc(X26)|~m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))|m1_subset_1(k2_pre_topc(X26,X27),k1_zfmisc_1(u1_struct_0(X26)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).
% 0.38/0.62  cnf(c_0_179, negated_conjecture, (~v1_tops_1(k3_subset_1(u1_struct_0(esk2_0),esk3_0),esk2_0)), inference(split_conjunct,[status(thm)],[c_0_78])).
% 0.38/0.62  cnf(c_0_180, negated_conjecture, (k2_pre_topc(esk2_0,u1_struct_0(esk2_0))=k2_struct_0(esk2_0)|~v2_tops_1(k1_xboole_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_173, c_0_174]), c_0_92]), c_0_40])])).
% 0.38/0.62  cnf(c_0_181, negated_conjecture, (v2_tops_1(k1_xboole_0,esk2_0)|k2_struct_0(esk2_0)!=u1_struct_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_175, c_0_147]), c_0_92])])).
% 0.38/0.62  cnf(c_0_182, negated_conjecture, (k3_subset_1(u1_struct_0(esk2_0),k2_pre_topc(esk2_0,k3_subset_1(u1_struct_0(esk2_0),esk3_0)))=k1_tops_1(esk2_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_176, c_0_177]), c_0_92]), c_0_164])])).
% 0.38/0.62  cnf(c_0_183, plain, (m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_178])).
% 0.38/0.62  cnf(c_0_184, negated_conjecture, (k2_pre_topc(esk2_0,k3_subset_1(u1_struct_0(esk2_0),esk3_0))!=k2_struct_0(esk2_0)|~m1_subset_1(k3_subset_1(u1_struct_0(esk2_0),esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_179, c_0_143]), c_0_92])])).
% 0.38/0.62  cnf(c_0_185, negated_conjecture, (k2_struct_0(esk2_0)=u1_struct_0(esk2_0)|~v2_tops_1(k1_xboole_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_147, c_0_180]), c_0_92])])).
% 0.38/0.62  cnf(c_0_186, negated_conjecture, (v2_tops_1(k1_xboole_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_181, c_0_145]), c_0_92])])).
% 0.38/0.62  fof(c_0_187, plain, ![X29, X30, X31]:(~l1_pre_topc(X29)|(~m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))|(~m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X29)))|(~r1_tarski(X30,X31)|r1_tarski(k2_pre_topc(X29,X30),k2_pre_topc(X29,X31)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t49_pre_topc])])])).
% 0.38/0.62  cnf(c_0_188, negated_conjecture, (k3_subset_1(u1_struct_0(esk2_0),k1_tops_1(esk2_0,esk3_0))=k2_pre_topc(esk2_0,k3_subset_1(u1_struct_0(esk2_0),esk3_0))|~m1_subset_1(k2_pre_topc(esk2_0,k3_subset_1(u1_struct_0(esk2_0),esk3_0)),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(spm,[status(thm)],[c_0_42, c_0_182])).
% 0.38/0.62  cnf(c_0_189, plain, (m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(X3))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(u1_struct_0(X1),X3)), inference(spm,[status(thm)],[c_0_45, c_0_183])).
% 0.38/0.62  cnf(c_0_190, negated_conjecture, (m1_subset_1(k1_tops_1(esk2_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))|~m1_subset_1(k2_pre_topc(esk2_0,k3_subset_1(u1_struct_0(esk2_0),esk3_0)),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(spm,[status(thm)],[c_0_43, c_0_182])).
% 0.38/0.62  cnf(c_0_191, negated_conjecture, (k2_pre_topc(esk2_0,k3_subset_1(u1_struct_0(esk2_0),esk3_0))!=k2_struct_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_184, c_0_164])])).
% 0.38/0.62  cnf(c_0_192, negated_conjecture, (k2_struct_0(esk2_0)=u1_struct_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_185, c_0_186])])).
% 0.38/0.62  cnf(c_0_193, plain, (r1_tarski(k2_pre_topc(X1,X2),k2_pre_topc(X1,X3))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_187])).
% 0.38/0.62  cnf(c_0_194, plain, (k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2))=k2_struct_0(X1)|~v2_tops_1(X2,X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_173, c_0_161]), c_0_43])).
% 0.38/0.62  cnf(c_0_195, negated_conjecture, (k1_tops_1(esk2_0,k3_subset_1(u1_struct_0(esk2_0),esk3_0))=k3_subset_1(u1_struct_0(esk2_0),k2_pre_topc(esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_170, c_0_177]), c_0_92]), c_0_164])])).
% 0.38/0.62  cnf(c_0_196, negated_conjecture, (k3_subset_1(u1_struct_0(esk2_0),k1_tops_1(esk2_0,esk3_0))=k2_pre_topc(esk2_0,k3_subset_1(u1_struct_0(esk2_0),esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_188, c_0_189]), c_0_92]), c_0_164]), c_0_34])])).
% 0.38/0.62  cnf(c_0_197, negated_conjecture, (m1_subset_1(k1_tops_1(esk2_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_190, c_0_183]), c_0_92]), c_0_164])])).
% 0.38/0.62  cnf(c_0_198, negated_conjecture, (k2_pre_topc(esk2_0,k3_subset_1(u1_struct_0(esk2_0),esk3_0))!=u1_struct_0(esk2_0)), inference(rw,[status(thm)],[c_0_191, c_0_192])).
% 0.38/0.62  cnf(c_0_199, plain, (r1_tarski(k2_struct_0(X1),k2_pre_topc(X1,X2))|~v2_tops_1(X3,X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(k3_subset_1(u1_struct_0(X1),X3),X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_193, c_0_194]), c_0_43])).
% 0.38/0.62  cnf(c_0_200, negated_conjecture, (r1_tarski(k3_subset_1(u1_struct_0(esk2_0),k2_pre_topc(esk2_0,esk3_0)),k3_subset_1(u1_struct_0(esk2_0),esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_124, c_0_195]), c_0_92]), c_0_164])])).
% 0.38/0.62  cnf(c_0_201, negated_conjecture, (~r1_tarski(u1_struct_0(esk2_0),k2_pre_topc(esk2_0,k3_subset_1(u1_struct_0(esk2_0),esk3_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_196]), c_0_197])]), c_0_198])).
% 0.38/0.62  fof(c_0_202, plain, ![X38, X39]:((~v3_tops_1(X39,X38)|v2_tops_1(k2_pre_topc(X38,X39),X38)|~m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(X38)))|~l1_pre_topc(X38))&(~v2_tops_1(k2_pre_topc(X38,X39),X38)|v3_tops_1(X39,X38)|~m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(X38)))|~l1_pre_topc(X38))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_tops_1])])])])).
% 0.38/0.62  cnf(c_0_203, negated_conjecture, (~v2_tops_1(k2_pre_topc(esk2_0,esk3_0),esk2_0)|~m1_subset_1(k2_pre_topc(esk2_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_199, c_0_200]), c_0_192]), c_0_92]), c_0_164])]), c_0_201])).
% 0.38/0.62  cnf(c_0_204, plain, (v2_tops_1(k2_pre_topc(X2,X1),X2)|~v3_tops_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_202])).
% 0.38/0.62  cnf(c_0_205, negated_conjecture, (v3_tops_1(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_78])).
% 0.38/0.62  cnf(c_0_206, negated_conjecture, (~m1_subset_1(k2_pre_topc(esk2_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_203, c_0_204]), c_0_205]), c_0_92]), c_0_84])])).
% 0.38/0.62  cnf(c_0_207, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_206, c_0_189]), c_0_92]), c_0_84]), c_0_34])]), ['proof']).
% 0.38/0.62  # SZS output end CNFRefutation
% 0.38/0.62  # Proof object total steps             : 208
% 0.38/0.62  # Proof object clause steps            : 161
% 0.38/0.62  # Proof object formula steps           : 47
% 0.38/0.62  # Proof object conjectures             : 72
% 0.38/0.62  # Proof object clause conjectures      : 69
% 0.38/0.62  # Proof object formula conjectures     : 3
% 0.38/0.62  # Proof object initial clauses used    : 31
% 0.38/0.62  # Proof object initial formulas used   : 23
% 0.38/0.62  # Proof object generating inferences   : 123
% 0.38/0.62  # Proof object simplifying inferences  : 117
% 0.38/0.62  # Training examples: 0 positive, 0 negative
% 0.38/0.62  # Parsed axioms                        : 23
% 0.38/0.62  # Removed by relevancy pruning/SinE    : 0
% 0.38/0.62  # Initial clauses                      : 34
% 0.38/0.62  # Removed in clause preprocessing      : 0
% 0.38/0.62  # Initial clauses in saturation        : 34
% 0.38/0.62  # Processed clauses                    : 3057
% 0.38/0.62  # ...of these trivial                  : 129
% 0.38/0.62  # ...subsumed                          : 1995
% 0.38/0.62  # ...remaining for further processing  : 933
% 0.38/0.62  # Other redundant clauses eliminated   : 2
% 0.38/0.62  # Clauses deleted for lack of memory   : 0
% 0.38/0.62  # Backward-subsumed                    : 59
% 0.38/0.62  # Backward-rewritten                   : 158
% 0.38/0.62  # Generated clauses                    : 20416
% 0.38/0.62  # ...of the previous two non-trivial   : 17424
% 0.38/0.62  # Contextual simplify-reflections      : 38
% 0.38/0.62  # Paramodulations                      : 20414
% 0.38/0.62  # Factorizations                       : 0
% 0.38/0.62  # Equation resolutions                 : 2
% 0.38/0.62  # Propositional unsat checks           : 0
% 0.38/0.62  #    Propositional check models        : 0
% 0.38/0.62  #    Propositional check unsatisfiable : 0
% 0.38/0.62  #    Propositional clauses             : 0
% 0.38/0.62  #    Propositional clauses after purity: 0
% 0.38/0.62  #    Propositional unsat core size     : 0
% 0.38/0.62  #    Propositional preprocessing time  : 0.000
% 0.38/0.62  #    Propositional encoding time       : 0.000
% 0.38/0.62  #    Propositional solver time         : 0.000
% 0.38/0.62  #    Success case prop preproc time    : 0.000
% 0.38/0.62  #    Success case prop encoding time   : 0.000
% 0.38/0.62  #    Success case prop solver time     : 0.000
% 0.38/0.62  # Current number of processed clauses  : 681
% 0.38/0.62  #    Positive orientable unit clauses  : 84
% 0.38/0.62  #    Positive unorientable unit clauses: 0
% 0.38/0.62  #    Negative unit clauses             : 14
% 0.38/0.62  #    Non-unit-clauses                  : 583
% 0.38/0.62  # Current number of unprocessed clauses: 13894
% 0.38/0.62  # ...number of literals in the above   : 46501
% 0.38/0.62  # Current number of archived formulas  : 0
% 0.38/0.62  # Current number of archived clauses   : 250
% 0.38/0.62  # Clause-clause subsumption calls (NU) : 56749
% 0.38/0.62  # Rec. Clause-clause subsumption calls : 44385
% 0.38/0.62  # Non-unit clause-clause subsumptions  : 1600
% 0.38/0.62  # Unit Clause-clause subsumption calls : 2839
% 0.38/0.62  # Rewrite failures with RHS unbound    : 0
% 0.38/0.62  # BW rewrite match attempts            : 86
% 0.38/0.62  # BW rewrite match successes           : 28
% 0.38/0.62  # Condensation attempts                : 0
% 0.38/0.62  # Condensation successes               : 0
% 0.38/0.62  # Termbank termtop insertions          : 304256
% 0.46/0.63  
% 0.46/0.63  # -------------------------------------------------
% 0.46/0.63  # User time                : 0.269 s
% 0.46/0.63  # System time              : 0.017 s
% 0.46/0.63  # Total time               : 0.286 s
% 0.46/0.63  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
