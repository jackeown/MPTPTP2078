%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1389+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:13 EST 2020

% Result     : Theorem 0.17s
% Output     : CNFRefutation 0.17s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 184 expanded)
%              Number of clauses        :   38 (  68 expanded)
%              Number of leaves         :   11 (  45 expanded)
%              Depth                    :   10
%              Number of atoms          :  325 (1240 expanded)
%              Number of equality atoms :   37 ( 148 expanded)
%              Maximal formula depth    :   22 (   6 average)
%              Maximal clause size      :   64 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t92_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => r1_tarski(X1,k3_tarski(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_zfmisc_1)).

fof(redefinition_k5_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => k5_setfam_1(X1,X2) = k3_tarski(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).

fof(d7_connsp_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( X3 = k1_connsp_1(X1,X2)
              <=> ? [X4] :
                    ( m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
                    & ! [X5] :
                        ( m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))
                       => ( r2_hidden(X5,X4)
                        <=> ( v2_connsp_1(X5,X1)
                            & r2_hidden(X2,X5) ) ) )
                    & k5_setfam_1(u1_struct_0(X1),X4) = X3 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_connsp_1)).

fof(t14_connsp_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X2))
                 => ( X3 = X4
                   => r1_tarski(k1_connsp_1(X2,X4),k1_connsp_1(X1,X3)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_connsp_2)).

fof(t24_connsp_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ! [X4] :
                  ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
                 => ( X3 = X4
                   => ( v2_connsp_1(X3,X1)
                    <=> v2_connsp_1(X4,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_connsp_1)).

fof(t39_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
             => m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_pre_topc)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(cc1_pre_topc,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => v2_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(dt_k1_connsp_1,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => m1_subset_1(k1_connsp_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_connsp_1)).

fof(fc2_connsp_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => ( ~ v1_xboole_0(k1_connsp_1(X1,X2))
        & v2_connsp_1(k1_connsp_1(X1,X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_connsp_1)).

fof(t40_connsp_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => r2_hidden(X2,k1_connsp_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_connsp_1)).

fof(c_0_11,plain,(
    ! [X32,X33] :
      ( ~ r2_hidden(X32,X33)
      | r1_tarski(X32,k3_tarski(X33)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t92_zfmisc_1])])).

fof(c_0_12,plain,(
    ! [X21,X22] :
      ( ~ m1_subset_1(X22,k1_zfmisc_1(k1_zfmisc_1(X21)))
      | k5_setfam_1(X21,X22) = k3_tarski(X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k5_setfam_1])])).

cnf(c_0_13,plain,
    ( r1_tarski(X1,k3_tarski(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_14,plain,
    ( k5_setfam_1(X2,X1) = k3_tarski(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_15,plain,(
    ! [X8,X9,X10,X12,X13] :
      ( ( m1_subset_1(esk1_3(X8,X9,X10),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X8))))
        | X10 != k1_connsp_1(X8,X9)
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X8)))
        | ~ m1_subset_1(X9,u1_struct_0(X8))
        | ~ l1_pre_topc(X8) )
      & ( v2_connsp_1(X12,X8)
        | ~ r2_hidden(X12,esk1_3(X8,X9,X10))
        | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X8)))
        | X10 != k1_connsp_1(X8,X9)
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X8)))
        | ~ m1_subset_1(X9,u1_struct_0(X8))
        | ~ l1_pre_topc(X8) )
      & ( r2_hidden(X9,X12)
        | ~ r2_hidden(X12,esk1_3(X8,X9,X10))
        | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X8)))
        | X10 != k1_connsp_1(X8,X9)
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X8)))
        | ~ m1_subset_1(X9,u1_struct_0(X8))
        | ~ l1_pre_topc(X8) )
      & ( ~ v2_connsp_1(X12,X8)
        | ~ r2_hidden(X9,X12)
        | r2_hidden(X12,esk1_3(X8,X9,X10))
        | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X8)))
        | X10 != k1_connsp_1(X8,X9)
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X8)))
        | ~ m1_subset_1(X9,u1_struct_0(X8))
        | ~ l1_pre_topc(X8) )
      & ( k5_setfam_1(u1_struct_0(X8),esk1_3(X8,X9,X10)) = X10
        | X10 != k1_connsp_1(X8,X9)
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X8)))
        | ~ m1_subset_1(X9,u1_struct_0(X8))
        | ~ l1_pre_topc(X8) )
      & ( m1_subset_1(esk2_4(X8,X9,X10,X13),k1_zfmisc_1(u1_struct_0(X8)))
        | ~ m1_subset_1(X13,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X8))))
        | k5_setfam_1(u1_struct_0(X8),X13) != X10
        | X10 = k1_connsp_1(X8,X9)
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X8)))
        | ~ m1_subset_1(X9,u1_struct_0(X8))
        | ~ l1_pre_topc(X8) )
      & ( ~ r2_hidden(esk2_4(X8,X9,X10,X13),X13)
        | ~ v2_connsp_1(esk2_4(X8,X9,X10,X13),X8)
        | ~ r2_hidden(X9,esk2_4(X8,X9,X10,X13))
        | ~ m1_subset_1(X13,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X8))))
        | k5_setfam_1(u1_struct_0(X8),X13) != X10
        | X10 = k1_connsp_1(X8,X9)
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X8)))
        | ~ m1_subset_1(X9,u1_struct_0(X8))
        | ~ l1_pre_topc(X8) )
      & ( v2_connsp_1(esk2_4(X8,X9,X10,X13),X8)
        | r2_hidden(esk2_4(X8,X9,X10,X13),X13)
        | ~ m1_subset_1(X13,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X8))))
        | k5_setfam_1(u1_struct_0(X8),X13) != X10
        | X10 = k1_connsp_1(X8,X9)
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X8)))
        | ~ m1_subset_1(X9,u1_struct_0(X8))
        | ~ l1_pre_topc(X8) )
      & ( r2_hidden(X9,esk2_4(X8,X9,X10,X13))
        | r2_hidden(esk2_4(X8,X9,X10,X13),X13)
        | ~ m1_subset_1(X13,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X8))))
        | k5_setfam_1(u1_struct_0(X8),X13) != X10
        | X10 = k1_connsp_1(X8,X9)
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X8)))
        | ~ m1_subset_1(X9,u1_struct_0(X8))
        | ~ l1_pre_topc(X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_connsp_1])])])])])).

fof(c_0_16,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & m1_pre_topc(X2,X1) )
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X2))
                   => ( X3 = X4
                     => r1_tarski(k1_connsp_1(X2,X4),k1_connsp_1(X1,X3)) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t14_connsp_2])).

cnf(c_0_17,plain,
    ( r1_tarski(X1,k5_setfam_1(X2,X3))
    | ~ r2_hidden(X1,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_18,plain,
    ( k5_setfam_1(u1_struct_0(X1),esk1_3(X1,X2,X3)) = X3
    | X3 != k1_connsp_1(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | X3 != k1_connsp_1(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_20,plain,(
    ! [X23,X24,X25,X26] :
      ( ( ~ v2_connsp_1(X25,X23)
        | v2_connsp_1(X26,X24)
        | X25 != X26
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X24)))
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X23)))
        | ~ m1_pre_topc(X24,X23)
        | ~ v2_pre_topc(X23)
        | ~ l1_pre_topc(X23) )
      & ( ~ v2_connsp_1(X26,X24)
        | v2_connsp_1(X25,X23)
        | X25 != X26
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X24)))
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X23)))
        | ~ m1_pre_topc(X24,X23)
        | ~ v2_pre_topc(X23)
        | ~ l1_pre_topc(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t24_connsp_1])])])])).

fof(c_0_21,plain,(
    ! [X27,X28,X29] :
      ( ~ l1_pre_topc(X27)
      | ~ m1_pre_topc(X28,X27)
      | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))
      | m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X27))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t39_pre_topc])])])).

fof(c_0_22,negated_conjecture,
    ( ~ v2_struct_0(esk3_0)
    & v2_pre_topc(esk3_0)
    & l1_pre_topc(esk3_0)
    & ~ v2_struct_0(esk4_0)
    & m1_pre_topc(esk4_0,esk3_0)
    & m1_subset_1(esk5_0,u1_struct_0(esk3_0))
    & m1_subset_1(esk6_0,u1_struct_0(esk4_0))
    & esk5_0 = esk6_0
    & ~ r1_tarski(k1_connsp_1(esk4_0,esk6_0),k1_connsp_1(esk3_0,esk5_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_16])])])])).

fof(c_0_23,plain,(
    ! [X17,X18] :
      ( ~ l1_pre_topc(X17)
      | ~ m1_pre_topc(X18,X17)
      | l1_pre_topc(X18) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

fof(c_0_24,plain,(
    ! [X6,X7] :
      ( ~ v2_pre_topc(X6)
      | ~ l1_pre_topc(X6)
      | ~ m1_pre_topc(X7,X6)
      | v2_pre_topc(X7) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_pre_topc])])])).

cnf(c_0_25,plain,
    ( r1_tarski(X1,X2)
    | X2 != k1_connsp_1(X3,X4)
    | ~ r2_hidden(X1,esk1_3(X3,X4,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ l1_pre_topc(X3) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19])).

cnf(c_0_26,plain,
    ( r2_hidden(X1,esk1_3(X2,X3,X4))
    | ~ v2_connsp_1(X1,X2)
    | ~ r2_hidden(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | X4 != k1_connsp_1(X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_27,plain,(
    ! [X15,X16] :
      ( ~ l1_pre_topc(X15)
      | ~ m1_subset_1(X16,u1_struct_0(X15))
      | m1_subset_1(k1_connsp_1(X15,X16),k1_zfmisc_1(u1_struct_0(X15))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_connsp_1])])).

cnf(c_0_28,plain,
    ( v2_connsp_1(X3,X4)
    | ~ v2_connsp_1(X1,X2)
    | X3 != X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))
    | ~ m1_pre_topc(X2,X4)
    | ~ v2_pre_topc(X4)
    | ~ l1_pre_topc(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,plain,
    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_30,plain,(
    ! [X19,X20] :
      ( ( ~ v1_xboole_0(k1_connsp_1(X19,X20))
        | v2_struct_0(X19)
        | ~ v2_pre_topc(X19)
        | ~ l1_pre_topc(X19)
        | ~ m1_subset_1(X20,u1_struct_0(X19)) )
      & ( v2_connsp_1(k1_connsp_1(X19,X20),X19)
        | v2_struct_0(X19)
        | ~ v2_pre_topc(X19)
        | ~ l1_pre_topc(X19)
        | ~ m1_subset_1(X20,u1_struct_0(X19)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_connsp_1])])])])).

cnf(c_0_31,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_32,negated_conjecture,
    ( esk5_0 = esk6_0 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_33,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_34,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_35,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_36,plain,
    ( v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_37,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_38,plain,
    ( r1_tarski(X1,X2)
    | X2 != k1_connsp_1(X3,X4)
    | ~ v2_connsp_1(X1,X3)
    | ~ r2_hidden(X4,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ l1_pre_topc(X3) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_39,plain,
    ( m1_subset_1(k1_connsp_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_40,plain,
    ( v2_connsp_1(X1,X2)
    | ~ v2_connsp_1(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_pre_topc(X3,X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_28]),c_0_29])).

cnf(c_0_41,plain,
    ( v2_connsp_1(k1_connsp_1(X1,X2),X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_42,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(esk4_0)) ),
    inference(rw,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_43,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35])])).

cnf(c_0_44,negated_conjecture,
    ( v2_pre_topc(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_34]),c_0_35]),c_0_37])])).

cnf(c_0_45,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_46,plain,
    ( r1_tarski(X1,k1_connsp_1(X2,X3))
    | k1_connsp_1(X2,X3) != k1_connsp_1(X2,X4)
    | ~ v2_connsp_1(X1,X2)
    | ~ r2_hidden(X4,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_47,plain,
    ( m1_subset_1(k1_connsp_1(X1,X2),k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_pre_topc(X1,X3)
    | ~ l1_pre_topc(X3) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_39]),c_0_33])).

cnf(c_0_48,plain,
    ( v2_connsp_1(k1_connsp_1(X1,X2),X3)
    | ~ v2_connsp_1(k1_connsp_1(X1,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_pre_topc(X1,X3)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X3) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_39]),c_0_33])).

cnf(c_0_49,negated_conjecture,
    ( v2_connsp_1(k1_connsp_1(esk4_0,esk5_0),esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_43]),c_0_44])]),c_0_45])).

fof(c_0_50,plain,(
    ! [X30,X31] :
      ( v2_struct_0(X30)
      | ~ v2_pre_topc(X30)
      | ~ l1_pre_topc(X30)
      | ~ m1_subset_1(X31,u1_struct_0(X30))
      | r2_hidden(X31,k1_connsp_1(X30,X31)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t40_connsp_1])])])])).

cnf(c_0_51,plain,
    ( r1_tarski(k1_connsp_1(X1,X2),k1_connsp_1(X3,X4))
    | k1_connsp_1(X3,X4) != k1_connsp_1(X3,X5)
    | ~ v2_connsp_1(k1_connsp_1(X1,X2),X3)
    | ~ r2_hidden(X5,k1_connsp_1(X1,X2))
    | ~ m1_subset_1(X5,u1_struct_0(X3))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_pre_topc(X1,X3)
    | ~ l1_pre_topc(X3) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_52,negated_conjecture,
    ( v2_connsp_1(k1_connsp_1(esk4_0,esk5_0),X1)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_42])])).

cnf(c_0_53,plain,
    ( v2_struct_0(X1)
    | r2_hidden(X2,k1_connsp_1(X1,X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_54,negated_conjecture,
    ( ~ r1_tarski(k1_connsp_1(esk4_0,esk6_0),k1_connsp_1(esk3_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_55,negated_conjecture,
    ( r1_tarski(k1_connsp_1(esk4_0,esk5_0),k1_connsp_1(X1,X2))
    | k1_connsp_1(X1,X2) != k1_connsp_1(X1,X3)
    | ~ r2_hidden(X3,k1_connsp_1(esk4_0,esk5_0))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_42])])).

cnf(c_0_56,negated_conjecture,
    ( r2_hidden(esk5_0,k1_connsp_1(esk4_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_42]),c_0_43]),c_0_44])]),c_0_45])).

cnf(c_0_57,negated_conjecture,
    ( ~ r1_tarski(k1_connsp_1(esk4_0,esk5_0),k1_connsp_1(esk3_0,esk5_0)) ),
    inference(rw,[status(thm)],[c_0_54,c_0_32])).

cnf(c_0_58,negated_conjecture,
    ( r1_tarski(k1_connsp_1(esk4_0,esk5_0),k1_connsp_1(X1,X2))
    | k1_connsp_1(X1,X2) != k1_connsp_1(X1,esk5_0)
    | ~ m1_subset_1(esk5_0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_59,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_60,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_59]),c_0_34]),c_0_35]),c_0_37])]),
    [proof]).

%------------------------------------------------------------------------------
