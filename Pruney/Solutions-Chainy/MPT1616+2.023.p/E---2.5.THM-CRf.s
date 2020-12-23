%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:15:59 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 350 expanded)
%              Number of clauses        :   48 ( 167 expanded)
%              Number of leaves         :   11 (  84 expanded)
%              Depth                    :   14
%              Number of atoms          :  272 (1554 expanded)
%              Number of equality atoms :   21 ( 140 expanded)
%              Maximal formula depth    :   27 (   4 average)
%              Maximal clause size      :   90 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(dt_u1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(t24_yellow_1,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => k4_yellow_0(k2_yellow_1(u1_pre_topc(X1))) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_yellow_1)).

fof(t94_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X1)
         => r1_tarski(X3,X2) )
     => r1_tarski(k3_tarski(X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_zfmisc_1)).

fof(d1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ( v2_pre_topc(X1)
      <=> ( r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))
          & ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
             => ( r1_tarski(X2,u1_pre_topc(X1))
               => r2_hidden(k5_setfam_1(u1_struct_0(X1),X2),u1_pre_topc(X1)) ) )
          & ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( r2_hidden(X2,u1_pre_topc(X1))
                      & r2_hidden(X3,u1_pre_topc(X1)) )
                   => r2_hidden(k9_subset_1(u1_struct_0(X1),X2,X3),u1_pre_topc(X1)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_pre_topc)).

fof(l49_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => r1_tarski(X1,k3_tarski(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

fof(t95_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => r1_tarski(k3_tarski(X1),k3_tarski(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_zfmisc_1)).

fof(t14_yellow_1,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ( r2_hidden(k3_tarski(X1),X1)
       => k4_yellow_0(k2_yellow_1(X1)) = k3_tarski(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_yellow_1)).

fof(c_0_11,plain,(
    ! [X4,X5] :
      ( ( r1_tarski(X4,X5)
        | X4 != X5 )
      & ( r1_tarski(X5,X4)
        | X4 != X5 )
      & ( ~ r1_tarski(X4,X5)
        | ~ r1_tarski(X5,X4)
        | X4 = X5 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_12,plain,(
    ! [X15,X16] :
      ( ( ~ m1_subset_1(X15,k1_zfmisc_1(X16))
        | r1_tarski(X15,X16) )
      & ( ~ r1_tarski(X15,X16)
        | m1_subset_1(X15,k1_zfmisc_1(X16)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_13,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_14,plain,(
    ! [X17,X18,X19] :
      ( ~ r2_hidden(X17,X18)
      | ~ m1_subset_1(X18,k1_zfmisc_1(X19))
      | ~ v1_xboole_0(X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

cnf(c_0_15,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_13])).

fof(c_0_17,plain,(
    ! [X27] :
      ( ~ l1_pre_topc(X27)
      | m1_subset_1(u1_pre_topc(X27),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X27)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).

fof(c_0_18,plain,(
    ! [X13,X14] :
      ( ( ~ m1_subset_1(X14,X13)
        | r2_hidden(X14,X13)
        | v1_xboole_0(X13) )
      & ( ~ r2_hidden(X14,X13)
        | m1_subset_1(X14,X13)
        | v1_xboole_0(X13) )
      & ( ~ m1_subset_1(X14,X13)
        | v1_xboole_0(X14)
        | ~ v1_xboole_0(X13) )
      & ( ~ v1_xboole_0(X14)
        | m1_subset_1(X14,X13)
        | ~ v1_xboole_0(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

fof(c_0_19,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => k4_yellow_0(k2_yellow_1(u1_pre_topc(X1))) = u1_struct_0(X1) ) ),
    inference(assume_negation,[status(cth)],[t24_yellow_1])).

fof(c_0_20,plain,(
    ! [X8,X9] :
      ( ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(k3_tarski(X8),X9) )
      & ( ~ r1_tarski(esk1_2(X8,X9),X9)
        | r1_tarski(k3_tarski(X8),X9) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_zfmisc_1])])])])).

cnf(c_0_21,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_23,plain,
    ( m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_25,plain,(
    ! [X20,X21,X22,X23] :
      ( ( r2_hidden(u1_struct_0(X20),u1_pre_topc(X20))
        | ~ v2_pre_topc(X20)
        | ~ l1_pre_topc(X20) )
      & ( ~ m1_subset_1(X21,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X20))))
        | ~ r1_tarski(X21,u1_pre_topc(X20))
        | r2_hidden(k5_setfam_1(u1_struct_0(X20),X21),u1_pre_topc(X20))
        | ~ v2_pre_topc(X20)
        | ~ l1_pre_topc(X20) )
      & ( ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X20)))
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X20)))
        | ~ r2_hidden(X22,u1_pre_topc(X20))
        | ~ r2_hidden(X23,u1_pre_topc(X20))
        | r2_hidden(k9_subset_1(u1_struct_0(X20),X22,X23),u1_pre_topc(X20))
        | ~ v2_pre_topc(X20)
        | ~ l1_pre_topc(X20) )
      & ( m1_subset_1(esk3_1(X20),k1_zfmisc_1(u1_struct_0(X20)))
        | m1_subset_1(esk2_1(X20),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X20))))
        | ~ r2_hidden(u1_struct_0(X20),u1_pre_topc(X20))
        | v2_pre_topc(X20)
        | ~ l1_pre_topc(X20) )
      & ( m1_subset_1(esk4_1(X20),k1_zfmisc_1(u1_struct_0(X20)))
        | m1_subset_1(esk2_1(X20),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X20))))
        | ~ r2_hidden(u1_struct_0(X20),u1_pre_topc(X20))
        | v2_pre_topc(X20)
        | ~ l1_pre_topc(X20) )
      & ( r2_hidden(esk3_1(X20),u1_pre_topc(X20))
        | m1_subset_1(esk2_1(X20),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X20))))
        | ~ r2_hidden(u1_struct_0(X20),u1_pre_topc(X20))
        | v2_pre_topc(X20)
        | ~ l1_pre_topc(X20) )
      & ( r2_hidden(esk4_1(X20),u1_pre_topc(X20))
        | m1_subset_1(esk2_1(X20),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X20))))
        | ~ r2_hidden(u1_struct_0(X20),u1_pre_topc(X20))
        | v2_pre_topc(X20)
        | ~ l1_pre_topc(X20) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X20),esk3_1(X20),esk4_1(X20)),u1_pre_topc(X20))
        | m1_subset_1(esk2_1(X20),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X20))))
        | ~ r2_hidden(u1_struct_0(X20),u1_pre_topc(X20))
        | v2_pre_topc(X20)
        | ~ l1_pre_topc(X20) )
      & ( m1_subset_1(esk3_1(X20),k1_zfmisc_1(u1_struct_0(X20)))
        | r1_tarski(esk2_1(X20),u1_pre_topc(X20))
        | ~ r2_hidden(u1_struct_0(X20),u1_pre_topc(X20))
        | v2_pre_topc(X20)
        | ~ l1_pre_topc(X20) )
      & ( m1_subset_1(esk4_1(X20),k1_zfmisc_1(u1_struct_0(X20)))
        | r1_tarski(esk2_1(X20),u1_pre_topc(X20))
        | ~ r2_hidden(u1_struct_0(X20),u1_pre_topc(X20))
        | v2_pre_topc(X20)
        | ~ l1_pre_topc(X20) )
      & ( r2_hidden(esk3_1(X20),u1_pre_topc(X20))
        | r1_tarski(esk2_1(X20),u1_pre_topc(X20))
        | ~ r2_hidden(u1_struct_0(X20),u1_pre_topc(X20))
        | v2_pre_topc(X20)
        | ~ l1_pre_topc(X20) )
      & ( r2_hidden(esk4_1(X20),u1_pre_topc(X20))
        | r1_tarski(esk2_1(X20),u1_pre_topc(X20))
        | ~ r2_hidden(u1_struct_0(X20),u1_pre_topc(X20))
        | v2_pre_topc(X20)
        | ~ l1_pre_topc(X20) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X20),esk3_1(X20),esk4_1(X20)),u1_pre_topc(X20))
        | r1_tarski(esk2_1(X20),u1_pre_topc(X20))
        | ~ r2_hidden(u1_struct_0(X20),u1_pre_topc(X20))
        | v2_pre_topc(X20)
        | ~ l1_pre_topc(X20) )
      & ( m1_subset_1(esk3_1(X20),k1_zfmisc_1(u1_struct_0(X20)))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X20),esk2_1(X20)),u1_pre_topc(X20))
        | ~ r2_hidden(u1_struct_0(X20),u1_pre_topc(X20))
        | v2_pre_topc(X20)
        | ~ l1_pre_topc(X20) )
      & ( m1_subset_1(esk4_1(X20),k1_zfmisc_1(u1_struct_0(X20)))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X20),esk2_1(X20)),u1_pre_topc(X20))
        | ~ r2_hidden(u1_struct_0(X20),u1_pre_topc(X20))
        | v2_pre_topc(X20)
        | ~ l1_pre_topc(X20) )
      & ( r2_hidden(esk3_1(X20),u1_pre_topc(X20))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X20),esk2_1(X20)),u1_pre_topc(X20))
        | ~ r2_hidden(u1_struct_0(X20),u1_pre_topc(X20))
        | v2_pre_topc(X20)
        | ~ l1_pre_topc(X20) )
      & ( r2_hidden(esk4_1(X20),u1_pre_topc(X20))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X20),esk2_1(X20)),u1_pre_topc(X20))
        | ~ r2_hidden(u1_struct_0(X20),u1_pre_topc(X20))
        | v2_pre_topc(X20)
        | ~ l1_pre_topc(X20) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X20),esk3_1(X20),esk4_1(X20)),u1_pre_topc(X20))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X20),esk2_1(X20)),u1_pre_topc(X20))
        | ~ r2_hidden(u1_struct_0(X20),u1_pre_topc(X20))
        | v2_pre_topc(X20)
        | ~ l1_pre_topc(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_pre_topc])])])])])).

fof(c_0_26,negated_conjecture,
    ( ~ v2_struct_0(esk5_0)
    & v2_pre_topc(esk5_0)
    & l1_pre_topc(esk5_0)
    & k4_yellow_0(k2_yellow_1(u1_pre_topc(esk5_0))) != u1_struct_0(esk5_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_19])])])])).

cnf(c_0_27,plain,
    ( r1_tarski(k3_tarski(X1),X2)
    | ~ r1_tarski(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_29,plain,
    ( m1_subset_1(X1,X2)
    | v1_xboole_0(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_30,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_31,plain,
    ( ~ l1_pre_topc(X1)
    | ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,u1_pre_topc(X1)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_23])).

cnf(c_0_32,plain,
    ( v1_xboole_0(k1_zfmisc_1(X1))
    | r2_hidden(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_22])).

cnf(c_0_33,plain,
    ( r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_34,negated_conjecture,
    ( v2_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_35,negated_conjecture,
    ( l1_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_36,plain,(
    ! [X6,X7] :
      ( ~ r2_hidden(X6,X7)
      | r1_tarski(X6,k3_tarski(X7)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l49_zfmisc_1])])).

cnf(c_0_37,plain,
    ( r1_tarski(k3_tarski(X1),X2)
    | ~ m1_subset_1(esk1_2(X1,X2),k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_38,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(csr,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_39,plain,
    ( r2_hidden(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ r2_hidden(X2,u1_pre_topc(X1)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35])])).

cnf(c_0_41,plain,
    ( v1_xboole_0(X1)
    | ~ m1_subset_1(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_42,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_43,plain,
    ( r1_tarski(X1,k3_tarski(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_44,plain,
    ( r1_tarski(k3_tarski(X1),X2)
    | ~ r2_hidden(esk1_2(X1,X2),k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_45,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(k3_tarski(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(u1_struct_0(esk5_0),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_35])])).

cnf(c_0_47,plain,
    ( v1_xboole_0(X1)
    | ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_22])).

cnf(c_0_48,plain,
    ( k3_tarski(X1) = X2
    | ~ r2_hidden(X2,X1)
    | ~ r1_tarski(k3_tarski(X1),X2) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_49,plain,
    ( r1_tarski(k3_tarski(k1_zfmisc_1(X1)),X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_50,negated_conjecture,
    ( ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(spm,[status(thm)],[c_0_30,c_0_46])).

cnf(c_0_51,plain,
    ( v1_xboole_0(X1)
    | r2_hidden(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_32])).

fof(c_0_52,plain,(
    ! [X11,X12] :
      ( ~ r1_tarski(X11,X12)
      | r1_tarski(k3_tarski(X11),k3_tarski(X12)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t95_zfmisc_1])])).

cnf(c_0_53,plain,
    ( k3_tarski(k1_zfmisc_1(X1)) = X1
    | ~ r2_hidden(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(k1_zfmisc_1(u1_struct_0(esk5_0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk5_0)))) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_55,plain,
    ( r1_tarski(k3_tarski(X1),k3_tarski(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_56,plain,
    ( k3_tarski(k1_zfmisc_1(X1)) = X1
    | v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_53,c_0_51])).

cnf(c_0_57,plain,
    ( v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | r2_hidden(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_23])).

cnf(c_0_58,negated_conjecture,
    ( ~ v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk5_0)))) ),
    inference(spm,[status(thm)],[c_0_30,c_0_54])).

fof(c_0_59,plain,(
    ! [X28] :
      ( v1_xboole_0(X28)
      | ~ r2_hidden(k3_tarski(X28),X28)
      | k4_yellow_0(k2_yellow_1(X28)) = k3_tarski(X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t14_yellow_1])])])).

cnf(c_0_60,plain,
    ( k3_tarski(X1) = k3_tarski(X2)
    | ~ r2_hidden(k3_tarski(X2),X1)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_48,c_0_55])).

cnf(c_0_61,negated_conjecture,
    ( k3_tarski(k1_zfmisc_1(u1_struct_0(esk5_0))) = u1_struct_0(esk5_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_46])).

cnf(c_0_62,plain,
    ( v1_xboole_0(X1)
    | r1_tarski(X2,X1)
    | ~ r2_hidden(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_56])).

cnf(c_0_63,negated_conjecture,
    ( r2_hidden(u1_pre_topc(esk5_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk5_0)))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_35]),c_0_58])).

cnf(c_0_64,plain,
    ( v1_xboole_0(X1)
    | k4_yellow_0(k2_yellow_1(X1)) = k3_tarski(X1)
    | ~ r2_hidden(k3_tarski(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_65,negated_conjecture,
    ( k3_tarski(X1) = u1_struct_0(esk5_0)
    | ~ r2_hidden(u1_struct_0(esk5_0),X1)
    | ~ r1_tarski(X1,k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_66,negated_conjecture,
    ( r1_tarski(u1_pre_topc(esk5_0),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_50])).

cnf(c_0_67,plain,
    ( k4_yellow_0(k2_yellow_1(X1)) = k3_tarski(X1)
    | ~ r2_hidden(k3_tarski(X1),X1) ),
    inference(csr,[status(thm)],[c_0_64,c_0_30])).

cnf(c_0_68,negated_conjecture,
    ( k3_tarski(u1_pre_topc(esk5_0)) = u1_struct_0(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_40])])).

cnf(c_0_69,negated_conjecture,
    ( k4_yellow_0(k2_yellow_1(u1_pre_topc(esk5_0))) != u1_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_70,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_40])]),c_0_69]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:59:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.41  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.20/0.41  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.20/0.41  #
% 0.20/0.41  # Preprocessing time       : 0.028 s
% 0.20/0.41  # Presaturation interreduction done
% 0.20/0.41  
% 0.20/0.41  # Proof found!
% 0.20/0.41  # SZS status Theorem
% 0.20/0.41  # SZS output start CNFRefutation
% 0.20/0.41  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.20/0.41  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.20/0.41  fof(t5_subset, axiom, ![X1, X2, X3]:~(((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))&v1_xboole_0(X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 0.20/0.41  fof(dt_u1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 0.20/0.41  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 0.20/0.41  fof(t24_yellow_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>k4_yellow_0(k2_yellow_1(u1_pre_topc(X1)))=u1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_yellow_1)).
% 0.20/0.41  fof(t94_zfmisc_1, axiom, ![X1, X2]:(![X3]:(r2_hidden(X3,X1)=>r1_tarski(X3,X2))=>r1_tarski(k3_tarski(X1),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_zfmisc_1)).
% 0.20/0.41  fof(d1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>(v2_pre_topc(X1)<=>((r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))&![X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>(r1_tarski(X2,u1_pre_topc(X1))=>r2_hidden(k5_setfam_1(u1_struct_0(X1),X2),u1_pre_topc(X1)))))&![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((r2_hidden(X2,u1_pre_topc(X1))&r2_hidden(X3,u1_pre_topc(X1)))=>r2_hidden(k9_subset_1(u1_struct_0(X1),X2,X3),u1_pre_topc(X1)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_pre_topc)).
% 0.20/0.41  fof(l49_zfmisc_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>r1_tarski(X1,k3_tarski(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 0.20/0.41  fof(t95_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>r1_tarski(k3_tarski(X1),k3_tarski(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_zfmisc_1)).
% 0.20/0.41  fof(t14_yellow_1, axiom, ![X1]:(~(v1_xboole_0(X1))=>(r2_hidden(k3_tarski(X1),X1)=>k4_yellow_0(k2_yellow_1(X1))=k3_tarski(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_yellow_1)).
% 0.20/0.41  fof(c_0_11, plain, ![X4, X5]:(((r1_tarski(X4,X5)|X4!=X5)&(r1_tarski(X5,X4)|X4!=X5))&(~r1_tarski(X4,X5)|~r1_tarski(X5,X4)|X4=X5)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.20/0.41  fof(c_0_12, plain, ![X15, X16]:((~m1_subset_1(X15,k1_zfmisc_1(X16))|r1_tarski(X15,X16))&(~r1_tarski(X15,X16)|m1_subset_1(X15,k1_zfmisc_1(X16)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.20/0.41  cnf(c_0_13, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.41  fof(c_0_14, plain, ![X17, X18, X19]:(~r2_hidden(X17,X18)|~m1_subset_1(X18,k1_zfmisc_1(X19))|~v1_xboole_0(X19)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).
% 0.20/0.41  cnf(c_0_15, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.41  cnf(c_0_16, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_13])).
% 0.20/0.41  fof(c_0_17, plain, ![X27]:(~l1_pre_topc(X27)|m1_subset_1(u1_pre_topc(X27),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X27))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).
% 0.20/0.41  fof(c_0_18, plain, ![X13, X14]:(((~m1_subset_1(X14,X13)|r2_hidden(X14,X13)|v1_xboole_0(X13))&(~r2_hidden(X14,X13)|m1_subset_1(X14,X13)|v1_xboole_0(X13)))&((~m1_subset_1(X14,X13)|v1_xboole_0(X14)|~v1_xboole_0(X13))&(~v1_xboole_0(X14)|m1_subset_1(X14,X13)|~v1_xboole_0(X13)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 0.20/0.41  fof(c_0_19, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>k4_yellow_0(k2_yellow_1(u1_pre_topc(X1)))=u1_struct_0(X1))), inference(assume_negation,[status(cth)],[t24_yellow_1])).
% 0.20/0.41  fof(c_0_20, plain, ![X8, X9]:((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(k3_tarski(X8),X9))&(~r1_tarski(esk1_2(X8,X9),X9)|r1_tarski(k3_tarski(X8),X9))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_zfmisc_1])])])])).
% 0.20/0.41  cnf(c_0_21, plain, (~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.41  cnf(c_0_22, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.20/0.41  cnf(c_0_23, plain, (m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.41  cnf(c_0_24, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.41  fof(c_0_25, plain, ![X20, X21, X22, X23]:((((r2_hidden(u1_struct_0(X20),u1_pre_topc(X20))|~v2_pre_topc(X20)|~l1_pre_topc(X20))&(~m1_subset_1(X21,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X20))))|(~r1_tarski(X21,u1_pre_topc(X20))|r2_hidden(k5_setfam_1(u1_struct_0(X20),X21),u1_pre_topc(X20)))|~v2_pre_topc(X20)|~l1_pre_topc(X20)))&(~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X20)))|(~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X20)))|(~r2_hidden(X22,u1_pre_topc(X20))|~r2_hidden(X23,u1_pre_topc(X20))|r2_hidden(k9_subset_1(u1_struct_0(X20),X22,X23),u1_pre_topc(X20))))|~v2_pre_topc(X20)|~l1_pre_topc(X20)))&(((m1_subset_1(esk3_1(X20),k1_zfmisc_1(u1_struct_0(X20)))|(m1_subset_1(esk2_1(X20),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X20))))|~r2_hidden(u1_struct_0(X20),u1_pre_topc(X20)))|v2_pre_topc(X20)|~l1_pre_topc(X20))&((m1_subset_1(esk4_1(X20),k1_zfmisc_1(u1_struct_0(X20)))|(m1_subset_1(esk2_1(X20),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X20))))|~r2_hidden(u1_struct_0(X20),u1_pre_topc(X20)))|v2_pre_topc(X20)|~l1_pre_topc(X20))&(((r2_hidden(esk3_1(X20),u1_pre_topc(X20))|(m1_subset_1(esk2_1(X20),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X20))))|~r2_hidden(u1_struct_0(X20),u1_pre_topc(X20)))|v2_pre_topc(X20)|~l1_pre_topc(X20))&(r2_hidden(esk4_1(X20),u1_pre_topc(X20))|(m1_subset_1(esk2_1(X20),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X20))))|~r2_hidden(u1_struct_0(X20),u1_pre_topc(X20)))|v2_pre_topc(X20)|~l1_pre_topc(X20)))&(~r2_hidden(k9_subset_1(u1_struct_0(X20),esk3_1(X20),esk4_1(X20)),u1_pre_topc(X20))|(m1_subset_1(esk2_1(X20),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X20))))|~r2_hidden(u1_struct_0(X20),u1_pre_topc(X20)))|v2_pre_topc(X20)|~l1_pre_topc(X20)))))&(((m1_subset_1(esk3_1(X20),k1_zfmisc_1(u1_struct_0(X20)))|(r1_tarski(esk2_1(X20),u1_pre_topc(X20))|~r2_hidden(u1_struct_0(X20),u1_pre_topc(X20)))|v2_pre_topc(X20)|~l1_pre_topc(X20))&((m1_subset_1(esk4_1(X20),k1_zfmisc_1(u1_struct_0(X20)))|(r1_tarski(esk2_1(X20),u1_pre_topc(X20))|~r2_hidden(u1_struct_0(X20),u1_pre_topc(X20)))|v2_pre_topc(X20)|~l1_pre_topc(X20))&(((r2_hidden(esk3_1(X20),u1_pre_topc(X20))|(r1_tarski(esk2_1(X20),u1_pre_topc(X20))|~r2_hidden(u1_struct_0(X20),u1_pre_topc(X20)))|v2_pre_topc(X20)|~l1_pre_topc(X20))&(r2_hidden(esk4_1(X20),u1_pre_topc(X20))|(r1_tarski(esk2_1(X20),u1_pre_topc(X20))|~r2_hidden(u1_struct_0(X20),u1_pre_topc(X20)))|v2_pre_topc(X20)|~l1_pre_topc(X20)))&(~r2_hidden(k9_subset_1(u1_struct_0(X20),esk3_1(X20),esk4_1(X20)),u1_pre_topc(X20))|(r1_tarski(esk2_1(X20),u1_pre_topc(X20))|~r2_hidden(u1_struct_0(X20),u1_pre_topc(X20)))|v2_pre_topc(X20)|~l1_pre_topc(X20)))))&((m1_subset_1(esk3_1(X20),k1_zfmisc_1(u1_struct_0(X20)))|(~r2_hidden(k5_setfam_1(u1_struct_0(X20),esk2_1(X20)),u1_pre_topc(X20))|~r2_hidden(u1_struct_0(X20),u1_pre_topc(X20)))|v2_pre_topc(X20)|~l1_pre_topc(X20))&((m1_subset_1(esk4_1(X20),k1_zfmisc_1(u1_struct_0(X20)))|(~r2_hidden(k5_setfam_1(u1_struct_0(X20),esk2_1(X20)),u1_pre_topc(X20))|~r2_hidden(u1_struct_0(X20),u1_pre_topc(X20)))|v2_pre_topc(X20)|~l1_pre_topc(X20))&(((r2_hidden(esk3_1(X20),u1_pre_topc(X20))|(~r2_hidden(k5_setfam_1(u1_struct_0(X20),esk2_1(X20)),u1_pre_topc(X20))|~r2_hidden(u1_struct_0(X20),u1_pre_topc(X20)))|v2_pre_topc(X20)|~l1_pre_topc(X20))&(r2_hidden(esk4_1(X20),u1_pre_topc(X20))|(~r2_hidden(k5_setfam_1(u1_struct_0(X20),esk2_1(X20)),u1_pre_topc(X20))|~r2_hidden(u1_struct_0(X20),u1_pre_topc(X20)))|v2_pre_topc(X20)|~l1_pre_topc(X20)))&(~r2_hidden(k9_subset_1(u1_struct_0(X20),esk3_1(X20),esk4_1(X20)),u1_pre_topc(X20))|(~r2_hidden(k5_setfam_1(u1_struct_0(X20),esk2_1(X20)),u1_pre_topc(X20))|~r2_hidden(u1_struct_0(X20),u1_pre_topc(X20)))|v2_pre_topc(X20)|~l1_pre_topc(X20)))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_pre_topc])])])])])).
% 0.20/0.41  fof(c_0_26, negated_conjecture, (((~v2_struct_0(esk5_0)&v2_pre_topc(esk5_0))&l1_pre_topc(esk5_0))&k4_yellow_0(k2_yellow_1(u1_pre_topc(esk5_0)))!=u1_struct_0(esk5_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_19])])])])).
% 0.20/0.41  cnf(c_0_27, plain, (r1_tarski(k3_tarski(X1),X2)|~r1_tarski(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.41  cnf(c_0_28, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.41  cnf(c_0_29, plain, (m1_subset_1(X1,X2)|v1_xboole_0(X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.41  cnf(c_0_30, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.20/0.41  cnf(c_0_31, plain, (~l1_pre_topc(X1)|~v1_xboole_0(k1_zfmisc_1(u1_struct_0(X1)))|~r2_hidden(X2,u1_pre_topc(X1))), inference(spm,[status(thm)],[c_0_21, c_0_23])).
% 0.20/0.41  cnf(c_0_32, plain, (v1_xboole_0(k1_zfmisc_1(X1))|r2_hidden(X1,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_24, c_0_22])).
% 0.20/0.41  cnf(c_0_33, plain, (r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.41  cnf(c_0_34, negated_conjecture, (v2_pre_topc(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.41  cnf(c_0_35, negated_conjecture, (l1_pre_topc(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.41  fof(c_0_36, plain, ![X6, X7]:(~r2_hidden(X6,X7)|r1_tarski(X6,k3_tarski(X7))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l49_zfmisc_1])])).
% 0.20/0.41  cnf(c_0_37, plain, (r1_tarski(k3_tarski(X1),X2)|~m1_subset_1(esk1_2(X1,X2),k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.20/0.41  cnf(c_0_38, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(csr,[status(thm)],[c_0_29, c_0_30])).
% 0.20/0.41  cnf(c_0_39, plain, (r2_hidden(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~r2_hidden(X2,u1_pre_topc(X1))), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.20/0.41  cnf(c_0_40, negated_conjecture, (r2_hidden(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35])])).
% 0.20/0.41  cnf(c_0_41, plain, (v1_xboole_0(X1)|~m1_subset_1(X1,X2)|~v1_xboole_0(X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.41  cnf(c_0_42, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.41  cnf(c_0_43, plain, (r1_tarski(X1,k3_tarski(X2))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.20/0.41  cnf(c_0_44, plain, (r1_tarski(k3_tarski(X1),X2)|~r2_hidden(esk1_2(X1,X2),k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.20/0.41  cnf(c_0_45, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(k3_tarski(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.41  cnf(c_0_46, negated_conjecture, (r2_hidden(u1_struct_0(esk5_0),k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_35])])).
% 0.20/0.41  cnf(c_0_47, plain, (v1_xboole_0(X1)|~v1_xboole_0(k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_41, c_0_22])).
% 0.20/0.41  cnf(c_0_48, plain, (k3_tarski(X1)=X2|~r2_hidden(X2,X1)|~r1_tarski(k3_tarski(X1),X2)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.20/0.41  cnf(c_0_49, plain, (r1_tarski(k3_tarski(k1_zfmisc_1(X1)),X1)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.20/0.41  cnf(c_0_50, negated_conjecture, (~v1_xboole_0(k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(spm,[status(thm)],[c_0_30, c_0_46])).
% 0.20/0.41  cnf(c_0_51, plain, (v1_xboole_0(X1)|r2_hidden(X1,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_47, c_0_32])).
% 0.20/0.41  fof(c_0_52, plain, ![X11, X12]:(~r1_tarski(X11,X12)|r1_tarski(k3_tarski(X11),k3_tarski(X12))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t95_zfmisc_1])])).
% 0.20/0.41  cnf(c_0_53, plain, (k3_tarski(k1_zfmisc_1(X1))=X1|~r2_hidden(X1,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.20/0.41  cnf(c_0_54, negated_conjecture, (r2_hidden(k1_zfmisc_1(u1_struct_0(esk5_0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk5_0))))), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.20/0.41  cnf(c_0_55, plain, (r1_tarski(k3_tarski(X1),k3_tarski(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.20/0.41  cnf(c_0_56, plain, (k3_tarski(k1_zfmisc_1(X1))=X1|v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_53, c_0_51])).
% 0.20/0.41  cnf(c_0_57, plain, (v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|r2_hidden(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_24, c_0_23])).
% 0.20/0.41  cnf(c_0_58, negated_conjecture, (~v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk5_0))))), inference(spm,[status(thm)],[c_0_30, c_0_54])).
% 0.20/0.41  fof(c_0_59, plain, ![X28]:(v1_xboole_0(X28)|(~r2_hidden(k3_tarski(X28),X28)|k4_yellow_0(k2_yellow_1(X28))=k3_tarski(X28))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t14_yellow_1])])])).
% 0.20/0.41  cnf(c_0_60, plain, (k3_tarski(X1)=k3_tarski(X2)|~r2_hidden(k3_tarski(X2),X1)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_48, c_0_55])).
% 0.20/0.41  cnf(c_0_61, negated_conjecture, (k3_tarski(k1_zfmisc_1(u1_struct_0(esk5_0)))=u1_struct_0(esk5_0)), inference(spm,[status(thm)],[c_0_53, c_0_46])).
% 0.20/0.41  cnf(c_0_62, plain, (v1_xboole_0(X1)|r1_tarski(X2,X1)|~r2_hidden(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_43, c_0_56])).
% 0.20/0.41  cnf(c_0_63, negated_conjecture, (r2_hidden(u1_pre_topc(esk5_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk5_0))))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_35]), c_0_58])).
% 0.20/0.41  cnf(c_0_64, plain, (v1_xboole_0(X1)|k4_yellow_0(k2_yellow_1(X1))=k3_tarski(X1)|~r2_hidden(k3_tarski(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.20/0.41  cnf(c_0_65, negated_conjecture, (k3_tarski(X1)=u1_struct_0(esk5_0)|~r2_hidden(u1_struct_0(esk5_0),X1)|~r1_tarski(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.20/0.41  cnf(c_0_66, negated_conjecture, (r1_tarski(u1_pre_topc(esk5_0),k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_50])).
% 0.20/0.41  cnf(c_0_67, plain, (k4_yellow_0(k2_yellow_1(X1))=k3_tarski(X1)|~r2_hidden(k3_tarski(X1),X1)), inference(csr,[status(thm)],[c_0_64, c_0_30])).
% 0.20/0.41  cnf(c_0_68, negated_conjecture, (k3_tarski(u1_pre_topc(esk5_0))=u1_struct_0(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_40])])).
% 0.20/0.41  cnf(c_0_69, negated_conjecture, (k4_yellow_0(k2_yellow_1(u1_pre_topc(esk5_0)))!=u1_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.41  cnf(c_0_70, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_40])]), c_0_69]), ['proof']).
% 0.20/0.41  # SZS output end CNFRefutation
% 0.20/0.41  # Proof object total steps             : 71
% 0.20/0.41  # Proof object clause steps            : 48
% 0.20/0.41  # Proof object formula steps           : 23
% 0.20/0.41  # Proof object conjectures             : 17
% 0.20/0.41  # Proof object clause conjectures      : 14
% 0.20/0.41  # Proof object formula conjectures     : 3
% 0.20/0.41  # Proof object initial clauses used    : 18
% 0.20/0.41  # Proof object initial formulas used   : 11
% 0.20/0.41  # Proof object generating inferences   : 27
% 0.20/0.41  # Proof object simplifying inferences  : 14
% 0.20/0.41  # Training examples: 0 positive, 0 negative
% 0.20/0.41  # Parsed axioms                        : 11
% 0.20/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.41  # Initial clauses                      : 38
% 0.20/0.41  # Removed in clause preprocessing      : 0
% 0.20/0.41  # Initial clauses in saturation        : 38
% 0.20/0.41  # Processed clauses                    : 469
% 0.20/0.41  # ...of these trivial                  : 0
% 0.20/0.41  # ...subsumed                          : 233
% 0.20/0.41  # ...remaining for further processing  : 236
% 0.20/0.41  # Other redundant clauses eliminated   : 2
% 0.20/0.41  # Clauses deleted for lack of memory   : 0
% 0.20/0.41  # Backward-subsumed                    : 2
% 0.20/0.41  # Backward-rewritten                   : 8
% 0.20/0.41  # Generated clauses                    : 1413
% 0.20/0.41  # ...of the previous two non-trivial   : 1248
% 0.20/0.41  # Contextual simplify-reflections      : 3
% 0.20/0.41  # Paramodulations                      : 1411
% 0.20/0.41  # Factorizations                       : 0
% 0.20/0.41  # Equation resolutions                 : 2
% 0.20/0.41  # Propositional unsat checks           : 0
% 0.20/0.41  #    Propositional check models        : 0
% 0.20/0.41  #    Propositional check unsatisfiable : 0
% 0.20/0.41  #    Propositional clauses             : 0
% 0.20/0.41  #    Propositional clauses after purity: 0
% 0.20/0.41  #    Propositional unsat core size     : 0
% 0.20/0.41  #    Propositional preprocessing time  : 0.000
% 0.20/0.41  #    Propositional encoding time       : 0.000
% 0.20/0.41  #    Propositional solver time         : 0.000
% 0.20/0.41  #    Success case prop preproc time    : 0.000
% 0.20/0.41  #    Success case prop encoding time   : 0.000
% 0.20/0.41  #    Success case prop solver time     : 0.000
% 0.20/0.41  # Current number of processed clauses  : 187
% 0.20/0.41  #    Positive orientable unit clauses  : 23
% 0.20/0.41  #    Positive unorientable unit clauses: 0
% 0.20/0.41  #    Negative unit clauses             : 7
% 0.20/0.41  #    Non-unit-clauses                  : 157
% 0.20/0.41  # Current number of unprocessed clauses: 831
% 0.20/0.41  # ...number of literals in the above   : 3114
% 0.20/0.41  # Current number of archived formulas  : 0
% 0.20/0.41  # Current number of archived clauses   : 47
% 0.20/0.41  # Clause-clause subsumption calls (NU) : 1998
% 0.20/0.41  # Rec. Clause-clause subsumption calls : 1323
% 0.20/0.41  # Non-unit clause-clause subsumptions  : 175
% 0.20/0.41  # Unit Clause-clause subsumption calls : 5
% 0.20/0.41  # Rewrite failures with RHS unbound    : 0
% 0.20/0.41  # BW rewrite match attempts            : 12
% 0.20/0.41  # BW rewrite match successes           : 3
% 0.20/0.41  # Condensation attempts                : 0
% 0.20/0.41  # Condensation successes               : 0
% 0.20/0.41  # Termbank termtop insertions          : 21799
% 0.20/0.41  
% 0.20/0.41  # -------------------------------------------------
% 0.20/0.41  # User time                : 0.063 s
% 0.20/0.41  # System time              : 0.003 s
% 0.20/0.41  # Total time               : 0.066 s
% 0.20/0.41  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
