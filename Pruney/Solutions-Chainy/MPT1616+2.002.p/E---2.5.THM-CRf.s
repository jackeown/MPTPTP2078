%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:15:56 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   48 (  73 expanded)
%              Number of clauses        :   25 (  31 expanded)
%              Number of leaves         :   11 (  18 expanded)
%              Depth                    :    8
%              Number of atoms          :  217 ( 391 expanded)
%              Number of equality atoms :   25 (  40 expanded)
%              Maximal formula depth    :   27 (   4 average)
%              Maximal clause size      :   90 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d12_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_setfam_1(X2,X1)
    <=> r1_tarski(X1,k3_tarski(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_setfam_1)).

fof(l49_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => r1_tarski(X1,k3_tarski(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t60_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ( m1_setfam_1(X2,X1)
      <=> k5_setfam_1(X1,X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_setfam_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(redefinition_k5_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => k5_setfam_1(X1,X2) = k3_tarski(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).

fof(dt_u1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(t24_yellow_1,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => k4_yellow_0(k2_yellow_1(u1_pre_topc(X1))) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_yellow_1)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_pre_topc)).

fof(t14_yellow_1,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ( r2_hidden(k3_tarski(X1),X1)
       => k4_yellow_0(k2_yellow_1(X1)) = k3_tarski(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_yellow_1)).

fof(c_0_11,plain,(
    ! [X8,X9] :
      ( ( ~ m1_setfam_1(X9,X8)
        | r1_tarski(X8,k3_tarski(X9)) )
      & ( ~ r1_tarski(X8,k3_tarski(X9))
        | m1_setfam_1(X9,X8) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_setfam_1])])).

fof(c_0_12,plain,(
    ! [X6,X7] :
      ( ~ r2_hidden(X6,X7)
      | r1_tarski(X6,k3_tarski(X7)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l49_zfmisc_1])])).

fof(c_0_13,plain,(
    ! [X4,X5] :
      ( ( r1_tarski(X4,X5)
        | X4 != X5 )
      & ( r1_tarski(X5,X4)
        | X4 != X5 )
      & ( ~ r1_tarski(X4,X5)
        | ~ r1_tarski(X5,X4)
        | X4 = X5 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_14,plain,(
    ! [X17,X18] :
      ( ( ~ m1_setfam_1(X18,X17)
        | k5_setfam_1(X17,X18) = X17
        | ~ m1_subset_1(X18,k1_zfmisc_1(k1_zfmisc_1(X17))) )
      & ( k5_setfam_1(X17,X18) != X17
        | m1_setfam_1(X18,X17)
        | ~ m1_subset_1(X18,k1_zfmisc_1(k1_zfmisc_1(X17))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t60_setfam_1])])])).

cnf(c_0_15,plain,
    ( m1_setfam_1(X2,X1)
    | ~ r1_tarski(X1,k3_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( r1_tarski(X1,k3_tarski(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_17,plain,(
    ! [X12,X13] :
      ( ( ~ m1_subset_1(X12,k1_zfmisc_1(X13))
        | r1_tarski(X12,X13) )
      & ( ~ r1_tarski(X12,X13)
        | m1_subset_1(X12,k1_zfmisc_1(X13)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_18,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_19,plain,(
    ! [X10,X11] :
      ( ~ m1_subset_1(X11,k1_zfmisc_1(k1_zfmisc_1(X10)))
      | k5_setfam_1(X10,X11) = k3_tarski(X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k5_setfam_1])])).

fof(c_0_20,plain,(
    ! [X26] :
      ( ~ l1_pre_topc(X26)
      | m1_subset_1(u1_pre_topc(X26),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X26)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).

cnf(c_0_21,plain,
    ( k5_setfam_1(X2,X1) = X2
    | ~ m1_setfam_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,plain,
    ( m1_setfam_1(X1,X2)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

fof(c_0_23,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => k4_yellow_0(k2_yellow_1(u1_pre_topc(X1))) = u1_struct_0(X1) ) ),
    inference(assume_negation,[status(cth)],[t24_yellow_1])).

fof(c_0_24,plain,(
    ! [X14,X15,X16] :
      ( ~ r2_hidden(X14,X15)
      | ~ m1_subset_1(X15,k1_zfmisc_1(X16))
      | ~ v1_xboole_0(X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

cnf(c_0_25,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_18])).

cnf(c_0_27,plain,
    ( k5_setfam_1(X2,X1) = k3_tarski(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_28,plain,
    ( m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,plain,
    ( k5_setfam_1(X1,X2) = X1
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

fof(c_0_30,plain,(
    ! [X19,X20,X21,X22] :
      ( ( r2_hidden(u1_struct_0(X19),u1_pre_topc(X19))
        | ~ v2_pre_topc(X19)
        | ~ l1_pre_topc(X19) )
      & ( ~ m1_subset_1(X20,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X19))))
        | ~ r1_tarski(X20,u1_pre_topc(X19))
        | r2_hidden(k5_setfam_1(u1_struct_0(X19),X20),u1_pre_topc(X19))
        | ~ v2_pre_topc(X19)
        | ~ l1_pre_topc(X19) )
      & ( ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X19)))
        | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X19)))
        | ~ r2_hidden(X21,u1_pre_topc(X19))
        | ~ r2_hidden(X22,u1_pre_topc(X19))
        | r2_hidden(k9_subset_1(u1_struct_0(X19),X21,X22),u1_pre_topc(X19))
        | ~ v2_pre_topc(X19)
        | ~ l1_pre_topc(X19) )
      & ( m1_subset_1(esk2_1(X19),k1_zfmisc_1(u1_struct_0(X19)))
        | m1_subset_1(esk1_1(X19),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X19))))
        | ~ r2_hidden(u1_struct_0(X19),u1_pre_topc(X19))
        | v2_pre_topc(X19)
        | ~ l1_pre_topc(X19) )
      & ( m1_subset_1(esk3_1(X19),k1_zfmisc_1(u1_struct_0(X19)))
        | m1_subset_1(esk1_1(X19),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X19))))
        | ~ r2_hidden(u1_struct_0(X19),u1_pre_topc(X19))
        | v2_pre_topc(X19)
        | ~ l1_pre_topc(X19) )
      & ( r2_hidden(esk2_1(X19),u1_pre_topc(X19))
        | m1_subset_1(esk1_1(X19),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X19))))
        | ~ r2_hidden(u1_struct_0(X19),u1_pre_topc(X19))
        | v2_pre_topc(X19)
        | ~ l1_pre_topc(X19) )
      & ( r2_hidden(esk3_1(X19),u1_pre_topc(X19))
        | m1_subset_1(esk1_1(X19),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X19))))
        | ~ r2_hidden(u1_struct_0(X19),u1_pre_topc(X19))
        | v2_pre_topc(X19)
        | ~ l1_pre_topc(X19) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X19),esk2_1(X19),esk3_1(X19)),u1_pre_topc(X19))
        | m1_subset_1(esk1_1(X19),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X19))))
        | ~ r2_hidden(u1_struct_0(X19),u1_pre_topc(X19))
        | v2_pre_topc(X19)
        | ~ l1_pre_topc(X19) )
      & ( m1_subset_1(esk2_1(X19),k1_zfmisc_1(u1_struct_0(X19)))
        | r1_tarski(esk1_1(X19),u1_pre_topc(X19))
        | ~ r2_hidden(u1_struct_0(X19),u1_pre_topc(X19))
        | v2_pre_topc(X19)
        | ~ l1_pre_topc(X19) )
      & ( m1_subset_1(esk3_1(X19),k1_zfmisc_1(u1_struct_0(X19)))
        | r1_tarski(esk1_1(X19),u1_pre_topc(X19))
        | ~ r2_hidden(u1_struct_0(X19),u1_pre_topc(X19))
        | v2_pre_topc(X19)
        | ~ l1_pre_topc(X19) )
      & ( r2_hidden(esk2_1(X19),u1_pre_topc(X19))
        | r1_tarski(esk1_1(X19),u1_pre_topc(X19))
        | ~ r2_hidden(u1_struct_0(X19),u1_pre_topc(X19))
        | v2_pre_topc(X19)
        | ~ l1_pre_topc(X19) )
      & ( r2_hidden(esk3_1(X19),u1_pre_topc(X19))
        | r1_tarski(esk1_1(X19),u1_pre_topc(X19))
        | ~ r2_hidden(u1_struct_0(X19),u1_pre_topc(X19))
        | v2_pre_topc(X19)
        | ~ l1_pre_topc(X19) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X19),esk2_1(X19),esk3_1(X19)),u1_pre_topc(X19))
        | r1_tarski(esk1_1(X19),u1_pre_topc(X19))
        | ~ r2_hidden(u1_struct_0(X19),u1_pre_topc(X19))
        | v2_pre_topc(X19)
        | ~ l1_pre_topc(X19) )
      & ( m1_subset_1(esk2_1(X19),k1_zfmisc_1(u1_struct_0(X19)))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X19),esk1_1(X19)),u1_pre_topc(X19))
        | ~ r2_hidden(u1_struct_0(X19),u1_pre_topc(X19))
        | v2_pre_topc(X19)
        | ~ l1_pre_topc(X19) )
      & ( m1_subset_1(esk3_1(X19),k1_zfmisc_1(u1_struct_0(X19)))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X19),esk1_1(X19)),u1_pre_topc(X19))
        | ~ r2_hidden(u1_struct_0(X19),u1_pre_topc(X19))
        | v2_pre_topc(X19)
        | ~ l1_pre_topc(X19) )
      & ( r2_hidden(esk2_1(X19),u1_pre_topc(X19))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X19),esk1_1(X19)),u1_pre_topc(X19))
        | ~ r2_hidden(u1_struct_0(X19),u1_pre_topc(X19))
        | v2_pre_topc(X19)
        | ~ l1_pre_topc(X19) )
      & ( r2_hidden(esk3_1(X19),u1_pre_topc(X19))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X19),esk1_1(X19)),u1_pre_topc(X19))
        | ~ r2_hidden(u1_struct_0(X19),u1_pre_topc(X19))
        | v2_pre_topc(X19)
        | ~ l1_pre_topc(X19) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X19),esk2_1(X19),esk3_1(X19)),u1_pre_topc(X19))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X19),esk1_1(X19)),u1_pre_topc(X19))
        | ~ r2_hidden(u1_struct_0(X19),u1_pre_topc(X19))
        | v2_pre_topc(X19)
        | ~ l1_pre_topc(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_pre_topc])])])])])).

fof(c_0_31,negated_conjecture,
    ( ~ v2_struct_0(esk4_0)
    & v2_pre_topc(esk4_0)
    & l1_pre_topc(esk4_0)
    & k4_yellow_0(k2_yellow_1(u1_pre_topc(esk4_0))) != u1_struct_0(esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_23])])])])).

fof(c_0_32,plain,(
    ! [X27] :
      ( v1_xboole_0(X27)
      | ~ r2_hidden(k3_tarski(X27),X27)
      | k4_yellow_0(k2_yellow_1(X27)) = k3_tarski(X27) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t14_yellow_1])])])).

cnf(c_0_33,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_34,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_35,plain,
    ( k5_setfam_1(u1_struct_0(X1),u1_pre_topc(X1)) = k3_tarski(u1_pre_topc(X1))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_36,plain,
    ( k5_setfam_1(u1_struct_0(X1),u1_pre_topc(X1)) = u1_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ r2_hidden(u1_struct_0(X1),u1_pre_topc(X1)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_28])).

cnf(c_0_37,plain,
    ( r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_38,negated_conjecture,
    ( v2_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_39,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_40,plain,
    ( v1_xboole_0(X1)
    | k4_yellow_0(k2_yellow_1(X1)) = k3_tarski(X1)
    | ~ r2_hidden(k3_tarski(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_41,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_42,plain,
    ( k3_tarski(u1_pre_topc(X1)) = u1_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ r2_hidden(u1_struct_0(X1),u1_pre_topc(X1)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39])])).

cnf(c_0_44,plain,
    ( k4_yellow_0(k2_yellow_1(X1)) = k3_tarski(X1)
    | ~ r2_hidden(k3_tarski(X1),X1) ),
    inference(csr,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_45,negated_conjecture,
    ( k3_tarski(u1_pre_topc(esk4_0)) = u1_struct_0(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_39])])).

cnf(c_0_46,negated_conjecture,
    ( k4_yellow_0(k2_yellow_1(u1_pre_topc(esk4_0))) != u1_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_47,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_43])]),c_0_46]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:28:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.40  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.20/0.40  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.20/0.40  #
% 0.20/0.40  # Preprocessing time       : 0.044 s
% 0.20/0.40  # Presaturation interreduction done
% 0.20/0.40  
% 0.20/0.40  # Proof found!
% 0.20/0.40  # SZS status Theorem
% 0.20/0.40  # SZS output start CNFRefutation
% 0.20/0.40  fof(d12_setfam_1, axiom, ![X1, X2]:(m1_setfam_1(X2,X1)<=>r1_tarski(X1,k3_tarski(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_setfam_1)).
% 0.20/0.40  fof(l49_zfmisc_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>r1_tarski(X1,k3_tarski(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 0.20/0.40  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.20/0.40  fof(t60_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>(m1_setfam_1(X2,X1)<=>k5_setfam_1(X1,X2)=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_setfam_1)).
% 0.20/0.40  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.20/0.40  fof(redefinition_k5_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>k5_setfam_1(X1,X2)=k3_tarski(X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k5_setfam_1)).
% 0.20/0.40  fof(dt_u1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 0.20/0.40  fof(t24_yellow_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>k4_yellow_0(k2_yellow_1(u1_pre_topc(X1)))=u1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_yellow_1)).
% 0.20/0.40  fof(t5_subset, axiom, ![X1, X2, X3]:~(((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))&v1_xboole_0(X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 0.20/0.40  fof(d1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>(v2_pre_topc(X1)<=>((r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))&![X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>(r1_tarski(X2,u1_pre_topc(X1))=>r2_hidden(k5_setfam_1(u1_struct_0(X1),X2),u1_pre_topc(X1)))))&![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((r2_hidden(X2,u1_pre_topc(X1))&r2_hidden(X3,u1_pre_topc(X1)))=>r2_hidden(k9_subset_1(u1_struct_0(X1),X2,X3),u1_pre_topc(X1)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_pre_topc)).
% 0.20/0.40  fof(t14_yellow_1, axiom, ![X1]:(~(v1_xboole_0(X1))=>(r2_hidden(k3_tarski(X1),X1)=>k4_yellow_0(k2_yellow_1(X1))=k3_tarski(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_yellow_1)).
% 0.20/0.40  fof(c_0_11, plain, ![X8, X9]:((~m1_setfam_1(X9,X8)|r1_tarski(X8,k3_tarski(X9)))&(~r1_tarski(X8,k3_tarski(X9))|m1_setfam_1(X9,X8))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_setfam_1])])).
% 0.20/0.40  fof(c_0_12, plain, ![X6, X7]:(~r2_hidden(X6,X7)|r1_tarski(X6,k3_tarski(X7))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l49_zfmisc_1])])).
% 0.20/0.40  fof(c_0_13, plain, ![X4, X5]:(((r1_tarski(X4,X5)|X4!=X5)&(r1_tarski(X5,X4)|X4!=X5))&(~r1_tarski(X4,X5)|~r1_tarski(X5,X4)|X4=X5)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.20/0.40  fof(c_0_14, plain, ![X17, X18]:((~m1_setfam_1(X18,X17)|k5_setfam_1(X17,X18)=X17|~m1_subset_1(X18,k1_zfmisc_1(k1_zfmisc_1(X17))))&(k5_setfam_1(X17,X18)!=X17|m1_setfam_1(X18,X17)|~m1_subset_1(X18,k1_zfmisc_1(k1_zfmisc_1(X17))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t60_setfam_1])])])).
% 0.20/0.40  cnf(c_0_15, plain, (m1_setfam_1(X2,X1)|~r1_tarski(X1,k3_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.40  cnf(c_0_16, plain, (r1_tarski(X1,k3_tarski(X2))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.40  fof(c_0_17, plain, ![X12, X13]:((~m1_subset_1(X12,k1_zfmisc_1(X13))|r1_tarski(X12,X13))&(~r1_tarski(X12,X13)|m1_subset_1(X12,k1_zfmisc_1(X13)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.20/0.40  cnf(c_0_18, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.40  fof(c_0_19, plain, ![X10, X11]:(~m1_subset_1(X11,k1_zfmisc_1(k1_zfmisc_1(X10)))|k5_setfam_1(X10,X11)=k3_tarski(X11)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k5_setfam_1])])).
% 0.20/0.40  fof(c_0_20, plain, ![X26]:(~l1_pre_topc(X26)|m1_subset_1(u1_pre_topc(X26),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X26))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).
% 0.20/0.40  cnf(c_0_21, plain, (k5_setfam_1(X2,X1)=X2|~m1_setfam_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.40  cnf(c_0_22, plain, (m1_setfam_1(X1,X2)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.20/0.40  fof(c_0_23, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>k4_yellow_0(k2_yellow_1(u1_pre_topc(X1)))=u1_struct_0(X1))), inference(assume_negation,[status(cth)],[t24_yellow_1])).
% 0.20/0.40  fof(c_0_24, plain, ![X14, X15, X16]:(~r2_hidden(X14,X15)|~m1_subset_1(X15,k1_zfmisc_1(X16))|~v1_xboole_0(X16)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).
% 0.20/0.40  cnf(c_0_25, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.40  cnf(c_0_26, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_18])).
% 0.20/0.40  cnf(c_0_27, plain, (k5_setfam_1(X2,X1)=k3_tarski(X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.40  cnf(c_0_28, plain, (m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.40  cnf(c_0_29, plain, (k5_setfam_1(X1,X2)=X1|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.20/0.40  fof(c_0_30, plain, ![X19, X20, X21, X22]:((((r2_hidden(u1_struct_0(X19),u1_pre_topc(X19))|~v2_pre_topc(X19)|~l1_pre_topc(X19))&(~m1_subset_1(X20,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X19))))|(~r1_tarski(X20,u1_pre_topc(X19))|r2_hidden(k5_setfam_1(u1_struct_0(X19),X20),u1_pre_topc(X19)))|~v2_pre_topc(X19)|~l1_pre_topc(X19)))&(~m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X19)))|(~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X19)))|(~r2_hidden(X21,u1_pre_topc(X19))|~r2_hidden(X22,u1_pre_topc(X19))|r2_hidden(k9_subset_1(u1_struct_0(X19),X21,X22),u1_pre_topc(X19))))|~v2_pre_topc(X19)|~l1_pre_topc(X19)))&(((m1_subset_1(esk2_1(X19),k1_zfmisc_1(u1_struct_0(X19)))|(m1_subset_1(esk1_1(X19),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X19))))|~r2_hidden(u1_struct_0(X19),u1_pre_topc(X19)))|v2_pre_topc(X19)|~l1_pre_topc(X19))&((m1_subset_1(esk3_1(X19),k1_zfmisc_1(u1_struct_0(X19)))|(m1_subset_1(esk1_1(X19),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X19))))|~r2_hidden(u1_struct_0(X19),u1_pre_topc(X19)))|v2_pre_topc(X19)|~l1_pre_topc(X19))&(((r2_hidden(esk2_1(X19),u1_pre_topc(X19))|(m1_subset_1(esk1_1(X19),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X19))))|~r2_hidden(u1_struct_0(X19),u1_pre_topc(X19)))|v2_pre_topc(X19)|~l1_pre_topc(X19))&(r2_hidden(esk3_1(X19),u1_pre_topc(X19))|(m1_subset_1(esk1_1(X19),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X19))))|~r2_hidden(u1_struct_0(X19),u1_pre_topc(X19)))|v2_pre_topc(X19)|~l1_pre_topc(X19)))&(~r2_hidden(k9_subset_1(u1_struct_0(X19),esk2_1(X19),esk3_1(X19)),u1_pre_topc(X19))|(m1_subset_1(esk1_1(X19),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X19))))|~r2_hidden(u1_struct_0(X19),u1_pre_topc(X19)))|v2_pre_topc(X19)|~l1_pre_topc(X19)))))&(((m1_subset_1(esk2_1(X19),k1_zfmisc_1(u1_struct_0(X19)))|(r1_tarski(esk1_1(X19),u1_pre_topc(X19))|~r2_hidden(u1_struct_0(X19),u1_pre_topc(X19)))|v2_pre_topc(X19)|~l1_pre_topc(X19))&((m1_subset_1(esk3_1(X19),k1_zfmisc_1(u1_struct_0(X19)))|(r1_tarski(esk1_1(X19),u1_pre_topc(X19))|~r2_hidden(u1_struct_0(X19),u1_pre_topc(X19)))|v2_pre_topc(X19)|~l1_pre_topc(X19))&(((r2_hidden(esk2_1(X19),u1_pre_topc(X19))|(r1_tarski(esk1_1(X19),u1_pre_topc(X19))|~r2_hidden(u1_struct_0(X19),u1_pre_topc(X19)))|v2_pre_topc(X19)|~l1_pre_topc(X19))&(r2_hidden(esk3_1(X19),u1_pre_topc(X19))|(r1_tarski(esk1_1(X19),u1_pre_topc(X19))|~r2_hidden(u1_struct_0(X19),u1_pre_topc(X19)))|v2_pre_topc(X19)|~l1_pre_topc(X19)))&(~r2_hidden(k9_subset_1(u1_struct_0(X19),esk2_1(X19),esk3_1(X19)),u1_pre_topc(X19))|(r1_tarski(esk1_1(X19),u1_pre_topc(X19))|~r2_hidden(u1_struct_0(X19),u1_pre_topc(X19)))|v2_pre_topc(X19)|~l1_pre_topc(X19)))))&((m1_subset_1(esk2_1(X19),k1_zfmisc_1(u1_struct_0(X19)))|(~r2_hidden(k5_setfam_1(u1_struct_0(X19),esk1_1(X19)),u1_pre_topc(X19))|~r2_hidden(u1_struct_0(X19),u1_pre_topc(X19)))|v2_pre_topc(X19)|~l1_pre_topc(X19))&((m1_subset_1(esk3_1(X19),k1_zfmisc_1(u1_struct_0(X19)))|(~r2_hidden(k5_setfam_1(u1_struct_0(X19),esk1_1(X19)),u1_pre_topc(X19))|~r2_hidden(u1_struct_0(X19),u1_pre_topc(X19)))|v2_pre_topc(X19)|~l1_pre_topc(X19))&(((r2_hidden(esk2_1(X19),u1_pre_topc(X19))|(~r2_hidden(k5_setfam_1(u1_struct_0(X19),esk1_1(X19)),u1_pre_topc(X19))|~r2_hidden(u1_struct_0(X19),u1_pre_topc(X19)))|v2_pre_topc(X19)|~l1_pre_topc(X19))&(r2_hidden(esk3_1(X19),u1_pre_topc(X19))|(~r2_hidden(k5_setfam_1(u1_struct_0(X19),esk1_1(X19)),u1_pre_topc(X19))|~r2_hidden(u1_struct_0(X19),u1_pre_topc(X19)))|v2_pre_topc(X19)|~l1_pre_topc(X19)))&(~r2_hidden(k9_subset_1(u1_struct_0(X19),esk2_1(X19),esk3_1(X19)),u1_pre_topc(X19))|(~r2_hidden(k5_setfam_1(u1_struct_0(X19),esk1_1(X19)),u1_pre_topc(X19))|~r2_hidden(u1_struct_0(X19),u1_pre_topc(X19)))|v2_pre_topc(X19)|~l1_pre_topc(X19)))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_pre_topc])])])])])).
% 0.20/0.40  fof(c_0_31, negated_conjecture, (((~v2_struct_0(esk4_0)&v2_pre_topc(esk4_0))&l1_pre_topc(esk4_0))&k4_yellow_0(k2_yellow_1(u1_pre_topc(esk4_0)))!=u1_struct_0(esk4_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_23])])])])).
% 0.20/0.40  fof(c_0_32, plain, ![X27]:(v1_xboole_0(X27)|(~r2_hidden(k3_tarski(X27),X27)|k4_yellow_0(k2_yellow_1(X27))=k3_tarski(X27))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t14_yellow_1])])])).
% 0.20/0.40  cnf(c_0_33, plain, (~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.40  cnf(c_0_34, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.20/0.40  cnf(c_0_35, plain, (k5_setfam_1(u1_struct_0(X1),u1_pre_topc(X1))=k3_tarski(u1_pre_topc(X1))|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.20/0.40  cnf(c_0_36, plain, (k5_setfam_1(u1_struct_0(X1),u1_pre_topc(X1))=u1_struct_0(X1)|~l1_pre_topc(X1)|~r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))), inference(spm,[status(thm)],[c_0_29, c_0_28])).
% 0.20/0.40  cnf(c_0_37, plain, (r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.40  cnf(c_0_38, negated_conjecture, (v2_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.20/0.40  cnf(c_0_39, negated_conjecture, (l1_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.20/0.40  cnf(c_0_40, plain, (v1_xboole_0(X1)|k4_yellow_0(k2_yellow_1(X1))=k3_tarski(X1)|~r2_hidden(k3_tarski(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.40  cnf(c_0_41, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.20/0.40  cnf(c_0_42, plain, (k3_tarski(u1_pre_topc(X1))=u1_struct_0(X1)|~l1_pre_topc(X1)|~r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.20/0.40  cnf(c_0_43, negated_conjecture, (r2_hidden(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_39])])).
% 0.20/0.40  cnf(c_0_44, plain, (k4_yellow_0(k2_yellow_1(X1))=k3_tarski(X1)|~r2_hidden(k3_tarski(X1),X1)), inference(csr,[status(thm)],[c_0_40, c_0_41])).
% 0.20/0.40  cnf(c_0_45, negated_conjecture, (k3_tarski(u1_pre_topc(esk4_0))=u1_struct_0(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_39])])).
% 0.20/0.40  cnf(c_0_46, negated_conjecture, (k4_yellow_0(k2_yellow_1(u1_pre_topc(esk4_0)))!=u1_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.20/0.40  cnf(c_0_47, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_43])]), c_0_46]), ['proof']).
% 0.20/0.40  # SZS output end CNFRefutation
% 0.20/0.40  # Proof object total steps             : 48
% 0.20/0.40  # Proof object clause steps            : 25
% 0.20/0.40  # Proof object formula steps           : 23
% 0.20/0.40  # Proof object conjectures             : 9
% 0.20/0.40  # Proof object clause conjectures      : 6
% 0.20/0.40  # Proof object formula conjectures     : 3
% 0.20/0.40  # Proof object initial clauses used    : 13
% 0.20/0.40  # Proof object initial formulas used   : 11
% 0.20/0.40  # Proof object generating inferences   : 10
% 0.20/0.40  # Proof object simplifying inferences  : 9
% 0.20/0.40  # Training examples: 0 positive, 0 negative
% 0.20/0.40  # Parsed axioms                        : 11
% 0.20/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.40  # Initial clauses                      : 36
% 0.20/0.40  # Removed in clause preprocessing      : 0
% 0.20/0.40  # Initial clauses in saturation        : 36
% 0.20/0.40  # Processed clauses                    : 117
% 0.20/0.40  # ...of these trivial                  : 0
% 0.20/0.40  # ...subsumed                          : 12
% 0.20/0.40  # ...remaining for further processing  : 105
% 0.20/0.40  # Other redundant clauses eliminated   : 2
% 0.20/0.40  # Clauses deleted for lack of memory   : 0
% 0.20/0.40  # Backward-subsumed                    : 1
% 0.20/0.40  # Backward-rewritten                   : 0
% 0.20/0.40  # Generated clauses                    : 112
% 0.20/0.40  # ...of the previous two non-trivial   : 80
% 0.20/0.40  # Contextual simplify-reflections      : 1
% 0.20/0.40  # Paramodulations                      : 110
% 0.20/0.40  # Factorizations                       : 0
% 0.20/0.40  # Equation resolutions                 : 2
% 0.20/0.40  # Propositional unsat checks           : 0
% 0.20/0.40  #    Propositional check models        : 0
% 0.20/0.40  #    Propositional check unsatisfiable : 0
% 0.20/0.40  #    Propositional clauses             : 0
% 0.20/0.40  #    Propositional clauses after purity: 0
% 0.20/0.40  #    Propositional unsat core size     : 0
% 0.20/0.40  #    Propositional preprocessing time  : 0.000
% 0.20/0.40  #    Propositional encoding time       : 0.000
% 0.20/0.40  #    Propositional solver time         : 0.000
% 0.20/0.40  #    Success case prop preproc time    : 0.000
% 0.20/0.40  #    Success case prop encoding time   : 0.000
% 0.20/0.40  #    Success case prop solver time     : 0.000
% 0.20/0.40  # Current number of processed clauses  : 67
% 0.20/0.40  #    Positive orientable unit clauses  : 8
% 0.20/0.40  #    Positive unorientable unit clauses: 1
% 0.20/0.40  #    Negative unit clauses             : 3
% 0.20/0.40  #    Non-unit-clauses                  : 55
% 0.20/0.40  # Current number of unprocessed clauses: 26
% 0.20/0.40  # ...number of literals in the above   : 72
% 0.20/0.40  # Current number of archived formulas  : 0
% 0.20/0.40  # Current number of archived clauses   : 36
% 0.20/0.40  # Clause-clause subsumption calls (NU) : 1032
% 0.20/0.40  # Rec. Clause-clause subsumption calls : 142
% 0.20/0.40  # Non-unit clause-clause subsumptions  : 14
% 0.20/0.40  # Unit Clause-clause subsumption calls : 19
% 0.20/0.40  # Rewrite failures with RHS unbound    : 0
% 0.20/0.40  # BW rewrite match attempts            : 1
% 0.20/0.40  # BW rewrite match successes           : 0
% 0.20/0.40  # Condensation attempts                : 0
% 0.20/0.40  # Condensation successes               : 0
% 0.20/0.40  # Termbank termtop insertions          : 5277
% 0.20/0.40  
% 0.20/0.40  # -------------------------------------------------
% 0.20/0.40  # User time                : 0.051 s
% 0.20/0.40  # System time              : 0.008 s
% 0.20/0.40  # Total time               : 0.059 s
% 0.20/0.40  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
